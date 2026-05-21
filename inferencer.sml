structure Inferencer = struct
  structure P = Parser
  datatype con = datatype P.con
  type longid = P.longid

  datatype ctx = Ctx of {fenv: (string list * inf_typ) HashArray.hash list, env: inf_typ HashArray.hash list}
  and typ_pat = PatWildcard
          | TyPatCon of con * inf_typ
          | TyPatConstr of bool * longid * typ_pat option * inf_typ
          | TyPatInfixApp of typ_pat * (string *typ_pat) list * inf_typ
          | TyPatTuple of typ_pat list * typ_pat
          | TyPatLayered of bool * string * inf_typ * typ_pat
          | TyPatRecord of rec_entry_typ_pat list * typ_pat
          | TyPatList of typ_pat list * typ_pat
  and rec_entry_typ_pat = TyPatRecordEntryA of string * typ_pat * typ_pat
                        | TyPatRecordEntryB of string * typ_pat option * typ_pat
  and inf_typ = InfTypUnbound of string * inf_typ option ref
          | InfTypConstr of inf_typ list * longid
          | InfTypFun of inf_typ * inf_typ
          | InfTypTuple of inf_typ list
          | InfTypRecord of (string * inf_typ) list
  and typ_decl = TyDeclVal of string list * (bool * typ_pat * typ_exp) list
           | TyDeclFun of string list * typ_decl_fun list
           | TyDeclTyp of (string list * string * inf_typ) list
           | TyDeclDataTyp of ((string list * string * (string * inf_typ option) list) list) * ((string list * string * inf_typ) list)
           | TyDeclDataTypRepl of string * longid
           | TyDeclAbsTyp of ((string list * string * (string * inf_typ option) list) list) * ((string list * string * inf_typ) list) * typ_decl
           | TyDeclExc of typ_decl_exc list
           | TyDeclSeq of typ_decl list
           | TyDeclLocal of typ_decl * typ_decl
           | TyDeclOpen of longid list
           | TyDeclNonfix of string list
           | TyDeclInfix of int option * string list
           | TyDeclInfixR of int option * string list
           (* | TyDeclStruct of TODO: MODULES *)
           | TyDeclEmpty
  and typ_decl_fun = TyDeclFunNonfix of (bool * string * typ_pat list * inf_typ * typ_exp) list
               | TyDeclFunInfixOne of (typ_pat * string * typ_pat * inf_typ * typ_exp) list
               | TyDeclFunInfixMany of (typ_pat * string * typ_pat * typ_pat list * inf_typ * typ_exp) list
  and typ_decl_exc = TyDeclExcGen of string * inf_typ option
                   | TyDeclExcRen of string * longid
  and typ_exp = TyExpCon of con * inf_typ
          | TyExpValId of bool * longid * inf_typ
          | TyExpApp of typ_exp list * inf_typ
          | TyExpInfixApp of typ_exp * string * typ_exp * inf_typ
          | TyExpTuple of typ_exp list * inf_typ
          | TyExpRecord of (string * typ_exp) list * inf_typ
          | TyExpRecordSelect of string * inf_typ
          | TyExpList of typ_exp list * inf_typ
          | TyExpSeq of typ_exp list * inf_typ
          | TyExpLocalDecl of typ_decl * typ_exp list * inf_typ
          | TyExpConj of typ_exp * typ_exp * inf_typ
          | TyExpDisj of typ_exp * typ_exp * inf_typ
          | TyExpExceptionRaise of typ_exp * inf_typ
          | TyExpExceptionHandle of typ_exp * (typ_pat * typ_exp) list * inf_typ
          | TyExpCond of typ_exp * typ_exp * typ_exp * inf_typ
          | TyExpIter of typ_exp * typ_exp * inf_typ
          | TyExpMatch of typ_exp * (typ_pat * typ_exp) list * inf_typ
          | TyExpFn of (typ_pat * typ_exp) list * inf_typ

  exception InferenceUnionErr of string * inf_typ * inf_typ

  val globalCount = ref 0
  fun gensym () =
      let val ret = !globalCount in
          globalCount := !globalCount + 1;
          Int.toString ret
      end

  fun getExpTyp (TyExpCon (_, ty)) = ty
    | getExpTyp (TyExpValId (_, _, ty)) = ty
    | getExpTyp (TyExpApp (_, ty)) = ty
    | getExpTyp (TyExpInfixApp (_, _, _, ty)) = ty
    | getExpTyp (TyExpTuple (_, ty)) = ty
    | getExpTyp (TyExpRecord (_, ty)) = ty
    | getExpTyp (TyExpRecordSelect (_, ty)) = ty
    | getExpTyp (TyExpList (_, ty)) = ty
    | getExpTyp (TyExpSeq (_, ty)) = ty
    | getExpTyp (TyExpLocalDecl (_, _, ty)) = ty
    | getExpTyp (TyExpConj (_, _, ty)) = ty
    | getExpTyp (TyExpDisj (_, _, ty)) = ty
    | getExpTyp (TyExpExceptionRaise (_, ty)) = ty
    | getExpTyp (TyExpExceptionHandle (_, _, ty)) = ty
    | getExpTyp (TyExpCond (_, _, _, ty)) = ty
    | getExpTyp (TyExpIter (_, _, ty)) = ty
    | getExpTyp (TyExpMatch (_, _, ty)) = ty
    | getExpTyp (TyExpFn (_, ty)) = ty

  fun occurs' (InfTypUnbound (namel, _)) (InfTypUnbound (namer, _)) = namel = namer
    | occurs' (tyx as (InfTypUnbound _)) (InfTypFun (app, rest)) = occurs' tyx app orelse occurs' tyx rest
    | occurs' (tyx as (InfTypUnbound _)) (InfTypTuple typs) = List.exists (occurs' tyx) typs
    | occurs' (tyx as (InfTypUnbound _)) (InfTypRecord rows) = List.exists (fn (_, tyy) => occurs' tyx tyy) rows
    | occurs' tyx (tyy as (InfTypUnbound _)) = occurs' tyy tyx
    | occurs' _ _ = false

  fun occurs (InfTypUnbound (namel, _)) (InfTypUnbound (namer, _)) = false
    | occurs (tyx as (InfTypUnbound _)) (InfTypFun (app, rest)) = occurs' tyx app orelse occurs' tyx rest
    | occurs (tyx as (InfTypUnbound _)) (InfTypTuple typs) = List.exists (occurs' tyx) typs
    | occurs (tyx as (InfTypUnbound _)) (InfTypRecord rows) = List.exists (fn (_, tyy) => occurs' tyx tyy) rows
    | occurs tyx (tyy as (InfTypUnbound _)) = occurs tyy tyx
    | occurs _ _ = false

  fun find (InfTypUnbound (name, rf)) =
      (case !rf of
           SOME ty => ty
         | NONE => InfTypUnbound (name, rf))
    | find ty = ty

  (* TODO: Type constructors are a little bit trickier
           Path compression (just a separate case for Unbound basically) *)
  fun union tyx tyy =
      let val tyx = find tyx
          val tyy = find tyy
      in case (tyx, tyy) of
             (InfTypUnbound (name, rf), tyy) =>
             if occurs tyx tyy
             then Err ("No such recursive evil allowed", tyx, tyy)
             else (rf := SOME tyy; Ok ())
           | (tyx, InfTypUnbound (name, rf)) => union tyy tyx
           | (InfTypConstr (varsl, idsl), InfTypConstr (varsr, idsr)) =>
             if List.length varsl = List.length varsr andalso
                List.length idsl = List.length idsr   andalso
                Result.isOk (Result.seq (Ok ())
                                        (ListPair.map
                                             (fn (x,y) => union x y)
                                             (varsl, varsr))) andalso
                ListPair.all (op =) (idsl, idsr)
             then Ok ()
             else Err ("Different type constructors", tyx, tyy)
           | (InfTypFun (appl, restl), InfTypFun (appr, restr)) =>
             Result.seq (Ok ()) [union appl appr, union restl restr]
           | (InfTypTuple typsl, InfTypTuple typsr) =>
             if List.length typsl <> List.length typsr
             then Err ("Different lengths in tuple types", tyx, tyy)
             else Result.seq (Ok ()) (List.map (fn (x, y) => union x y)
                                               (ListPair.zip (typsl, typsr)))
           | (InfTypRecord rowsl, InfTypRecord rowsr) =>
             if List.length rowsl <> List.length rowsr
             then Err ("Different number of fields in record types", tyx, tyy)
             else Result.seq (Ok ()) (List.map (fn ((nx,tx), (ny,ty)) =>
                                                   if nx = ny
                                                   then union tx ty
                                                   else Err ("Record field names did not match", tyx, tyy))
                                               (ListPair.zip (rowsl, rowsr)))
           | _ => Err ("Unhandled union/Wrong type", tyx, tyy)
      end

  fun inferExp (P.ExpCon (P.ConInt x), _) = TyExpCon (ConInt x, InfTypConstr ([], ["int"]))
    | inferExp (P.ExpCon (P.ConString x), _) = TyExpCon (ConString x, InfTypConstr ([], ["string"]))
    | inferExp (P.ExpCon (P.ConChar x), _) = TyExpCon (ConChar x, InfTypConstr ([], ["char"]))
    | inferExp (P.ExpCon (P.ConWord x), _) = TyExpCon (ConWord x, InfTypConstr ([], ["word"]))
    | inferExp (P.ExpCon (P.ConReal x), _) = TyExpCon (ConReal x, InfTypConstr ([], ["real"]))
    | inferExp (P.ExpValId (b, lid), {env, fenv}) =
      (case HashArray.sub (env, String.concatWith "." lid) of
           SOME ty => TyExpValId (b, lid, ty)
         | NONE => TyExpValId (b, lid, InfTypUnbound (gensym (), ref NONE)))
    | inferExp (P.ExpList exps, ctx) =
      let val ty = InfTypUnbound (gensym (), ref NONE)
          val exps = List.map (fn ex => inferExp (ex, ctx)) exps
      in
          case Result.seq (Ok ()) (List.map (fn ex => union ty (getExpTyp ex)) exps) of
              Ok () => TyExpList (exps, InfTypConstr ([ty], ["list"]))
            | Err err => raise InferenceUnionErr err
      end
    | inferExp (exp, _) = (TyExpCon (ConInt 5, InfTypConstr ([], ["none"])))
end
