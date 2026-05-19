structure Inferencer = struct
  structure P = Parser

  datatype ctx = Ctx of {fenv: (string list * inf_typ) HashArray.hash list, env: inf_typ HashArray.hash list}
  and typ_pat = PatWildcard
          | TyPatCon of P.con * inf_typ
          | TyPatConstr of bool * P.longid * typ_pat option * inf_typ
          | TyPatInfixApp of typ_pat * (string *typ_pat) list * inf_typ
          | TyPatTuple of typ_pat list * typ_pat
          | TyPatLayered of bool * string * inf_typ * typ_pat
          | TyPatRecord of rec_entry_typ_pat list * typ_pat
          | TyPatList of typ_pat list * typ_pat
  and rec_entry_typ_pat = TyPatRecordEntryA of string * typ_pat * typ_pat
                        | TyPatRecordEntryB of string * typ_pat option * typ_pat
  and inf_typ = InfTypUnbound of string * inf_typ option ref
          | InfTypConstr of inf_typ list * P.longid
          | InfTypFun of inf_typ * inf_typ
          | InfTypTuple of inf_typ list
          | InfTypRecord of (string * inf_typ) list
  and typ_decl = TyDeclVal of string list * (bool * typ_pat * typ_exp) list
           | TyDeclFun of string list * typ_decl_fun list
           | TyDeclTyp of (string list * string * inf_typ) list
           | TyDeclDataTyp of ((string list * string * (string * inf_typ option) list) list) * ((string list * string * inf_typ) list)
           | TyDeclDataTypRepl of string * P.longid
           | TyDeclAbsTyp of ((string list * string * (string * inf_typ option) list) list) * ((string list * string * inf_typ) list) * typ_decl
           | TyDeclExc of typ_decl_exc list
           | TyDeclSeq of typ_decl list
           | TyDeclLocal of typ_decl * typ_decl
           | TyDeclOpen of P.longid list
           | TyDeclNonfix of string list
           | TyDeclInfix of int option * string list
           | TyDeclInfixR of int option * string list
           (* | TyDeclStruct of TODO: MODULES *)
           | TyDeclEmpty
  and typ_decl_fun = TyDeclFunNonfix of (bool * string * typ_pat list * inf_typ * typ_exp) list
               | TyDeclFunInfixOne of (typ_pat * string * typ_pat * inf_typ * typ_exp) list
               | TyDeclFunInfixMany of (typ_pat * string * typ_pat * typ_pat list * inf_typ * typ_exp) list
  and typ_decl_exc = TyDeclExcGen of string * inf_typ option
                   | TyDeclExcRen of string * P.longid
  and typ_exp = TyExpCon of P.con * inf_typ
          | TyExpValId of bool * P.longid * inf_typ
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

  val globalCount = ref 0
  val gensym =
      let val ret = !globalCount in
          globalCount := !globalCount + 1;
          Int.toString ret
      end

  (* TODO: This should work *)
  fun occurs tyx tyy = false

  fun find (InfTypUnbound (name, rf)) =
      (case !rf of
           SOME ty => ty
         | NONE => InfTypUnbound (name, rf))
    | find ty = ty

  (* TODO: Some types are not handled, such as more advanced type constructors *)
  fun union tyx tyy =
      let val tyx = find tyx
          val tyy = find tyy
      in
          if occurs tyx tyy
          then Err ("No such evil allowed", tyx, tyy)
          else case (tyx, tyy) of
                   (InfTypUnbound (name, rf), tyy) => (rf := SOME tyy; Ok ())
                 | (tyx, InfTypUnbound (name, rf)) => (rf := SOME tyx; Ok ())
                 | (InfTypConstr ([], [idl]), InfTypConstr ([], [idr])) =>
                   if idl = idr
                   then Ok ()
                   else Err ("Different type constructors", tyx, tyy)
                 | (InfTypFun (appl,restl), InfTypFun (appr,restr)) =>
                   Result.seq (Ok ()) [union appl appr, union restl restr]
                 | (InfTypTuple typsl, InfTypTuple typsr) =>
                   if List.length typsl <> List.length typsr
                   then Err ("Different lengths in tuple types", tyx, tyy)
                   else Result.seq (Ok ()) (List.map (fn (x, y) => union x y)
                                                     (ListPair.zip (typsl, typsr)))
                 | (InfTypRecord rowsl, InfTypRecord rowsr) =>
                   if List.length rowsl <> List.length rowsr
                   then Err ("Different lengths in tuple types", tyx, tyy)
                   else Result.seq (Ok ()) (List.map (fn ((nx,tx), (ny,ty)) =>
                                                         if nx = ny then union tx ty else Err ("Record field names did not match", tyx, tyy))
                                                     (ListPair.zip (rowsl, rowsr)))
                 | _ => Err ("Unhandled union/Wrong type", tyx, tyy)
      end
end
