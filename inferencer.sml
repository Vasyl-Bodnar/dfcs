(* This Source Code Form is subject to the terms of the Mozilla Public
   License, v. 2.0. If a copy of the MPL was not distributed with this
   file, You can obtain one at http://mozilla.org/MPL/2.0/. *)
structure Inferencer = struct
structure P = Parser
datatype con = datatype P.con
type longid = P.longid

datatype typ_pat = TyPatWildcard of inf_typ
                 | TyPatCon of con * inf_typ
                 | TyPatId of longid * inf_typ
                 | TyPatConstr of longid * typ_pat * inf_typ
                 | TyPatInfixConstr of typ_pat * string * typ_pat * inf_typ
                 | TyPatLayered of string * typ_pat * inf_typ
                 | TyPatRecord of rec_entry_typ_pat list * inf_typ
                 | TyPatList of typ_pat list * inf_typ
     and rec_entry_typ_pat = TyPatRecordEntryA of string * typ_pat * inf_typ
                           | TyPatRecordEntryB of string * typ_pat option * inf_typ
     and inf_typ = InfTypUnbound of string * inf_typ option ref
                 | InfTypConstr of inf_typ list * longid
                 | InfTypFun of inf_typ * inf_typ
                 | InfTypRecord of (string * inf_typ) list
                 | InfTypPoly of string list * inf_typ
                 | InfTypNever (* Does not return i.e. exceptions / Type that does not matter at all *)
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
     and typ_decl_fun = TyDeclFunNonfix of (string * typ_pat list * inf_typ * typ_exp) list
                      | TyDeclFunInfixOne of (typ_pat * string * typ_pat * inf_typ * typ_exp) list
                      | TyDeclFunInfixMany of (typ_pat * string * typ_pat * typ_pat list * inf_typ * typ_exp) list
     and typ_decl_exc = TyDeclExcGen of string * inf_typ option
                      | TyDeclExcRen of string * longid
     and typ_exp = TyExpCon of con * inf_typ
                 | TyExpValId of longid * inf_typ
                 | TyExpApp of typ_exp list * inf_typ
                 | TyExpInfixApp of typ_exp * string * typ_exp * inf_typ
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

type ctx = {env: (string * string list * inf_typ) list} (* TODO: Aliases *)

exception InferenceUnionErr of string * inf_typ * inf_typ
exception InferenceErr of string

val globalCount = ref 0
fun gensym () =
    let val ret = !globalCount in
        globalCount := !globalCount + 1;
        Int.toString ret
    end

fun makeInfTyp (P.TypVar str) = InfTypUnbound (str, ref NONE)
  | makeInfTyp (P.TypConstr (vars, lid)) = InfTypConstr (List.map makeInfTyp vars, lid)
  | makeInfTyp (P.TypFun (tyl, tyr)) = InfTypFun (makeInfTyp tyl, makeInfTyp tyr)
  | makeInfTyp (P.TypRecord rows) = InfTypRecord (List.map (fn (s, ty) => (s, makeInfTyp ty)) rows)

fun makeFun [] = raise InferenceErr "Cannot turn zero types into a function type"
  | makeFun (ty::typs) = List.foldl InfTypFun ty typs

fun getFunRight (InfTypFun (_, r)) = r
  | getFunRight _ = raise InferenceErr "Cannot get result as this is not a function"

fun getPatTyp (TyPatWildcard ty) = ty
  | getPatTyp (TyPatCon (_, ty)) = ty
  | getPatTyp (TyPatId (_, ty)) = ty
  | getPatTyp (TyPatConstr (_, _, ty)) = ty
  | getPatTyp (TyPatInfixConstr (_, _, _, ty)) = ty
  | getPatTyp (TyPatLayered (_, _, ty)) = ty
  | getPatTyp (TyPatRecord (_, ty)) = ty
  | getPatTyp (TyPatList (_, ty)) = ty

fun getPatIdsTyps (TyPatWildcard _) = []
  | getPatIdsTyps (TyPatCon _) = []
  | getPatIdsTyps (TyPatId (lid, ty)) = [(String.concatWith "." lid, ty)]
  | getPatIdsTyps (TyPatConstr (_, pat, _)) = getPatIdsTyps pat
  | getPatIdsTyps (TyPatInfixConstr (patl, opr, patr, ty)) = getPatIdsTyps patl @ getPatIdsTyps patr
  | getPatIdsTyps (TyPatLayered (id, pat, ty)) = (id, ty)::(getPatIdsTyps pat)
  | getPatIdsTyps (TyPatRecord (rows, _)) =
    List.concat
        (List.map (fn TyPatRecordEntryA (lab, pat, ty) =>
                      (getPatIdsTyps pat @ [(lab, ty)])
                  | TyPatRecordEntryB (id, SOME pat, ty) =>
                    (getPatIdsTyps pat @ [(id, ty)])
                  | TyPatRecordEntryB (id, NONE, ty) =>
                    [(id, ty)]) rows)
  | getPatIdsTyps (TyPatList (pats, _)) = List.concat (List.map getPatIdsTyps pats)

fun getExpTyp (TyExpCon (_, ty)) = ty
  | getExpTyp (TyExpValId (_, ty)) = ty
  | getExpTyp (TyExpApp (_, ty)) = ty
  | getExpTyp (TyExpInfixApp (_, _, _, ty)) = ty
  | getExpTyp (TyExpRecord (_, ty)) = ty
  | getExpTyp (TyExpRecordSelect (_, ty as InfTypFun _)) = ty
  | getExpTyp (TyExpRecordSelect (s, _)) = raise InferenceErr ("Illegal Record Select: #" ^ s)
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

fun getFunTyp (InfTypFun (_, ty)) = getFunTyp ty
  | getFunTyp ty = ty

fun occurs' (InfTypUnbound (namel, _)) (InfTypUnbound (namer, _)) = namel = namer
  | occurs' (tyx as (InfTypUnbound _)) (InfTypFun (app, rest)) = occurs' tyx app orelse occurs' tyx rest
  | occurs' (tyx as (InfTypUnbound _)) (InfTypRecord rows) = List.exists (fn (_, tyy) => occurs' tyx tyy) rows
  | occurs' tyx (tyy as (InfTypUnbound _)) = occurs' tyy tyx
  | occurs' _ _ = false

fun occurs (InfTypUnbound (namel, _)) (InfTypUnbound (namer, _)) = false
  | occurs (tyx as (InfTypUnbound _)) (InfTypFun (app, rest)) = occurs' tyx app orelse occurs' tyx rest
  | occurs (tyx as (InfTypUnbound _)) (InfTypRecord rows) = List.exists (fn (_, tyy) => occurs' tyx tyy) rows
  | occurs tyx (tyy as (InfTypUnbound _)) = occurs tyy tyx
  | occurs _ _ = false

fun find (InfTypUnbound (name, rf)) =
    (case !rf of
         SOME (ty as InfTypUnbound _) =>
         let val res = find ty
         in rf := SOME res; res
         end
       | SOME ty => ty
       | NONE => InfTypUnbound (name, rf))
  | find ty = ty

(* TODO: Instantiate future polymorphic types too *)
fun union tyx tyy =
    let val tyx = find tyx
        val tyy = find tyy
    in case (tyx, tyy) of
           (tyx, InfTypNever) => Ok ()
         | (InfTypNever, tyy) => Ok ()
         | (InfTypUnbound (name, rf), tyy) =>
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

fun inferPat (P.PatWildcard, _) = TyPatWildcard (InfTypUnbound (gensym (), ref NONE))
  | inferPat (P.PatCon (P.ConInt x), _) = TyPatCon (ConInt x, InfTypConstr ([], ["int"]))
  | inferPat (P.PatCon (P.ConString x), _) = TyPatCon (ConString x, InfTypConstr ([], ["string"]))
  | inferPat (P.PatCon (P.ConChar x), _) = TyPatCon (ConChar x, InfTypConstr ([], ["char"]))
  | inferPat (P.PatCon (P.ConWord x), _) = TyPatCon (ConWord x, InfTypConstr ([], ["word"]))
  | inferPat (P.PatCon (P.ConReal x), _) = TyPatCon (ConReal x, InfTypConstr ([], ["real"]))
  | inferPat (P.PatId (b, lid), {env}) =
    (case List.find (fn (n, _, _) => n = (String.concatWith "." lid)) env of
         SOME (_, [], ty) => TyPatId (lid, ty)
       | SOME (_, vars, ty) => TyPatId (lid, InfTypPoly (vars, ty))
       | NONE => TyPatId (lid, InfTypUnbound (gensym (), ref NONE)))
  | inferPat (P.PatApp [], ctx as {env}) = raise InferenceErr "Empty Application is impossible"
  | inferPat (P.PatApp pats, ctx as {env}) =
    let val pats = List.rev pats
        val pat = inferPat (List.hd pats, ctx)
        val pats = List.tl pats
    in
        #1 (List.foldl (fn (P.PatId (b, lid), (accp, accty)) =>
                           (case List.find (fn (n, _, _) => n = (String.concatWith "." lid)) env of
                                SOME (_, vars, ty) =>
                                (case union (makeFun [getFunRight ty, accty]) ty of
                                     Ok () => (TyPatConstr (lid, accp, getFunRight ty), getFunRight ty)
                                   | Err err => raise InferenceUnionErr err)
                              | NONE => raise InferenceErr ("Expected an existing id in pattern constructor: " ^ (String.concatWith "." lid)))
                       | _ => raise InferenceErr "Expected an id in pattern constructor")
                       (pat, getPatTyp pat)
                       pats)
    end
  | inferPat (P.PatInfixApp (patl, opr, patr), ctx as {env}) =
    let val patl = inferPat (patl, ctx)
        val patr = inferPat (patr, ctx)
    in case List.find (fn (n, _, _) => n = opr) env of
           SOME (_, vars, ty) =>
           (case union (makeFun [getFunRight ty, getPatTyp patr, getPatTyp patl]) ty of
                Ok () => TyPatInfixConstr (patl, opr, patr, getFunRight ty)
              | Err err => raise InferenceUnionErr err)
         | NONE => raise InferenceErr ("Expected an existing id in infix pattern constructor: " ^ opr)
    end
  | inferPat (P.PatLayered (b, id, SOME typ, pat), ctx) =
    let val ty = makeInfTyp typ
        val pat = inferPat (pat, ctx)
        val patty = getPatTyp pat
    in case union ty patty of
           Ok () => TyPatLayered (id, pat, ty)
         | Err err => raise InferenceUnionErr err
    end
  | inferPat (P.PatLayered (b, id, NONE, pat), ctx) =
    let val ty = InfTypUnbound (gensym (), ref NONE)
        val pat = inferPat (pat, ctx)
        val patty = getPatTyp pat
    in case union ty patty of
           Ok () => TyPatLayered (id, pat, ty)
         | Err err => raise InferenceUnionErr err
    end
  | inferPat (P.PatRecord entries, ctx) =
    let val entries =
            List.map (fn P.PatRecordEntryA (lab, pat) =>
                         let val pat = inferPat (pat, ctx)
                         in TyPatRecordEntryA (lab, pat, getPatTyp pat)
                         end
                     | P.PatRecordEntryB (id, SOME typ, SOME pat) =>
                       let val ty = makeInfTyp typ
                           val pat = inferPat (pat, ctx)
                       in case union ty (getPatTyp pat) of
                              Ok () => TyPatRecordEntryB (id, SOME pat, ty)
                            | Err err => raise InferenceUnionErr err
                       end
                     | P.PatRecordEntryB (id, SOME typ, NONE) =>
                       TyPatRecordEntryB (id, NONE, makeInfTyp typ)
                     | P.PatRecordEntryB (id, NONE, SOME pat) =>
                       let val ty = InfTypUnbound (gensym (), ref NONE)
                           val pat = inferPat (pat, ctx)
                       in case union ty (getPatTyp pat) of
                              Ok () => TyPatRecordEntryB (id, SOME pat, ty)
                            | Err err => raise InferenceUnionErr err
                       end
                     | P.PatRecordEntryB (id, NONE, NONE) =>
                       TyPatRecordEntryB (id, NONE, InfTypUnbound (gensym (), ref NONE)))
                     entries
        val typs = List.map (fn TyPatRecordEntryA (lab, _, ty) => (lab, ty)
                            | TyPatRecordEntryB (id, _, ty) => (id, ty))
                            entries
    in
        TyPatRecord (entries, InfTypRecord typs)
    end
  | inferPat (P.PatList pats, ctx) =
    let val ty = InfTypUnbound (gensym (), ref NONE)
        val pats = List.map (fn pat => inferPat (pat, ctx)) pats
    in case Result.seq (Ok ()) (List.map (fn pat => union ty (getPatTyp pat)) pats) of
           Ok () => TyPatList (pats, InfTypConstr ([ty], ["list"]))
         | Err err => raise InferenceUnionErr err
    end
  | inferPat (P.PatTypeAnnote (pat, typ), ctx) =
    let val pat = inferPat (pat, ctx)
        val ty = getPatTyp pat
    in case union ty (makeInfTyp typ) of
           Ok () => pat
         | Err err => raise InferenceUnionErr err
    end

and inferMatches (matches : (P.pat * P.exp) list, ctx) : (typ_pat * typ_exp) list * inf_typ =
    let val pat_ty = InfTypUnbound (gensym (), ref NONE)
        val exp_ty = InfTypUnbound (gensym (), ref NONE)
        val matches = List.map (fn (pa, ex) =>
                                   (inferPat (pa, ctx),
                                    inferExp (ex, ctx))) matches
        val res = Result.seq (Ok ())
                             (List.map (fn (pa, ex) =>
                                           let val pa_ty = getPatTyp pa
                                               val ex_ty = getExpTyp ex
                                           in Result.seq (Ok ()) [union pat_ty pa_ty,
                                                                  union exp_ty ex_ty]
                                           end) matches)
    in case res of
           Ok () => ()
         | Err err => raise InferenceUnionErr err;
       (matches, exp_ty)
    end

and inferExp (P.ExpCon (P.ConInt x), _) = TyExpCon (ConInt x, InfTypConstr ([], ["int"]))
  | inferExp (P.ExpCon (P.ConString x), _) = TyExpCon (ConString x, InfTypConstr ([], ["string"]))
  | inferExp (P.ExpCon (P.ConChar x), _) = TyExpCon (ConChar x, InfTypConstr ([], ["char"]))
  | inferExp (P.ExpCon (P.ConWord x), _) = TyExpCon (ConWord x, InfTypConstr ([], ["word"]))
  | inferExp (P.ExpCon (P.ConReal x), _) = TyExpCon (ConReal x, InfTypConstr ([], ["real"]))
  | inferExp (P.ExpValId (b, lid), {env}) =
    (case List.find (fn (n, _, _) => n = (String.concatWith "." lid)) env of
         SOME (_, [], ty) => TyExpValId (lid, ty)
       | SOME (_, vars, ty) => TyExpValId (lid, InfTypPoly (vars, ty))
       | NONE => raise InferenceErr ("Expected an existing variable for expression id: " ^ (String.concatWith "." lid)))
  | inferExp (P.ExpApp exps, ctx as {env}) =
    let val ty = InfTypUnbound (gensym (), ref NONE)
        val exps = List.rev (List.map (fn ex => inferExp (ex, ctx)) exps)
    in case exps of
           [TyExpRecordSelect (s, _), record as TyExpRecord (rows, rty)] =>
           (case List.find (fn (n, _) => s = n) rows of
                SOME (_, exp) => TyExpApp ([TyExpRecordSelect (s, InfTypFun (rty, getExpTyp exp)), record], getExpTyp exp)
              | NONE => raise InferenceErr "Record Select on a wrong record")
         | (TyExpRecordSelect _)::_ => raise InferenceErr "Illegal Record Select without a record"
         | f::exps =>
           let val fty = getExpTyp f
               val appty = List.foldr (fn (ex, acc) => InfTypFun (getExpTyp ex, acc)) ty exps
           in case union fty appty of
                  Ok () => TyExpApp (f::exps, ty)
                | Err err => raise InferenceUnionErr err
           end
         | [] => raise InferenceErr "Empty Application is impossible"
    end
  | inferExp (P.ExpInfixApp (expl, opr, expr), ctx as {env}) =
    let val ty = InfTypUnbound (gensym (), ref NONE)
        val expl = inferExp (expl, ctx)
        val expr = inferExp (expr, ctx)
    in case List.find (fn (n, _, _) => n = opr) env of
           SOME (_, vars, fty) => (* TODO: Instantiate future polymorphic types too *)
           let val tyl = getExpTyp expl
               val tyr = getExpTyp expr
           in case (union fty (InfTypFun (tyl, InfTypFun (tyr, ty)))) of
                  Ok () => TyExpInfixApp (expl, opr, expr, ty)
                | Err err => raise InferenceUnionErr err
           end
         | NONE => raise InferenceErr "Expected an existing variable for infix expression"
    end
  | inferExp (P.ExpRecord rows, ctx) =
    let val rows = List.map (fn (n, ex) => (n, inferExp (ex, ctx))) rows
        val rowtys = List.map (fn (n, ex) => (n, getExpTyp ex)) rows
    in
        TyExpRecord (rows, InfTypRecord rowtys)
    end
  | inferExp (P.ExpRecordSelect s, ctx) = TyExpRecordSelect (s, InfTypNever)
  | inferExp (P.ExpList exps, ctx) =
    let val ty = InfTypUnbound (gensym (), ref NONE)
        val exps = List.map (fn ex => inferExp (ex, ctx)) exps
    in case Result.seq (Ok ()) (List.map (fn ex => union ty (getExpTyp ex)) exps) of
           Ok () => TyExpList (exps, InfTypConstr ([ty], ["list"]))
         | Err err => raise InferenceUnionErr err
    end
  | inferExp (P.ExpSeq exps, ctx) =
    let val exps = List.map (fn ex => inferExp (ex, ctx)) exps
        val ty = getExpTyp (List.last exps)
    in
        TyExpSeq (exps, ty)
    end
  | inferExp (P.ExpLocalDecl (decl, exps), ctx) =
    let val (decl, ctx) = inferDecl (decl, ctx)
        val exps = List.map (fn ex => inferExp (ex, ctx)) exps
        val ty = getExpTyp (List.last exps)
    in
        TyExpLocalDecl (decl, exps, ty)
    end
  | inferExp (P.ExpConj (expl, expr), ctx) = TyExpConj (inferExp (expl, ctx), inferExp (expr, ctx), InfTypConstr ([], ["bool"]))
  | inferExp (P.ExpDisj (expl, expr), ctx) = TyExpDisj (inferExp (expl, ctx), inferExp (expr, ctx), InfTypConstr ([], ["bool"]))
  | inferExp (P.ExpExceptionRaise exp, ctx) = TyExpExceptionRaise (inferExp (exp, ctx), InfTypNever)
  | inferExp (P.ExpExceptionHandle (exp, matches), ctx) = TyExpExceptionHandle (inferExp (exp, ctx), #1 (inferMatches (matches, ctx)), InfTypNever)
  | inferExp (P.ExpCond (cond, expl, expr), ctx) =
    let val cond = inferExp (cond, ctx)
        val expl = inferExp (expl, ctx)
        val expr = inferExp (expr, ctx)
        val ty = InfTypUnbound (gensym (), ref NONE)
    in case Result.seq (Ok ()) (List.map (fn (a, b) => union a b)
                                         [(getExpTyp cond, InfTypConstr ([], ["bool"])),
                                          (getExpTyp expl, ty),
                                          (getExpTyp expr, ty)])
        of
           Ok () => TyExpCond (cond, expl, expr, ty)
         | Err err => raise InferenceUnionErr err
    end
  | inferExp (P.ExpIter (cond, exp), ctx) = TyExpIter (inferExp (cond, ctx), inferExp (exp, ctx), InfTypRecord [])
  | inferExp (P.ExpMatch (exp, matches), ctx) =
    let val (matches, ty) = inferMatches (matches, ctx)
    in
        TyExpMatch (inferExp (exp, ctx), matches, ty)
    end
  | inferExp (P.ExpFn matches, ctx) = TyExpFn (inferMatches (matches, ctx))
  | inferExp (P.ExpTypeAnnote (exp, typ), ctx) =
    let val exp = inferExp (exp, ctx)
        val ty = getExpTyp exp
    in case union ty (makeInfTyp typ) of
           Ok () => exp
         | Err err => raise InferenceUnionErr err
    end

and inferFunDecl (P.DeclFunNonfix [], _) = raise InferenceErr "Empty nonfix functions should be impossible"
  | inferFunDecl (P.DeclFunNonfix ((opr, id, pats, typ, exp)::fs), ctx as {env}) =
    let val fty = InfTypUnbound (gensym (), ref NONE)
        val (f, fid, fsig) =
            let val typ = case typ of SOME typ => makeInfTyp typ
                                    | NONE => InfTypNever
                val pats = List.map (fn pat => inferPat (pat, ctx)) pats
                val patidstys = List.map (fn (n, ty) => (n, [], ty))
                                         (List.concat (List.map getPatIdsTyps pats))
                val pattys = List.map getPatTyp pats
                val fsig = makeFun (fty::pattys)
                val env = patidstys @ (id, [], fsig)::env
                val exp = inferExp (exp, {env=env})
            in (case Result.seq (Ok ())
                                (List.map (fn (tl, tr) => union tl tr)
                                          [(fty, typ), (fty, getExpTyp exp)]) of
                    Ok () => ((id, pats, fty, exp),
                              id,
                              fsig)
                  | Err err => raise InferenceUnionErr err)
            end
        val fs = List.map (fn (opr, id, pats, typ, exp) =>
                              let val typ = case typ of SOME typ => makeInfTyp typ
                                                      | NONE => InfTypNever
                                  val pats = List.map (fn pat => inferPat (pat, ctx)) pats
                                  val patidstys = List.map (fn (n, ty) => (n, [], ty))
                                                           (List.concat (List.map getPatIdsTyps pats))
                                  val pattys = List.map getPatTyp pats
                                  val fsigr = makeFun (fty::pattys)
                                  val env = patidstys @ (id, [], fsigr)::env
                                  val exp = inferExp (exp, {env=env})
                              in (case Result.seq (if fid = id
                                                   then Ok ()
                                                   else Err ("Function names should match in guards", fsig, fsigr))
                                                  (List.map (fn (tl, tr) => union tl tr)
                                                            [(fty, typ), (fty, getExpTyp exp), (fsig, fsigr)]) of
                                      Ok () => ((id, pats, fty, exp))
                                    | Err err => raise InferenceUnionErr err)
                              end) fs
    in
        (TyDeclFunNonfix (f::fs), (fid, fsig))
    end
  | inferFunDecl (P.DeclFunInfixOne fs, ctx as {env}) = raise InferenceErr "Unhandled function kind InfixOne"
  | inferFunDecl (P.DeclFunInfixMany fs, ctx as {env}) = raise InferenceErr "Unhandled function kind InfixMany"

and inferDecl (P.DeclVal (vars, vals), ctx) =
    let val (vals, ctx) = List.foldl (fn ((b, pat, exp), (acc, ctx as {env})) =>
                                         let val pat = inferPat (pat, ctx)
                                             val exp = inferExp (exp, ctx)
                                             val patidstys = List.map (fn (n, ty) => (n, [], ty)) (getPatIdsTyps pat)
                                             val ctx = {env=patidstys@env}
                                         in case union (getPatTyp pat) (getExpTyp exp) of
                                                Ok () => ((b, pat, exp)::acc, ctx)
                                              | Err err => raise InferenceUnionErr err
                                         end) ([], ctx) vals
    in
        (TyDeclVal (vars, List.rev vals), ctx)
    end
  | inferDecl (P.DeclFun (vars, funs), ctx as {env}) =
    let val (funs, fsigs) = ListPair.unzip (List.map (fn f => inferFunDecl (f, ctx)) funs)
        val ctx = {env=(List.map (fn (fid, fsig) => (fid, [], fsig)) fsigs) @ env}
    in
        (TyDeclFun (vars, funs), ctx)
    end
  | inferDecl (P.DeclTyp typs, ctx) = (* TODO: Handle aliases properly *)
    (TyDeclTyp (List.map (fn (vars, id, ty) => (vars, id, makeInfTyp ty)) typs), ctx)
  | inferDecl (P.DeclDataTyp (data, typs), ctx as {env}) =
    let val data = List.map (fn (vars, id, cons) =>
                                (vars, id, List.map (fn (id, SOME ty) => (id, SOME (makeInfTyp ty))
                                                    | (id, NONE) => (id, NONE)) cons)) data
        val typs = List.map (fn (vars, id, ty) => (vars, id, makeInfTyp ty)) typs
        val ctx = {env=(List.concat (List.map (fn (vars, id, cons) => List.map (fn (cid, SOME ty) => (cid, vars, makeFun [InfTypConstr ([], [id]), ty])
                                                                               | (cid, NONE) => (cid, vars, InfTypConstr ([], [id]))) cons) data))@env}
    in
        (TyDeclDataTyp (data, typs), ctx)
    end
  | inferDecl (P.DeclDataTypRepl (id, lid), ctx) = (TyDeclDataTypRepl (id, lid), ctx)
  | inferDecl (P.DeclAbsTyp (data, typs, decl), ctx as {env}) =
    let val data = List.map (fn (vars, id, cons) =>
                                (vars, id, List.map (fn (id, SOME ty) => (id, SOME (makeInfTyp ty))
                                                    | (id, NONE) => (id, NONE)) cons)) data
        val typs = List.map (fn (vars, id, ty) => (vars, id, makeInfTyp ty)) typs
        val ctx = {env=(List.concat (List.map (fn (vars, id, cons) => List.map (fn (cid, SOME ty) => (cid, vars, makeFun [InfTypConstr ([], [id]), ty])
                                                                               | (cid, NONE) => (cid, vars, InfTypConstr ([], [id]))) cons) data))@env}
        val (decl, _) = inferDecl (decl, ctx)
    in
        (TyDeclAbsTyp (data, typs, decl), ctx)
    end
  | inferDecl (P.DeclExc excs, ctx) =
    (TyDeclExc (List.map (fn P.DeclExcGen (id, SOME ty) => TyDeclExcGen (id, SOME (makeInfTyp ty))
                         | P.DeclExcGen (id, NONE) => TyDeclExcGen (id, NONE)
                         | P.DeclExcRen (id, lid) => TyDeclExcRen (id, lid)) excs),
     ctx)
  | inferDecl (P.DeclSeq decls, ctx) =
    let val (decls, ctx) =
            List.foldl (fn (decl, (acc, ctx)) =>
                           let val (decl, ctx) = inferDecl (decl, ctx)
                           in (decl::acc, ctx)
                           end) ([], ctx) decls
    in
        (TyDeclSeq (List.rev decls), ctx)
    end
  | inferDecl (P.DeclLocal (decl, decr), ctx) =
    let val (decl, ctxl) = inferDecl (decl, ctx)
        val (decr, _) = inferDecl (decr, ctxl)
    in
        (TyDeclLocal (decl, decr), ctx)
    end
  | inferDecl (P.DeclOpen lids, ctx) = (TyDeclOpen lids, ctx)
  | inferDecl (P.DeclNonfix ids, ctx) = (TyDeclNonfix ids, ctx)
  | inferDecl (P.DeclInfix (dig, ids), ctx) = (TyDeclInfix (dig, ids), ctx)
  | inferDecl (P.DeclInfixR (dig, ids), ctx) =  (TyDeclInfixR (dig, ids), ctx)
  (* | inferDecl (TyDeclStruct _, ctx) = TODO: MODULES *)
  | inferDecl (P.DeclEmpty, ctx) = (TyDeclEmpty, ctx)

fun infer ast =
    let val env = [("+", [], makeFun [InfTypConstr ([], ["int"]), InfTypConstr ([], ["int"]), InfTypConstr ([], ["int"])])]
    in
        inferDecl (ast, {env=env})
    end
end
