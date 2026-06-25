(* This Source Code Form is subject to the terms of the Mozilla Public
   License, v. 2.0. If a copy of the MPL was not distributed with this
   file, You can obtain one at http://mozilla.org/MPL/2.0/. *)
(* Currently used for fixing infix operators *)
structure Elaborator = struct
structure P = Parser
exception IllegalElab of string
exception ImproperElabResultExp of P.exp list
exception ImproperElabResultPat of P.pat list

type ctx = {tinfix: (string * int option) list}

fun checkInfix id {tinfix, ...} = List.find (fn (i, SOME _) => id = i
                                                  | _ => false) tinfix
fun removeInfix id {tinfix} = {tinfix=(id, NONE)::tinfix}
fun addInfix fix id {tinfix} = {tinfix=(id, SOME fix)::tinfix}

fun shuntingYardCombineOpPat (p, id) pats ctx opst (v::u::valst) =
    if p >= 0
    then shuntingYardPat pats ctx opst ((P.PatInfixApp (u, id, v))::valst) false
    else shuntingYardPat pats ctx opst ((P.PatInfixApp (v, id, u))::valst) false
  | shuntingYardCombineOpPat (p, id) pats ctx opst ((P.PatApp (e::es))::valst) =
    if p >= 0
    then shuntingYardPat pats ctx opst ((P.PatInfixApp (P.PatApp es, id, e))::valst) false
    else shuntingYardPat pats ctx opst ((P.PatInfixApp (e, id, P.PatApp es))::valst) false
  | shuntingYardCombineOpPat (p, id) pats ctx opst _ = raise IllegalElab "Elaborator Error: Pattern infix operator has no operands."

and shuntingYardCombinePat pat pats ctx opst (allvalst as ((P.PatApp es)::valst)) b =
    if b
    then shuntingYardPat pats ctx opst ((P.PatApp (pat::es))::valst) true
    else shuntingYardPat pats ctx opst (pat::allvalst) true
  | shuntingYardCombinePat pat pats ctx opst (allvalst as (e::valst)) b =
    if b
    then shuntingYardPat pats ctx opst ((P.PatApp (pat::[e]))::valst) true
    else shuntingYardPat pats ctx opst (pat::allvalst) true
  | shuntingYardCombinePat pat pats ctx opst [] b = shuntingYardPat pats ctx opst [pat] true

and shuntingYardPat [] ctx [] [v] _ = v
  | shuntingYardPat [] ctx [] xs _ = raise ImproperElabResultPat xs
  | shuntingYardPat [] ctx ((p, id)::opst) valst _ = shuntingYardCombineOpPat (p, id) [] ctx opst valst
  | shuntingYardPat ((pat as P.PatId (false, [id])) :: pats) ctx opst valst b =
    (case checkInfix id ctx of
         SOME (_, SOME pow) => (case opst of
                          [] => shuntingYardPat pats ctx [(pow,id)] valst false
                        | ((p,i)::oprest) =>
                          case (p < 0, pow < 0) of
                              (true, true) => if pow <= p
                                              then shuntingYardPat pats ctx ((pow,id)::opst) valst false
                                              else shuntingYardCombineOpPat (p, i) pats ctx ((pow,id)::oprest) valst
                            | (false, false) => if pow >= p
                                                then shuntingYardPat pats ctx ((pow,id)::opst) valst false
                                                else shuntingYardCombineOpPat (p, i) pats ctx ((pow,id)::oprest) valst
                            | (true, false) => if pow = (~p - 1)
                                               then raise IllegalElab "Elaborator Error: Equal right and left associativity cannot be mixed together. E.g. a >> b << c or a << b >> c"
                                               else (if pow > (~p - 1)
                                                     then shuntingYardPat pats ctx ((pow,id)::opst) valst false
                                                     else shuntingYardCombineOpPat (p, i) pats ctx ((pow,id)::oprest) valst)
                            | (false, true) => if (~pow - 1) = p
                                               then raise IllegalElab "Elaborator Error: Equal right and left associativity cannot be mixed together. E.g. a >> b << c or a << b >> c"
                                               else (if (~pow - 1) > p
                                                     then shuntingYardPat pats ctx ((pow,id)::opst) valst false
                                                     else shuntingYardCombineOpPat (p, i) pats ctx ((pow,id)::oprest) valst))
       | _ => shuntingYardCombinePat pat pats ctx opst valst b)
  | shuntingYardPat ((pat as P.PatId (true, [id])) :: pats) ctx opst valst b =
    (case checkInfix id ctx of
         SOME (_, SOME _) => shuntingYardCombinePat pat pats ctx opst valst b
       | _ => raise IllegalElab "Elaborator Error: `op` applied to a nonfix value. Either forgot to infix or misused `op`")
  | shuntingYardPat ((pat as P.PatId (true, _)) :: pats) ctx opst valst b = raise IllegalElab "Elaborator Error: `op` applied to a nonfix value construct. Constructs cannot be infixed (e.g. Module.+ has to be nonfix)"
  | shuntingYardPat (pat::pats) ctx opst valst true = shuntingYardCombinePat (elaboratePat (pat, ctx)) pats ctx opst valst true
  | shuntingYardPat (pat::pats) ctx opst valst false = shuntingYardCombinePat (elaboratePat (pat, ctx)) pats ctx opst valst false

and elaboratePat (P.PatApp pats, ctx) = shuntingYardPat pats ctx [] [] false
  | elaboratePat (P.PatRecord rows, ctx) =
    P.PatRecord
        (ListSort.sort (fn (P.PatRecordEntryA (ll, _), P.PatRecordEntryA (rl, _)) => ll >= rl
                       | (P.PatRecordEntryA (ll, _), P.PatRecordEntryB (rl, _, _)) => ll >= rl
                       | (P.PatRecordEntryB (ll, _, _), P.PatRecordEntryA (rl, _)) => ll >= rl
                       | (P.PatRecordEntryB (ll, _, _), P.PatRecordEntryB (rl, _, _)) => ll >= rl)
                       (List.map (fn P.PatRecordEntryA (lab, pat) =>
                                     P.PatRecordEntryA (lab, elaboratePat (pat, ctx))
                                 | P.PatRecordEntryB (lab, typ, pat) =>
                                   P.PatRecordEntryB (lab, typ, Option.map (fn p => elaboratePat (p, ctx)) pat))
                                 rows))
  | elaboratePat (P.PatList pats, ctx) = P.PatList (List.map (fn pat => elaboratePat (pat, ctx)) pats)
  | elaboratePat (P.PatTypeAnnote (pat, typ), ctx) = P.PatTypeAnnote (elaboratePat (pat, ctx), typ)
  | elaboratePat (P.PatLayered (opr, lid, typ, pat), ctx) = P.PatLayered (opr, lid, typ, elaboratePat (pat, ctx))
  | elaboratePat (ast, _) = ast

fun shuntingYardCombineOpExp (p, id) exps ctx opst (v::u::valst) =
    if p >= 0
    then shuntingYard exps ctx opst ((P.ExpInfixApp (u, id, v))::valst) false
    else shuntingYard exps ctx opst ((P.ExpInfixApp (v, id, u))::valst) false
  | shuntingYardCombineOpExp (p, id) exps ctx opst ((P.ExpApp (e::es))::valst) =
    if p >= 0
    then shuntingYard exps ctx opst ((P.ExpInfixApp (P.ExpApp es, id, e))::valst) false
    else shuntingYard exps ctx opst ((P.ExpInfixApp (e, id, P.ExpApp es))::valst) false
  | shuntingYardCombineOpExp (p, id) exps ctx opst _ = raise IllegalElab "Elaborator Error: Infix operator has no operands."

and shuntingYardCombineExp exp exps ctx opst (allvalst as ((P.ExpApp es)::valst)) b =
    if b
    then shuntingYard exps ctx opst ((P.ExpApp (exp::es))::valst) true
    else shuntingYard exps ctx opst (exp::allvalst) true
  | shuntingYardCombineExp exp exps ctx opst (allvalst as (e::valst)) b =
    if b
    then shuntingYard exps ctx opst ((P.ExpApp (exp::[e]))::valst) true
    else shuntingYard exps ctx opst (exp::allvalst) true
  | shuntingYardCombineExp exp exps ctx opst [] b = shuntingYard exps ctx opst [exp] true

and shuntingYard [] ctx [] [v] _ = v
  | shuntingYard [] ctx [] xs _ = raise ImproperElabResultExp xs
  | shuntingYard [] ctx ((p, id)::opst) valst _ = shuntingYardCombineOpExp (p, id) [] ctx opst valst
  | shuntingYard ((exp as P.ExpValId (false, [id])) :: exps) ctx opst valst b =
    (case checkInfix id ctx of
         SOME (_, SOME pow) => (case opst of
                          [] => shuntingYard exps ctx [(pow,id)] valst false
                        | ((p,i)::oprest) =>
                          case (p < 0, pow < 0) of
                              (true, true) => if pow <= p
                                              then shuntingYard exps ctx ((pow,id)::opst) valst false
                                              else shuntingYardCombineOpExp (p, i) exps ctx ((pow,id)::oprest) valst
                            | (false, false) => if pow >= p
                                                then shuntingYard exps ctx ((pow,id)::opst) valst false
                                                else shuntingYardCombineOpExp (p, i) exps ctx ((pow,id)::oprest) valst
                            | (true, false) => if pow = (~p - 1)
                                               then raise IllegalElab "Elaborator Error: Equal right and left associativity cannot be mixed together. E.g. a >> b << c or a << b >> c"
                                               else (if pow >= (~p - 1)
                                                     then shuntingYard exps ctx ((pow,id)::opst) valst false
                                                     else shuntingYardCombineOpExp (p, i) exps ctx ((pow,id)::oprest) valst)
                            | (false, true) => if (~pow - 1) = p
                                               then raise IllegalElab "Elaborator Error: Equal right and left associativity cannot be mixed together. E.g. a >> b << c or a << b >> c"
                                               else (if (~pow - 1) >= p
                                                     then shuntingYard exps ctx ((pow,id)::opst) valst false
                                                     else shuntingYardCombineOpExp (p, i) exps ctx ((pow,id)::oprest) valst))
       | _ => shuntingYardCombineExp exp exps ctx opst valst b)
  | shuntingYard ((exp as P.ExpValId (true, [id])) :: exps) ctx opst valst b =
    (case checkInfix id ctx of
         SOME (_, SOME _) => shuntingYardCombineExp exp exps ctx opst valst b
       | _ => raise IllegalElab "Elaborator Error: `op` applied to a nonfix value. Either forgot to infix or misused `op`")
  | shuntingYard ((exp as P.ExpValId (true, _)) :: exps) ctx opst valst b = raise IllegalElab "Elaborator Error: `op` applied to a nonfix value construct. Constructs cannot be infixed (e.g. Module.+ has to be nonfix)"
  | shuntingYard (exp::exps) ctx opst valst true = shuntingYardCombineExp (elaborateExp (exp, ctx)) exps ctx opst valst true
  | shuntingYard (exp::exps) ctx opst valst false = shuntingYardCombineExp (elaborateExp (exp, ctx)) exps ctx opst valst false

and elaborateExp (P.ExpApp exps, ctx) = shuntingYard exps ctx [] [] false
  | elaborateExp (P.ExpRecord rows, ctx) = P.ExpRecord (ListSort.sort (fn ((ll, _), (rl, _)) => ll >= rl) (List.map (fn (lab, exp) => (lab, elaborateExp (exp, ctx))) rows))
  | elaborateExp (P.ExpList exps, ctx) = P.ExpList (List.map (fn exp => elaborateExp (exp, ctx)) exps)
  | elaborateExp (P.ExpSeq exps, ctx) = P.ExpSeq (List.map (fn exp => elaborateExp (exp, ctx)) exps)
  | elaborateExp (P.ExpLocalDecl (decl, exps), ctx) =
    let val (decl, ctx) = elaborateDecl (decl, ctx)
    in
        P.ExpLocalDecl (decl, (List.map (fn exp => elaborateExp (exp, ctx)) exps))
    end
  | elaborateExp (P.ExpTypeAnnote (exp, typ), ctx) = P.ExpTypeAnnote (elaborateExp (exp, ctx), typ)
  | elaborateExp (P.ExpExceptionRaise exp, ctx) = P.ExpExceptionRaise (elaborateExp (exp, ctx))
  | elaborateExp (P.ExpExceptionHandle (exp, matches), ctx) = P.ExpExceptionHandle (elaborateExp (exp, ctx), List.map (fn (pat, exp) => (elaboratePat (pat, ctx), elaborateExp (exp, ctx))) matches)
  | elaborateExp (P.ExpConj (expl, expr), ctx) = P.ExpConj (elaborateExp (expl, ctx), elaborateExp (expr, ctx))
  | elaborateExp (P.ExpDisj (expl, expr), ctx) = P.ExpDisj (elaborateExp (expl, ctx), elaborateExp (expr, ctx))
  | elaborateExp (P.ExpCond (expl, expm, expr), ctx) = P.ExpCond (elaborateExp (expl, ctx), elaborateExp (expm, ctx), elaborateExp (expr, ctx))
  | elaborateExp (P.ExpIter (expl, expr), ctx) = P.ExpIter (elaborateExp (expl, ctx), elaborateExp (expr, ctx))
  | elaborateExp (P.ExpMatch (exp, matches), ctx) = P.ExpMatch (elaborateExp (exp, ctx), List.map (fn (pat, exp) => (elaboratePat (pat, ctx), elaborateExp (exp, ctx))) matches)
  | elaborateExp (P.ExpFn matches, ctx) = P.ExpFn (List.map (fn (pat, exp) => (elaboratePat (pat, ctx), elaborateExp (exp, ctx))) matches)
  | elaborateExp (ast, _) = ast

(* TODO: Handle modules and local-let kind scopes for infixes
     Can also handle it later on with scope managing semantics checking *)
and elaborateDecl (P.DeclSeq [decl], ctx) = elaborateDecl (decl, ctx)
  | elaborateDecl (P.DeclSeq seq, ctx) =
    let val (lst, ctx) =
            (List.foldl (fn (x, (lst, ctx)) =>
                            let val (y, ctx) = elaborateDecl (x, ctx)
                            in (y::lst, ctx)
                            end)
                        ([], ctx) seq)
    in
        (P.DeclSeq (List.rev lst), ctx)
    end
  | elaborateDecl (P.DeclVal (vars, vals), ctx) =
    (P.DeclVal (vars, List.map (fn (b, p, exp) => (b, elaboratePat (p, ctx), elaborateExp (exp, ctx))) vals), ctx)
  | elaborateDecl (P.DeclFun (vars, fs), ctx) =
    (P.DeclFun (vars, List.map (fn P.DeclFunNonfix matches =>
                                   P.DeclFunNonfix (List.map (fn (b, id, ps, typ, exp) =>
                                                                 (b, id,
                                                                  List.map (fn p => elaboratePat (p, ctx)) ps,
                                                                  typ,
                                                                  elaborateExp (exp, ctx))) matches)
                               | P.DeclFunInfixOne matches =>
                                 (case matches of
                                      (_, id, _, _, _)::_ =>
                                      (case checkInfix id ctx of
                                           SOME (_, SOME _) =>
                                           P.DeclFunInfixOne (List.map (fn (pl, id, pr, typ, exp) =>
                                                                           (elaboratePat (pl, ctx),
                                                                            id,
                                                                            elaboratePat (pr, ctx),
                                                                            typ,
                                                                            elaborateExp (exp, ctx))) matches)
                                         | _ =>
                                           P.DeclFunNonfix (List.map (fn (P.PatId (_, [id]), pl, pr, typ, exp) =>
                                                                         (false, id,
                                                                          [P.PatId (false, [pl]), elaboratePat (pr, ctx)],
                                                                          typ,
                                                                          elaborateExp (exp, ctx))
                                                                     | _ => raise IllegalElab "Expected either proper infix or proper nonfix function, found neither") matches))
                                    | [] => raise IllegalElab "Empty functions are impossible")
                               | P.DeclFunInfixMany matches =>
                                 P.DeclFunInfixMany (List.map (fn (pl, id, pr, ps, typ, exp) =>
                                                                  (elaboratePat (pl, ctx),
                                                                   id,
                                                                   elaboratePat (pr, ctx),
                                                                   List.map (fn p => elaboratePat (p, ctx)) ps,
                                                                   typ,
                                                                   elaborateExp (exp, ctx))) matches)) fs),
     ctx)
  | elaborateDecl (P.DeclAbsTyp (dbind, tbind, decl), ctx) =
    (P.DeclAbsTyp (dbind, tbind, #1 (elaborateDecl (decl, ctx))), ctx)
  | elaborateDecl (P.DeclLocal (decll, declr), ctx) =
    let val (decll, ctxl) = elaborateDecl (decll, ctx)
        val (declr, _) = elaborateDecl (declr, ctxl)
    in (P.DeclLocal (decll, declr), ctx)
    end
  | elaborateDecl (P.DeclNonfix ids, ctx) =
    let val ctx = List.foldl (fn (id, acc) => removeInfix id acc) ctx ids
    in (P.DeclNonfix ids, ctx)
    end
  | elaborateDecl (P.DeclInfix (SOME fix, ids), ctx) =
    let val ctx = List.foldl (fn (id, acc) => addInfix fix id acc) ctx ids
    in (P.DeclInfix (SOME fix, ids), ctx)
    end
  | elaborateDecl (P.DeclInfix (NONE, ids), ctx) =
    let val ctx = List.foldl (fn (id, acc) => addInfix 0 id acc) ctx ids
    in (P.DeclInfix (SOME 0, ids), ctx)
    end
  | elaborateDecl (P.DeclInfixR (SOME fix, ids), ctx) =
    let val ctx = List.foldl (fn (id, acc) => addInfix (~fix - 1) id acc) ctx ids
    in (P.DeclInfixR (SOME (~fix - 1), ids), ctx)
    end
  | elaborateDecl (P.DeclInfixR (NONE, ids), ctx) =
    let val ctx = List.foldl (fn (id, acc) => addInfix ~1 id acc) ctx ids
    in (P.DeclInfixR (SOME ~1, ids), ctx)
    end
  | elaborateDecl (ast, ctx) = (ast, ctx)

fun elaborate (decl, _) =
    let val tinfix = [("*", 7), ("/", 7), ("div", 7), ("mod",7),
                      ("+", 6), ("-", 6), ("^", 6), ("::", ~6), ("@", ~6),
                      ("=", 4), ("<>", 4), (">", 4), ("<", 4), (">=", 4), ("<=", 4),
                      (":=", 3), ("o", 3), ("before", 0)]
    in
        elaborateDecl (decl, {tinfix=List.map (fn (x, y) => (x, SOME y)) tinfix})
    end
end
