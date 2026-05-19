(* This Source Code Form is subject to the terms of the Mozilla Public
   License, v. 2.0. If a copy of the MPL was not distributed with this
   file, You can obtain one at http://mozilla.org/MPL/2.0/. *)
(* Currently used for fixing infix operators *)
structure Elaborator = struct
  structure P = Parser
  exception IllegalElab of string
  exception ImproperElabResult of P.exp list

  datatype ctx = Ctx of {htinfix: int HashArray.hash}

  fun checkInfix id (Ctx {htinfix, ...}) = HashArray.sub (htinfix, id)
  fun removeInfix id (Ctx {htinfix, ...}) = HashArray.delete (htinfix, id)
  fun addInfix fix id (Ctx {htinfix, ...}) = HashArray.update (htinfix, id, fix)

  fun shuntingYardCombineOp (p, id) exps ctx opst (v::u::valst) =
      if p >= 0
      then shuntingYard exps ctx opst ((P.ExpInfixApp (u, id, v))::valst) false
      else shuntingYard exps ctx opst ((P.ExpInfixApp (v, id, u))::valst) false
    | shuntingYardCombineOp (p, id) exps ctx opst ((P.ExpApp (e::es))::valst) =
      if p >= 0
      then shuntingYard exps ctx opst ((P.ExpInfixApp (P.ExpApp es, id, e))::valst) false
      else shuntingYard exps ctx opst ((P.ExpInfixApp (e, id, P.ExpApp es))::valst) false
    | shuntingYardCombineOp (p, id) exps ctx opst _ = raise IllegalElab "Elaborator Error: Infix operator has no operands."

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
    | shuntingYard [] ctx [] xs _ = raise ImproperElabResult xs
    | shuntingYard [] ctx ((p, id)::opst) valst _ = shuntingYardCombineOp (p, id) [] ctx opst valst
    | shuntingYard ((exp as P.ExpValId (false, [id])) :: exps) ctx opst valst b =
      (case checkInfix id ctx of
          SOME pow => (case opst of
                           [] => shuntingYard exps ctx [(pow,id)] valst false
                         | ((p,i)::oprest) =>
                           case (p < 0, pow < 0) of
                               (true, true) => if pow <= p
                                               then shuntingYard exps ctx ((pow,id)::opst) valst false
                                               else shuntingYardCombineOp (p, i) exps ctx ((pow,id)::oprest) valst
                             | (false, false) => if pow >= p
                                               then shuntingYard exps ctx ((pow,id)::opst) valst false
                                               else shuntingYardCombineOp (p, i) exps ctx ((pow,id)::oprest) valst
                             | (true, false) => if pow = (~p - 1)
                                               then raise IllegalElab "Elaborator Error: Equal right and left associativity cannot be mixed together. E.g. a >> b << c or a << b >> c"
                                               else (if pow >= (~p - 1)
                                               then shuntingYard exps ctx ((pow,id)::opst) valst false
                                               else shuntingYardCombineOp (p, i) exps ctx ((pow,id)::oprest) valst)
                             | (false, true) => if (~pow - 1) = p
                                               then raise IllegalElab "Elaborator Error: Equal right and left associativity cannot be mixed together. E.g. a >> b << c or a << b >> c"
                                               else (if (~pow - 1) >= p
                                               then shuntingYard exps ctx ((pow,id)::opst) valst false
                                               else shuntingYardCombineOp (p, i) exps ctx ((pow,id)::oprest) valst))
        | NONE => shuntingYardCombineExp exp exps ctx opst valst b)
    | shuntingYard ((exp as P.ExpValId (true, [id])) :: exps) ctx opst valst b =
      (case checkInfix id ctx of
           SOME _ => shuntingYardCombineExp exp exps ctx opst valst b
         | NONE => raise IllegalElab "Elaborator Error: `op` applied to a nonfix value. Either forgot to infix or misused `op`")
    | shuntingYard ((exp as P.ExpValId (true, _)) :: exps) ctx opst valst b = raise IllegalElab "Elaborator Error: `op` applied to a nonfix value construct. Constructs cannot be infixed (e.g. Module.+ has to be nonfix)"
    | shuntingYard (exp::exps) ctx opst valst true = shuntingYardCombineExp (elaborateExp (exp, ctx)) exps ctx opst valst true
    | shuntingYard (exp::exps) ctx opst valst false = shuntingYardCombineExp (elaborateExp (exp, ctx)) exps ctx opst valst false

  and elaborateExp (P.ExpApp exps, ctx) = shuntingYard exps ctx [] [] false
    | elaborateExp (P.ExpTuple exps, ctx) = P.ExpTuple (List.map (fn exp => elaborateExp (exp, ctx)) exps)
    | elaborateExp (P.ExpRecord rows, ctx) = P.ExpRecord (List.map (fn (lab, exp) => (lab, elaborateExp (exp, ctx))) rows)
    | elaborateExp (P.ExpList exps, ctx) = P.ExpList (List.map (fn exp => elaborateExp (exp, ctx)) exps)
    | elaborateExp (P.ExpSeq exps, ctx) = P.ExpSeq (List.map (fn exp => elaborateExp (exp, ctx)) exps)
    | elaborateExp (P.ExpLocalDecl (decl, exps), ctx) = P.ExpLocalDecl (elaborateDecl (decl, ctx), (List.map (fn exp => elaborateExp (exp, ctx)) exps))
    | elaborateExp (P.ExpTypeAnnote (exp, typ), ctx) = P.ExpTypeAnnote (elaborateExp (exp, ctx), typ)
    | elaborateExp (P.ExpExceptionRaise exp, ctx) = P.ExpExceptionRaise (elaborateExp (exp, ctx))
    | elaborateExp (P.ExpExceptionHandle (exp, matches), ctx) = P.ExpExceptionHandle (elaborateExp (exp, ctx), List.map (fn (pat, exp) => (pat, elaborateExp (exp, ctx))) matches)
    | elaborateExp (P.ExpConj (expl, expr), ctx) = P.ExpConj (elaborateExp (expl, ctx), elaborateExp (expr, ctx))
    | elaborateExp (P.ExpDisj (expl, expr), ctx) = P.ExpDisj (elaborateExp (expl, ctx), elaborateExp (expr, ctx))
    | elaborateExp (P.ExpCond (expl, expm, expr), ctx) = P.ExpCond (elaborateExp (expl, ctx), elaborateExp (expm, ctx), elaborateExp (expr, ctx))
    | elaborateExp (P.ExpIter (expl, expr), ctx) = P.ExpIter (elaborateExp (expl, ctx), elaborateExp (expr, ctx))
    | elaborateExp (P.ExpMatch (exp, matches), ctx) = P.ExpMatch (elaborateExp (exp, ctx), List.map (fn (pat, exp) => (pat, elaborateExp (exp, ctx))) matches)
    | elaborateExp (P.ExpFn matches, ctx) = P.ExpFn (List.map (fn (pat, exp) => (pat, elaborateExp (exp, ctx))) matches)
    | elaborateExp (ast, _) = ast

  (* TODO: Handle modules and local-let kind scopes for infixes
     Can also handle it later on with scope managing semantics checking *)
  and elaborateDecl (P.DeclSeq [decl], ctx) = elaborateDecl (decl, ctx)
    | elaborateDecl (P.DeclSeq seq, ctx) =
      P.DeclSeq (List.map (fn x => elaborateDecl (x, ctx)) seq)
    | elaborateDecl (P.DeclVal (vars, vals), ctx) =
      P.DeclVal (vars, List.map (fn (b, p, exp) => (b, p, elaborateExp (exp, ctx))) vals)
    | elaborateDecl (P.DeclFun (vars, fs), ctx) =
      P.DeclFun (vars, List.map (fn P.DeclFunNonfix matches =>
                                    P.DeclFunNonfix (List.map (fn (b, id, ps, typ, exp) =>
                                                                  (b, id, ps, typ, elaborateExp (exp, ctx))) matches)) fs)
    | elaborateDecl (P.DeclAbsTyp (dbind, tbind, decl), ctx) =
      P.DeclAbsTyp (dbind, tbind, elaborateDecl (decl, ctx))
    | elaborateDecl (P.DeclLocal (decll, declr), ctx) =
      P.DeclLocal (elaborateDecl (decll, ctx), elaborateDecl (declr, ctx))
    | elaborateDecl (P.DeclNonfix ids, ctx) =
      let val _ = List.app (fn id => removeInfix id ctx) ids
      in P.DeclNonfix ids
      end
    | elaborateDecl (P.DeclInfix (SOME fix, ids), ctx) =
      let val _ = List.app (fn id => addInfix fix id ctx) ids
      in P.DeclInfix (SOME fix, ids)
      end
    | elaborateDecl (P.DeclInfix (NONE, ids), ctx) =
      let val _ = List.app (fn id => addInfix 0 id ctx) ids
      in P.DeclInfix (SOME 0, ids)
      end
    | elaborateDecl (P.DeclInfixR (SOME fix, ids), ctx) =
      let val _ = List.app (fn id => addInfix (~fix - 1) id ctx) ids
      in P.DeclInfixR (SOME (~fix - 1), ids)
      end
    | elaborateDecl (P.DeclInfixR (NONE, ids), ctx) =
      let val _ = List.app (fn id => addInfix ~1 id ctx) ids
      in P.DeclInfixR (SOME ~1, ids)
      end
    | elaborateDecl (ast, _) = ast

  fun elaborate (decl, P.Ctx {htinfix, ...}) = elaborateDecl (decl, Ctx {htinfix=htinfix})
end
