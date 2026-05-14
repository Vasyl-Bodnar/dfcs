(* This Source Code Form is subject to the terms of the Mozilla Public
   License, v. 2.0. If a copy of the MPL was not distributed with this
   file, You can obtain one at http://mozilla.org/MPL/2.0/. *)
(* Currently used for fixing infix operators *)
structure Elaborator = struct
  structure P = Parser
  exception IllegalElab of string
  exception ImproperElabResult of P.exp list

  fun checkInfix id (P.Ctx {htinfix, ...}) = HashArray.sub (htinfix, id)

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
                         | ((p,i)::oprest) => if pow >= p
                                              then shuntingYard exps ctx ((pow,id)::opst) valst false
                                              else shuntingYardCombineOp (p, i) exps ctx ((pow,id)::oprest) valst)
        | NONE => shuntingYardCombineExp exp exps ctx opst valst b)
    | shuntingYard ((exp as P.ExpValId (true, [id])) :: exps) ctx opst valst b =
      (case checkInfix id ctx of
           SOME _ => shuntingYardCombineExp exp exps ctx opst valst b
         | NONE => raise IllegalElab "Elaborator Error: `op` applied to a nonfix value. Either forgot to infix or misused `op`")
    | shuntingYard ((exp as P.ExpValId (true, _)) :: exps) ctx opst valst b = raise IllegalElab "Elaborator Error: `op` applied to a nonfix value construct. Constructs cannot be infixed (e.g. Module.+ has to be nonfix)"
    | shuntingYard (exp::exps) ctx opst valst true = shuntingYardCombineExp exp exps ctx opst valst true
    | shuntingYard (exp::exps) ctx opst valst false = shuntingYardCombineExp exp exps ctx opst valst false

  (* TODO: Handle all cases of multiple exps *)
  fun elaborateExp (P.ExpApp exps, ctx) = shuntingYard exps ctx [] [] false
    | elaborateExp (ast, _) = ast

  (* TODO: Handle modules and local-let kind scopes for infixes
     Can also handle it later on with scope managing semantics checking *)
  fun elaborateDecl (P.DeclSeq seq, ctx) =
      P.DeclSeq (List.map (fn x => elaborateDecl (x, ctx)) seq)
    | elaborateDecl (P.DeclVal (vars, vals), ctx) =
      P.DeclVal (vars, List.map (fn (b, p, e) => (b, p, elaborateExp (e, ctx))) vals)
    | elaborateDecl (ast, _) = ast
end
