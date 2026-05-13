(* This Source Code Form is subject to the terms of the Mozilla Public
   License, v. 2.0. If a copy of the MPL was not distributed with this
   file, You can obtain one at http://mozilla.org/MPL/2.0/. *)
(* Currently used for fixing infix operators *)
structure Elaborator = struct
  structure P = Parser
  exception IllegalElab of string

  fun checkInfix [id] (P.Ctx {htinfix, ...}) = HashArray.sub (htinfix, id)
    | checkInfix [] _ = NONE
    | checkInfix (x::xs) ctx = checkInfix xs ctx

  fun shuntingYard [] ctx [] valst = P.ExpApp valst
    | shuntingYard [] ctx ((p,exp)::opst) valst = shuntingYard [] ctx opst (exp::valst)
    | shuntingYard ((exp as P.ExpValId (false, id)) :: exps) ctx opst valst =
      (case checkInfix id ctx of
          SOME pow => (case opst of
                           [] => shuntingYard exps ctx [(pow,exp)] valst
                         | ((p,e)::oprest) => if p > pow
                                         then shuntingYard exps ctx ((pow,exp)::opst) valst
                                         else shuntingYard exps ctx ((pow,exp)::oprest) (e::valst))
        | NONE => shuntingYard exps ctx opst (exp::valst))
    | shuntingYard ((exp as P.ExpValId (true, id)) :: exps) ctx opst valst =
      (case checkInfix id ctx of
          SOME _ => shuntingYard exps ctx opst (exp::valst)
        | NONE => raise IllegalElab "Elaborator Error: `op` applied to a nonfix value. Either forgot to infix or misused `op`")
    | shuntingYard (exp::exps) ctx opst valst = shuntingYard exps ctx opst (exp::valst)

  fun elaborateExp (P.ExpApp exps, ctx) = shuntingYard exps ctx [] []
    | elaborateExp (ast, _) = ast

  (* TODO: Handle modules and local-let kind scopes for infixes
     Can also handle it later on with scope managing semantics checking *)
  fun elaborateDecl (P.DeclSeq seq, ctx) =
      P.DeclSeq (List.map (fn x => elaborateDecl (x, ctx)) seq)
    | elaborateDecl (P.DeclVal (vars, vals), ctx) =
      P.DeclVal (vars, List.map (fn (b, p, e) => (b, p, elaborateExp (e, ctx))) vals)
    | elaborateDecl (ast, _) = ast
end
