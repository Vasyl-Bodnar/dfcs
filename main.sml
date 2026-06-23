(* This Source Code Form is subject to the terms of the Mozilla Public
   License, v. 2.0. If a copy of the MPL was not distributed with this
   file, You can obtain one at http://mozilla.org/MPL/2.0/. *)
val _ = PolyML.make "result"
val _ = PolyML.make "listsort"

val _ = PolyML.make "parser"

val _ = PolyML.make "elaborator"

val _ = PolyML.make "inferencer"

(*
fun doAll s = Result.map Inferencer.infer (Result.map Elaborator.elaborate (Parser.parse Parser.coreDecl s))
*)

(* TODO: Combinable errors *)
(* TODO: Proper Infixes in Elaborator *)
