(* This Source Code Form is subject to the terms of the Mozilla Public
   License, v. 2.0. If a copy of the MPL was not distributed with this
   file, You can obtain one at http://mozilla.org/MPL/2.0/. *)
datatype ('ok, 'err) result = Ok of 'ok
                            | Err of 'err

structure Result = struct
fun map f (Ok ok) = Ok (f ok)
  | map f (Err err) = Err err

fun bind f (Ok ok) = (f ok)
  | bind f (Err err) = Err err

fun seq init res = List.foldr (fn (x, acc) => bind (fn _ => x) acc) init res

fun isOk (Ok _) = true
  | isOk (Err _) = false
end
