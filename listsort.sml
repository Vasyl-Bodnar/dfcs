(* This Source Code Form is subject to the terms of the Mozilla Public
   License, v. 2.0. If a copy of the MPL was not distributed with this
   file, You can obtain one at http://mozilla.org/MPL/2.0/. *)
signature LIST_SORT = sig
    val sort : (('a * 'a) -> bool) -> 'a list -> 'a list
end

structure ListSort :> LIST_SORT = struct
fun merge _ (xs, []) = xs
  | merge _ ([], xs) = xs
  | merge ge (x::xs, y::ys) = if ge (y, x)
                              then x :: (merge ge (xs, y::ys))
                              else y :: (merge ge (x::xs, ys))

fun combiner [] = []
  | combiner [x] = [(x, [])]
  | combiner (x::y::xs) = (x,y)::(combiner xs)

fun merger _ [] = []
  | merger _ [(x, [])] = x
  | merger ge xs = merger ge (combiner (List.map (merge ge) xs))

fun extractAsc ge [] = ([], [])
  | extractAsc ge [x] = ([x], [])
  | extractAsc ge (x::y::xs) =
    if ge (y, x) then
        let val (run, rest) = extractAsc ge (y::xs)
        in (x :: run, rest)
        end
    else ([], x::y::xs)

fun extractDes ge [] acc = acc
  | extractDes ge [x] (acc, rest) = (x::acc, rest)
  | extractDes ge (x::y::xs) (acc, rest) =
    if ge (y, x) then (acc, x::y::xs)
    else extractDes ge (y::xs) (x::acc, rest)

fun natural ge [] = []
  | natural ge [x] = [[x]]
  | natural ge (x::y::xs) = if ge (y, x) then
                                let val (run, rest) = extractAsc ge (y::xs)
                                in (x::run)::(natural ge rest)
                                end
                            else
                                let val (run, rest) = extractDes ge (x::y::xs) ([], [])
                                in run::(natural ge rest)
                                end

fun sort _ [] = []
  | sort _ [x] = [x]
  | sort ge xs = merger ge (combiner (natural ge xs))
end
