signature LIST_SORT = sig
    val sort : (('a * 'a) -> bool) -> 'a list -> 'a list
end

structure ListSort :> LIST_SORT = struct
fun splitAt' [] _ acc = (acc, [])
  | splitAt' xs 0 acc = (acc, xs)
  | splitAt' (x::xs) n acc = splitAt' xs (n-1) (x::acc)

fun splitAt xs n = splitAt' xs n []

fun merge _ (xs, []) = xs
  | merge _ ([], xs) = xs
  | merge ge (x::xs, y::ys) = if ge (y, x)
                              then x :: (merge ge (xs, y::ys))
                              else y :: (merge ge (x::xs, ys))

fun sort _ [] = []
  | sort _ [x] = [x]
  | sort ge xs = merge ge ((fn (xs, ys) => (sort ge xs, sort ge ys))
                               (splitAt xs ((List.length xs) div 2)))
end
