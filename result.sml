datatype ('ok, 'err) result = Ok of 'ok
                            | Err of 'err

structure Result = struct
  fun map f (Ok ok) = Ok (f ok)
    | map f (Err err) = Err err

  fun bind f (Ok ok) = (f ok)
    | bind f (Err err) = Err err

  fun seq init res = List.foldr (fn (x, acc) => bind (fn _ => x) acc) init res
end
