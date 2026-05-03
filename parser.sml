(* This Source Code Form is subject to the terms of the Mozilla Public
   License, v. 2.0. If a copy of the MPL was not distributed with this
   file, You can obtain one at http://mozilla.org/MPL/2.0/. *)
datatype ('ok, 'err) result = Ok of 'ok
                            | Err of 'err
infix 1 |>
fun x |> y = (y x)

structure Result = struct
  fun map f (Ok ok) = Ok (f ok)
    | map f (Err err) = Err err

  fun bind f (Ok ok) = (f ok)
    | bind f (Err err) = Err err
end

structure Parser = struct
  type 'a parser = string * int -> ('a * string * int, string * string * int) result

  fun mapRes f (Ok (ok, str, idx)) = Ok (f ok, str, idx)
    | mapRes f (Err (err, str, idx)) = Err (err, str, idx)

  fun map f p (str, idx) = mapRes f (p (str, idx))
  fun mapFull f p (str, idx) = Result.map f (p (str, idx))

  fun bindFull f p (str, idx) = Result.bind f (p (str, idx))

  fun isOk (Ok _) = true
    | isOk (Err _) = false

  fun parse (p : 'a parser) str idx = p (str, idx)
end

fun ch c (str, idx) =
    if idx < (String.size str) andalso String.sub (str, idx) = c
    then Ok (c, str, idx+1)
    else Err ("ERROR in ch with c = " ^ String.str c ^ "\n", str, idx)

fun str s (str, idx) =
    if String.size str < String.size s then
      Err (("ERROR in str with s = \"" ^ s ^ "\", s is too large\n"), str, idx)
    else let
      val subs = Substring.extract (s, 0, NONE)
      val substr = Substring.substring (str, idx, Substring.size subs)
    in
      if Substring.compare (substr, subs) = EQUAL
      then Ok (substr, str, idx + (Substring.size substr))
      else Err ("ERROR in str with s = \"" ^ s ^ "\"\n", str, idx)
    end

fun notChs cs (str, idx) =
    if idx < (String.size str) andalso not (List.exists (fn c => c = String.sub (str, idx)) cs)
    then Ok (String.sub (str, idx), str, idx+1)
    else Err ("ERROR in ch with cs = [" ^ (String.concatWith "," (map String.str cs)) ^ "]\n", str, idx)

fun ignoreLeft p q = Parser.bindFull (fn (_, str, idx) => q (str, idx)) p
fun ignoreRight p q = Parser.bindFull (fn (res, str, idx) => (Parser.map (fn _ => res) q) (str, idx)) p
fun between lp q rp = ignoreRight (ignoreLeft lp q) rp

fun check f p (str, idx) =
    case (p (str, idx)) of
        Ok (ok, str, idx) => if f ok
                             then Ok (ok, str, idx)
                             else Err ("ERROR in check", str, idx)
       | Err err => Err err

fun chain ps (str, idx) = Parser.mapRes rev
        (foldl (fn (p, acc) =>
                      Result.bind (fn (oks, str, idx) =>
                                     Result.map (fn (ok, str, idx) =>
                                                    (ok :: oks, str, idx))
                                                (p (str, idx)))
                                  acc)
               (Ok ([], str, idx)) ps)

fun many p (str, idx) =
    case p (str, idx) of
        Ok (ok, str, idx) => let val Ok (oks, str, idx) = many p (str, idx)
                             in Ok (ok :: oks, str, idx)
                             end
      | Err (err, str, idx) => Ok ([], str, idx)

fun some p (str, idx) =
    case p (str, idx) of
        Ok (ok, str, idx) => let val resNext = many p (str, idx)
                             in case resNext of
                                    Ok (oks, str, idx) => Ok (ok :: oks, str, idx)
                                  | Err (err, _, _) => Ok ([ok], str, idx)
                             end
      | Err err => Err err

fun choose [] (str, idx) = Err (("ERROR in choose with no correct choice"), str, idx)
  | choose (p::ps) (str, idx) =
    let val res = p (str, idx)
    in
      if Parser.isOk res
      then res
      else choose ps (str, idx)
    end

fun opt default p (str, idx) =
    let val res = p (str, idx)
    in
      if Parser.isOk res
      then res
      else Ok (default, str, idx)
    end

datatype con = ConInt of int
              | ConWord of word (* TODO: Currently unused *)
              | ConReal of real (* TODO: Currently unused *)
              | ConChar of char
              | ConString of string
              | ConNegate of bool

val digit = (choose (map ch [#"0", #"1", #"2", #"3", #"4", #"5", #"6", #"7", #"8", #"9"]))
val conHexLetter = Parser.map (fn dig => (Char.ord (Char.toLower dig)) - (Char.ord #"a") + 10) (choose (List.map ch [#"a", #"b", #"c", #"d", #"e", #"f", #"A", #"B", #"C", #"D", #"E", #"F"]))
val conDigit = Parser.map (fn dig => (Char.ord dig) - (Char.ord #"0")) digit
val conNonZeroDigit = Parser.map (fn dig => (Char.ord dig) - (Char.ord #"0")) (choose (map ch [#"1", #"2", #"3", #"4", #"5", #"6", #"7", #"8", #"9"]))
val conHex = Parser.map ConInt (ignoreLeft (str "0x") (Parser.map (foldl (fn (num, acc) => acc * 16 + num) 0) (some (choose [conDigit, conHexLetter]))))
val conNum = Parser.map ConInt (Parser.map (foldl (fn (num, acc) => acc * 10 + num) 0) (some conDigit))
val conNonZeroNum = Parser.map (foldl (fn (num, acc) => acc * 10 + num) 0)
                               (Parser.map List.concat (chain [Parser.map (fn x => [x]) conNonZeroDigit, many conDigit]))
val conInt = Parser.map (fn [ConNegate neg, ConInt num] => ConInt (if neg then ~num else num))
                        (chain [opt (ConNegate false) (Parser.map (fn _ => ConNegate true) (ch #"~")), choose [conHex, conNum]])

val conAscii =
    choose [ignoreLeft (ch #"\\")
                       (choose [(ch #"\\"), (ch #"\""),
                                Parser.map (fn _ => #"\a") (ch #"a"),
                                Parser.map (fn _ => #"\b") (ch #"b"),
                                Parser.map (fn _ => #"\t") (ch #"t"),
                                Parser.map (fn _ => #"\n") (ch #"n"),
                                Parser.map (fn _ => #"\v") (ch #"v"),
                                Parser.map (fn _ => #"\f") (ch #"f"),
                                Parser.map (fn _ => #"\r") (ch #"r")
                                (* \^c where c is @-] *)
                                (* \ddd where d is 0-9 *)
                                (* \uxxxx where x is 0-F *)
                                (* \f..f\ where f..f is ignored formatting *)]),
            notChs [#"\""]]
val conChar = Parser.map ConChar (between (ignoreLeft (ch #"#") (ch #"\"")) conAscii (ch #"\""))
val conString = Parser.map (fn list => ConString (String.implode list)) (between (ch #"\"") (many conAscii) (ch #"\""))

val letter = choose (map ch [#"a",#"b",#"c",#"d",#"e",#"f",#"g",#"h",#"i",#"j",#"k",#"l",#"m",#"n",#"o",#"p",#"q",#"r",#"s",#"t",#"u",#"v",#"w",#"x",#"y",#"z",
                             #"A",#"B",#"C",#"D",#"E",#"F",#"G",#"H",#"I",#"J",#"K",#"L",#"M",#"N",#"O",#"P",#"Q",#"R",#"S",#"T",#"U",#"V",#"W",#"X",#"Y",#"Z"])
val symbolic = choose (map ch [#"!",#"%",#"&",#"$",#"#",#"+",#"-",#"/",#":",#"<",#"=",#">",#"?",#"@",#"\\",#"~",#"`",#"^",#"|",#"*"])
val reserved = ["abstype", "and", "andalso", "as", "case", "datatype", "do", "else", "end",
                "exception", "fn", "fun", "handle", "if", "in", "infix", "infixr", "let",
                "local", "nonfix", "of", "op", "open", "orelse", "raise", "rec", "then",
                "type", "val", "with", "withtype", "while", "(", ")", "[", "]", "{",
                "}", ",", ":", ";", "...", "_", "|", "=", "=>", "->", "#"]

val coreCon = choose [conInt, conChar, conString]
val coreId = check (fn s => not (List.exists (fn r => (String.compare (s, r)) = EQUAL) reserved))
                   (choose [Parser.map (fn ls => String.implode (List.concat ls))
                                       (chain [Parser.map (fn x => [x]) letter,
                                               many (choose [letter, digit, ch #"_", ch #"'"])]),
                            Parser.map String.implode (some symbolic)])
(* TODO: A bit more special than just one/two primes at the start *)
val coreVar = ignoreLeft (ch #"'") (Parser.map (fn ls => String.implode (List.concat ls))
                                (chain [Parser.map (fn x => [x]) letter,
                                        many (choose [letter, digit, ch #"_", ch #"'"])]))
val coreLongId = Parser.map List.concat (chain [Parser.map (fn x => [x]) coreId, many (ignoreLeft (ch #".") coreId)])
val coreLab = choose [coreId, Parser.map Int.toString conNonZeroNum]
