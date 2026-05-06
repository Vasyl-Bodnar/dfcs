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
  type ctx = {str: string, idx: int, htinfix: int HashArray.hash}
  type 'a parser = ctx -> ('a * ctx, string * ctx) result

  fun mapRes f (Ok (ok, ctx)) = Ok (f ok, ctx)
    | mapRes f (Err (err, ctx)) = Err (err, ctx)

  fun map f p ctx = mapRes f (p ctx)
  fun mapFull f p ctx = Result.map f (p ctx)

  fun bindFull f p ctx = Result.bind f (p ctx)

  fun isOk (Ok _) = true
    | isOk (Err _) = false

  fun parse (p : 'a parser) str =
      let val ht = HashArray.hash 20
      in
          app (fn (name, fix) => HashArray.update (ht, name, fix))
              [("*", 7), ("/", 7), ("div", 7), ("mod",7),
               ("+", 6), ("-", 6), ("^", 6), ("::", ~5), ("@", ~5),
               ("=", 4), ("<>", 4), (">", 4), ("<", 4), (">=", 4), ("<=", 4),
               (":=", 3), ("o", 3), ("before", 0)];
          p {str=str, idx=0, htinfix=ht}
      end

end

fun ch c ({str, idx, htinfix} : Parser.ctx) =
    if idx < (String.size str) andalso String.sub (str, idx) = c
    then Ok (c, {str=str, idx=idx+1, htinfix=htinfix})
    else Err ("ERROR in ch with c = " ^ String.str c ^ "\n", {str=str, idx=idx, htinfix=htinfix})

fun str s ({str, idx, htinfix} : Parser.ctx) =
    if String.size str - idx < String.size s then
      Err (("ERROR in str with s = \"" ^ s ^ "\", s is too large\n"), {str=str, idx=idx, htinfix=htinfix})
    else let
      val subs = Substring.extract (s, 0, NONE)
      val substr = Substring.substring (str, idx, Substring.size subs)
    in
      if Substring.compare (substr, subs) = EQUAL
      then Ok (substr, {str=str, idx=idx + Substring.size substr, htinfix=htinfix})
      else Err ("ERROR in str with s = \"" ^ s ^ "\"\n", {str=str, idx=idx, htinfix=htinfix})
    end

fun notChs cs ({str, idx, htinfix} : Parser.ctx) =
    if idx < (String.size str) andalso not (List.exists (fn c => c = String.sub (str, idx)) cs)
    then Ok (String.sub (str, idx), {str=str, idx=idx+1, htinfix=htinfix})
    else Err ("ERROR in ch with cs = [" ^ (String.concatWith "," (map String.str cs)) ^ "]\n", {str=str, idx=idx, htinfix=htinfix})

fun chain2 (p, q) = Parser.bindFull (fn (rp, ctx) => Parser.map (fn rq => (rp, rq)) q ctx) p
fun chain3 (p, q, r) = Parser.bindFull (fn (rp, ctx) => Parser.bindFull (fn (rq, ctx) => Parser.map (fn rr => (rp, rq, rr)) r ctx) q ctx) p

fun ignoreLeft p q = Parser.bindFull (fn (_, ctx) => q ctx) p
fun ignoreRight p q = Parser.bindFull (fn (res, ctx) => (Parser.map (fn _ => res) q) ctx) p
fun between lp q rp = ignoreRight (ignoreLeft lp q) rp

fun check f p ctx =
    case (p ctx) of
        Ok (ok, ctx) => if f ok
                        then Ok (ok, ctx)
                        else Err ("ERROR in check", ctx)
       | Err err => Err err

fun checkFull f p ctx =
    case (p ctx) of
        Ok (ok, ctx) => if f (ok, ctx)
                        then Ok (ok, ctx)
                        else Err ("ERROR in check", ctx)
       | Err err => Err err

fun chain ps ctx = Parser.mapRes rev
        (foldl (fn (p, acc) =>
                      Result.bind (fn (oks, ctx) =>
                                     Result.map (fn (ok, ctx) =>
                                                    (ok :: oks, ctx))
                                                (p ctx))
                                  acc)
               (Ok ([], ctx)) ps)

fun many p ctx =
    case p ctx of
        Ok (ok, ctx) => (case many p ctx of
                                 Ok (oks, ctx) => Ok (ok :: oks, ctx)
                               | Err (err, _) => Err (err, ctx))
      | Err _ => Ok ([], ctx)

fun some p ctx =
    case p ctx of
        Ok (ok, ctx) => let val resNext = many p ctx
                             in case resNext of
                                    Ok (oks, ctx) => Ok (ok :: oks, ctx)
                                  | Err (err, _) => Ok ([ok], ctx)
                             end
      | Err (err, _) => Err (err, ctx)

fun choose [] ctx = Err (("ERROR in choose with no correct choice"), ctx)
  | choose (p::ps) ctx =
    let val res = p ctx
    in
      if Parser.isOk res
      then res
      else choose ps ctx
    end

fun chooseLong' [] ctx acc = acc
  | chooseLong' (p::ps) ctx (acc as (Ok ok, idx)) =
    (case p ctx of
        res as (Ok (ok, {idx=nidx, ...} : Parser.ctx)) => if nidx > idx then chooseLong' ps ctx (res, nidx) else chooseLong' ps ctx acc
      | Err _ => chooseLong' ps ctx acc)
  | chooseLong' (p::ps) ctx (acc as (Err _, _)) =
    (case p ctx of
        res as (Ok (ok, {idx=idx, ...} : Parser.ctx)) => chooseLong' ps ctx (res, idx)
      | Err _ => chooseLong' ps ctx acc)
fun chooseLong ps ctx = #1 (chooseLong' ps ctx (Err (("ERROR in choose with no correct choice"), ctx), 0))

fun opt default p ctx =
    let val res = p ctx
    in
      if Parser.isOk res
      then res
      else Ok (default, ctx)
    end

datatype con = ConInt of int
              | ConWord of word (* TODO: Currently unused *)
              | ConReal of real (* TODO: Currently unused *)
              | ConChar of char
              | ConString of string

(* TODO: Expand pat, typ, and decl *)
datatype pat = PatCon of con
and typ = TypVar of string
and decl = DeclVal of string list * (bool * pat * exp) list
         | DeclPlaceholder of char
and      exp = ExpCon of con
             | ExpValId of bool * string list
             | ExpApp of exp * exp list
             | ExpInfixApp of exp * string * exp
             | ExpTuple of exp list
             | ExpRecord of (string * exp) list
             | ExpRecordSelect of string
             | ExpList of exp list
             | ExpSeq of exp list
             | ExpLocalDecl of decl * exp list
             | ExpConj of exp * exp
             | ExpDisj of exp * exp
             | ExpTypeAnnote of exp * typ
             | ExpExceptionRaise of exp
             | ExpExceptionHandle of exp * (pat * exp) list
             | ExpCond of exp * exp * exp
             | ExpIter of exp * exp
             | ExpMatch of exp * (pat * exp) list
             | ExpFn of (pat * exp) list

val someSpace = some (choose (map ch [#" ", #"\t", #"\r", #"\n"]))
val space = many (choose (map ch [#" ", #"\t", #"\r", #"\n"]))
fun spacedCh c = between space (ch c) space
val digit = (choose (map ch [#"0", #"1", #"2", #"3", #"4", #"5", #"6", #"7", #"8", #"9"]))
val conHexLetter = Parser.map (fn dig => (Char.ord (Char.toLower dig)) - (Char.ord #"a") + 10) (choose (List.map ch [#"a", #"b", #"c", #"d", #"e", #"f", #"A", #"B", #"C", #"D", #"E", #"F"]))
val conDigit = Parser.map (fn dig => (Char.ord dig) - (Char.ord #"0")) digit
val conNonZeroDigit = Parser.map (fn dig => (Char.ord dig) - (Char.ord #"0")) (choose (map ch [#"1", #"2", #"3", #"4", #"5", #"6", #"7", #"8", #"9"]))
val conHex = ignoreLeft (str "0x") (Parser.map (foldl (fn (num, acc) => acc * 16 + num) 0) (some (choose [conDigit, conHexLetter])))
val conNum = Parser.map (foldl (fn (num, acc) => acc * 10 + num) 0) (some conDigit)
val conNonZeroNum = Parser.map (foldl (fn (num, acc) => acc * 10 + num) 0)
                               (Parser.map List.concat (chain [Parser.map (fn x => [x]) conNonZeroDigit, many conDigit]))
val conInt = Parser.map (fn (neg, num) => ConInt (if neg then ~num else num))
                        (chain2 (opt false (Parser.map (fn _ => true) (ch #"~")), choose [conHex, conNum]))

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
                "}", ",", ":", ";", "...", "_", "|", "=>", "->", "#"]

val coreCon = choose [conInt, conChar, conString]
val coreId = check (fn s => not (List.exists (fn r => (String.compare (s, r)) = EQUAL) reserved))
                   (choose [Parser.map (fn ls => String.implode (List.concat ls))
                                       (chain [Parser.map (fn x => [x]) letter,
                                               many (choose [letter, digit, ch #"_", ch #"'"])]),
                            Parser.map String.implode (some symbolic)])
val coreInfixId = checkFull (fn (s, {htinfix, ...}) => isSome (HashArray.sub (htinfix, s))) coreId
(* TODO: A bit more special than just one/two primes at the start *)
val coreVar = ignoreLeft (ch #"'") (Parser.map (fn ls => String.implode (List.concat ls))
                                (chain [Parser.map (fn x => [x]) letter,
                                        many (choose [letter, digit, ch #"_", ch #"'"])]))
val coreLongId = Parser.map List.concat (chain [Parser.map (fn x => [x]) coreId, many (ignoreLeft (ch #".") coreId)])
val coreLab = choose [coreId, Parser.map Int.toString conNonZeroNum]

fun coreMatch ctx =
    Parser.map List.concat
               (chain [chain [chain2 (ignoreRight corePat (between someSpace (str "=>") someSpace), coreExp)],
                       many (ignoreLeft (spacedCh #"|") (chain2 (ignoreRight corePat (between someSpace (str "=>") someSpace), coreExp)))]) ctx

and corePat ctx = Parser.map PatCon coreCon ctx

and coreTyp ctx = Parser.map TypVar coreVar ctx

and coreDecl ctx = Parser.map DeclPlaceholder (notChs [#"i"]) ctx

and coreATExp ctx =
    choose [Parser.map ExpCon coreCon,
            Parser.map ExpValId
                       (chain2 (opt false (Parser.map (fn _ => true) (chain2 (str "op", someSpace))), coreLongId)),
            between (ch #"(") coreExp (ch #")"),
            Parser.map (fn _ => ExpTuple []) (between (ch #"(") space (ch #")")),
            Parser.map ExpTuple
                       (between (ignoreRight (ch #"(") space)
                                (Parser.map List.concat (chain [chain [coreExp],
                                                                some (ignoreLeft (spacedCh #",") coreExp)]))
                                (ignoreLeft space (ch #")"))),
            Parser.map ExpRecord
                       (between (ignoreRight (ch #"{") space)
                                (Parser.map List.concat (chain [opt [] (chain [chain2 (ignoreRight coreLab (spacedCh #"="), coreExp)]),
                                                                many (ignoreLeft (spacedCh #",") (chain2 (ignoreRight coreLab (spacedCh #"="), coreExp)))]))
                                (ignoreLeft space (ch #"}"))),
            Parser.map ExpRecordSelect (ignoreLeft (spacedCh #"#") coreLab),
            Parser.map ExpList
                       (between (ignoreRight (ch #"[") space)
                                (Parser.map List.concat (chain [opt [] (chain [coreExp]),
                                                                many (ignoreLeft (spacedCh #",") coreExp)]))
                                (ignoreLeft space (ch #"]"))),
            Parser.map ExpSeq
                       (between (ignoreRight (ch #"(") space)
                                (Parser.map List.concat (chain [chain [coreExp],
                                                                some (ignoreLeft (spacedCh #";") coreExp)]))
                                (ignoreLeft space (ch #")"))),
            Parser.map ExpLocalDecl
                       (chain2 (ignoreLeft (ignoreRight (str "let") space) coreDecl,
                               (between (between space (str "in") space)
                                        (Parser.map List.concat (chain [chain [coreExp],
                                                                        many (ignoreLeft (spacedCh #";") coreExp)]))
                                        (ignoreLeft space (str "end")))))]
           ctx

(* TODO: Infix correction required *)
and coreAppExp ctx =
    choose [Parser.map ExpApp
                       (chain2 (coreATExp, some (ignoreLeft someSpace coreATExp))),
            coreATExp]
           ctx

(* TODO: Further work required *)
and coreExp ctx =
    choose [Parser.map ExpTypeAnnote
                       (chain2 (ignoreRight coreAppExp (spacedCh #":"), coreTyp)),
            Parser.map ExpConj
                       (chain2 (coreAppExp, ignoreLeft (between someSpace (str "andalso") someSpace) coreExp)),
            Parser.map ExpDisj
                       (chain2 (coreAppExp, ignoreLeft (between someSpace (str "orelse") someSpace) coreExp)),
            Parser.map ExpExceptionHandle
                       (chain2 (ignoreRight coreAppExp (between someSpace (str "handle") someSpace), coreMatch)),
            Parser.map ExpExceptionRaise (ignoreLeft (ignoreRight (str "raise") someSpace) coreExp),
            Parser.map ExpCond (ignoreLeft (ignoreRight (str "if") someSpace) (chain3 (ignoreRight coreExp (between someSpace (str "then") someSpace), ignoreRight coreExp (between someSpace (str "else") someSpace), coreExp))),
            Parser.map ExpIter (ignoreLeft (ignoreRight (str "while") someSpace) (chain2 (ignoreRight coreExp (between someSpace (str "do") someSpace), coreExp))),
            Parser.map ExpMatch (ignoreLeft (ignoreRight (str "case") someSpace) (chain2 (ignoreRight coreExp (between someSpace (str "of") someSpace), coreMatch))),
            Parser.map ExpFn (ignoreLeft (ignoreRight (str "fn") someSpace) coreMatch),
            coreAppExp]
           ctx
