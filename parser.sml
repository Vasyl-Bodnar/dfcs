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
  datatype con = ConInt of int
                | ConWord of word (* TODO: Currently unused *)
                | ConReal of real (* TODO: Currently unused *)
                | ConChar of char
                | ConString of string
  datatype pat = PatCon of con
  and typ = TypVar of string
          | TypConstr of typ list * string list
          | TypFun of typ * typ
          | TypTuple of typ list
          | TypRecord of (string * typ) list
  and decl = DeclVal of string list * (bool * pat * exp) list
           | DeclPlaceholder of char
  and exp = ExpCon of con
          | ExpValId of bool * string list
          | ExpApp of exp list
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

  datatype ctx = Ctx of {str: string, idx: int, htinfix: int HashArray.hash, httyp: (typ * ctx, string * ctx) result HashArray.hash, htexp: (exp * ctx, string * ctx) result HashArray.hash}
  type 'a parser = ctx -> ('a * ctx, string * ctx) result

  fun mapRes f (Ok (ok, ctx)) = Ok (f ok, ctx)
    | mapRes f (Err (err, ctx)) = Err (err, ctx)

  fun map f p ctx = mapRes f (p ctx)
  fun mapFull f p ctx = Result.map f (p ctx)

  fun bindFull f p ctx = Result.bind f (p ctx)

  fun isOk (Ok _) = true
    | isOk (Err _) = false

  fun memoizeTyp uniq (p : typ parser) (ctx as Ctx {idx, httyp, ...}) =
      let val uniqid = uniq ^ (Int.toString idx)
      in case HashArray.sub (httyp, uniqid) of
            SOME x => x
          | NONE => let val res = p ctx in
                        HashArray.update (httyp, uniqid, res);
                        res
                    end
      end

  fun memoizeExp uniq (p : exp parser) (ctx as Ctx {idx, htexp, ...}) =
      let val uniqid = uniq ^ (Int.toString idx)
      in case HashArray.sub (htexp, uniqid) of
            SOME x => x
          | NONE => let val res = p ctx in
                        HashArray.update (htexp, uniqid, res);
                        res
                    end
      end

  fun parse (p : 'a parser) (str : string) =
      let val ht = HashArray.hash 20 in
          app (fn (name, fix) => HashArray.update (ht, name, fix))
              [("*", 7), ("/", 7), ("div", 7), ("mod",7),
               ("+", 6), ("-", 6), ("^", 6), ("::", ~5), ("@", ~5),
               ("=", 4), ("<>", 4), (">", 4), ("<", 4), (">=", 4), ("<=", 4),
               (":=", 3), ("o", 3), ("before", 0)];
          (* NOTE: String.size might be too much in some cases, better heuristic appreciated *)
          p (Ctx {str=str, idx=0,
                  htinfix=ht,
                  htexp=HashArray.hash (String.size str),
                  httyp=HashArray.hash (String.size str)})
      end

  fun ch c (Ctx {str, idx, htinfix, htexp, httyp}) =
      if idx < (String.size str) andalso String.sub (str, idx) = c
      then Ok (c, Ctx {str=str, idx=idx+1, htinfix=htinfix, htexp=htexp, httyp=httyp})
      else Err ("ERROR in ch with c = " ^ String.str c ^ "\n", Ctx {str=str, idx=idx, htinfix=htinfix, htexp=htexp, httyp=httyp})

  fun str s (Ctx {str, idx, htinfix, htexp, httyp}) =
      if String.size str - idx < String.size s then
        Err (("ERROR in str with s = \"" ^ s ^ "\", s is too large\n"), Ctx {str=str, idx=idx, htinfix=htinfix, htexp=htexp, httyp=httyp})
      else let
        val subs = Substring.extract (s, 0, NONE)
        val substr = Substring.substring (str, idx, Substring.size subs)
      in
        if Substring.compare (substr, subs) = EQUAL
        then Ok (substr, Ctx {str=str, idx=idx + Substring.size substr, htinfix=htinfix, htexp=htexp, httyp=httyp})
        else Err ("ERROR in str with s = \"" ^ s ^ "\"\n", Ctx {str=str, idx=idx, htinfix=htinfix, htexp=htexp, httyp=httyp})
      end

  fun notChs cs (ctx as Ctx {str, idx, htinfix, htexp, httyp}) =
      if idx < (String.size str) andalso not (List.exists (fn c => c = String.sub (str, idx)) cs)
      then Ok (String.sub (str, idx), Ctx {str=str, idx=idx+1, htinfix=htinfix, htexp=htexp, httyp=httyp})
      else Err ("ERROR in ch with cs = [" ^ (String.concatWith "," (List.map String.str cs)) ^ "]\n", ctx)

  fun chain2 (p, q) = bindFull (fn (rp, ctx) => map (fn rq => (rp, rq)) q ctx) p
  fun chain3 (p, q, r) = bindFull (fn (rp, ctx) => bindFull (fn (rq, ctx) => map (fn rr => (rp, rq, rr)) r ctx) q ctx) p

  fun ignoreLeft p q = bindFull (fn (_, ctx) => q ctx) p
  fun ignoreRight p q = bindFull (fn (res, ctx) => (map (fn _ => res) q) ctx) p
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

  fun chain ps ctx = mapRes rev
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
        if isOk res
        then res
        else choose ps ctx
      end

  fun chooseLong' [] ctx acc = acc
    | chooseLong' (p::ps) ctx (acc as (Ok ok, idx)) =
      (case p ctx of
          res as (Ok (ok, Ctx {idx=nidx, ...})) => if nidx > idx then chooseLong' ps ctx (res, nidx) else chooseLong' ps ctx acc
        | Err _ => chooseLong' ps ctx acc)
    | chooseLong' (p::ps) ctx (acc as (Err _, _)) =
      (case p ctx of
          res as (Ok (ok, Ctx {idx=idx, ...})) => chooseLong' ps ctx (res, idx)
        | Err _ => chooseLong' ps ctx acc)
  fun chooseLong ps ctx = #1 (chooseLong' ps ctx (Err (("ERROR in choose with no correct choice"), ctx), 0))

  fun opt default p ctx =
      let val res = p ctx
      in
        if isOk res
        then res
        else Ok (default, ctx)
      end

  val someSpace = some (choose (List.map ch [#" ", #"\t", #"\r", #"\n"]))
  val space = many (choose (List.map ch [#" ", #"\t", #"\r", #"\n"]))
  fun spacedCh c = between space (ch c) space
  val digit = (choose (List.map ch [#"0", #"1", #"2", #"3", #"4", #"5", #"6", #"7", #"8", #"9"]))
  val conHexLetter = map (fn dig => (Char.ord (Char.toLower dig)) - (Char.ord #"a") + 10) (choose (List.map ch [#"a", #"b", #"c", #"d", #"e", #"f", #"A", #"B", #"C", #"D", #"E", #"F"]))
  val conDigit = map (fn dig => (Char.ord dig) - (Char.ord #"0")) digit
  val conNonZeroDigit = map (fn dig => (Char.ord dig) - (Char.ord #"0")) (choose (List.map ch [#"1", #"2", #"3", #"4", #"5", #"6", #"7", #"8", #"9"]))
  val conHex = ignoreLeft (str "0x") (map (foldl (fn (num, acc) => acc * 16 + num) 0) (some (choose [conDigit, conHexLetter])))
  val conNum = map (foldl (fn (num, acc) => acc * 10 + num) 0) (some conDigit)
  val conNonZeroNum = map (foldl (fn (num, acc) => acc * 10 + num) 0)
                                 (map List.concat (chain [map (fn x => [x]) conNonZeroDigit, many conDigit]))
  val conInt = map (fn (neg, num) => ConInt (if neg then ~num else num))
                          (chain2 (opt false (map (fn _ => true) (ch #"~")), choose [conHex, conNum]))

  val conAscii =
      choose [ignoreLeft (ch #"\\")
                         (choose [(ch #"\\"), (ch #"\""),
                                  map (fn _ => #"\a") (ch #"a"),
                                  map (fn _ => #"\b") (ch #"b"),
                                  map (fn _ => #"\t") (ch #"t"),
                                  map (fn _ => #"\n") (ch #"n"),
                                  map (fn _ => #"\v") (ch #"v"),
                                  map (fn _ => #"\f") (ch #"f"),
                                  map (fn _ => #"\r") (ch #"r")
                                  (* \^c where c is @-] *)
                                  (* \ddd where d is 0-9 *)
                                  (* \uxxxx where x is 0-F *)
                                  (* \f..f\ where f..f is ignored formatting *)]),
              notChs [#"\""]]
  val conChar = map ConChar (between (ignoreLeft (ch #"#") (ch #"\"")) conAscii (ch #"\""))
  val conString = map (fn list => ConString (String.implode list)) (between (ch #"\"") (many conAscii) (ch #"\""))

  val letter = choose (List.map ch [#"a",#"b",#"c",#"d",#"e",#"f",#"g",#"h",#"i",#"j",#"k",#"l",#"m",#"n",#"o",#"p",#"q",#"r",#"s",#"t",#"u",#"v",#"w",#"x",#"y",#"z",
                               #"A",#"B",#"C",#"D",#"E",#"F",#"G",#"H",#"I",#"J",#"K",#"L",#"M",#"N",#"O",#"P",#"Q",#"R",#"S",#"T",#"U",#"V",#"W",#"X",#"Y",#"Z"])
  val symbolic = choose (List.map ch [#"!",#"%",#"&",#"$",#"#",#"+",#"-",#"/",#":",#"<",#"=",#">",#"?",#"@",#"\\",#"~",#"`",#"^",#"|",#"*"])
  val reserved = ["abstype", "and", "andalso", "as", "case", "datatype", "do", "else", "end",
                  "exception", "fn", "fun", "handle", "if", "in", "infix", "infixr", "let",
                  "local", "nonfix", "of", "op", "open", "orelse", "raise", "rec", "then",
                  "type", "val", "with", "withtype", "while", "(", ")", "[", "]", "{",
                  "}", ",", ":", ";", "...", "_", "|", "=>", "->", "#"]

  val coreCon = choose [conInt, conChar, conString]
  val coreId = check (fn s => not (List.exists (fn r => (String.compare (s, r)) = EQUAL) reserved))
                     (choose [map (fn ls => String.implode (List.concat ls))
                                         (chain [map (fn x => [x]) letter,
                                                 many (choose [letter, digit, ch #"_", ch #"'"])]),
                              map String.implode (some symbolic)])
  val coreInfixId = checkFull (fn (s, Ctx {htinfix, ...}) => isSome (HashArray.sub (htinfix, s))) coreId
  (* TODO: A bit more special than just one/two primes at the start *)
  val coreVar = ignoreLeft (ch #"'") (map (fn ls => String.implode (List.concat ls))
                                  (chain [map (fn x => [x]) letter,
                                          many (choose [letter, digit, ch #"_", ch #"'"])]))
  val coreLongId = map List.concat (chain [map (fn x => [x]) coreId, many (ignoreLeft (ch #".") coreId)])
  val coreLab = choose [coreId, map Int.toString conNonZeroNum]

  fun listBetween left core repeat sep right =
      between (ignoreRight left space)
              (map List.concat (chain [chain [core],
                                              repeat (ignoreLeft (spacedCh sep) core)]))
              (ignoreLeft space right)

  fun coreMatch ctx =
      map List.concat
                 (chain [chain [chain2 (ignoreRight corePat (between someSpace (str "=>") someSpace), coreExp)],
                         many (ignoreLeft (spacedCh #"|") (chain2 (ignoreRight corePat (between someSpace (str "=>") someSpace), coreExp)))]) ctx

  and corePat ctx = map PatCon coreCon ctx

  and coreATTyp ctx =
      memoizeTyp "coreATTyp"
      (choose [map TypVar coreVar,
              map (fn _ => TypRecord []) (between (ch #"{") space (ch #"}")),
              map TypRecord (listBetween (ch #"{") (chain2 (ignoreRight coreLab (spacedCh #":"), coreTyp)) many #"," (ch #"}"))]) ctx
  and coreConstrTyp ctx =
      memoizeTyp "coreConstrTyp"
      (choose [map TypConstr (chain2 ((listBetween (ch #"(") coreTyp many #"," (ch #")")), (ignoreLeft space coreLongId))),
              map TypConstr (chain2 (opt [] (chain [coreATTyp]), (ignoreLeft space coreLongId))),
              coreATTyp]) ctx
  and coreTupleTyp ctx =
      memoizeTyp "coreTupleTyp"
      (choose [map TypTuple
                         (map List.concat (chain [chain [coreConstrTyp], some (ignoreLeft (ignoreLeft space (ch #"*")) coreConstrTyp)])),
              coreConstrTyp]) ctx
  and coreAppTyp ctx =
      memoizeTyp "coreAppTyp"
      (choose [map TypFun
                         (chain2 (coreTupleTyp, ignoreLeft (between someSpace (str "->") someSpace) coreTyp)),
              coreTupleTyp]) ctx
  and coreTyp ctx =
      memoizeTyp "coreTyp"
      (choose [between (ch #"(") coreTyp (ch #")"),
              coreAppTyp]) ctx

  and coreDecl ctx = map DeclPlaceholder (ignoreRight (notChs [#"i"]) someSpace) ctx

  and coreATExp ctx =
      memoizeExp "coreATExp"
      (choose [map ExpCon coreCon,
              map ExpValId
                         (chain2 (opt false (map (fn _ => true) (chain2 (str "op", someSpace))), coreLongId)),
              between (ch #"(") coreExp (ch #")"),
              map (fn _ => ExpTuple []) (between (ch #"(") space (ch #")")),
              map (fn _ => ExpRecord []) (between (ch #"{") space (ch #"}")),
              map (fn _ => ExpList []) (between (ch #"[") space (ch #"]")),
              map ExpTuple (listBetween (ch #"(") coreExp some #"," (ch #")")),
              map ExpRecord (listBetween (ch #"{") (chain2 (ignoreRight coreLab (spacedCh #"="), coreExp)) many #"," (ch #"}")),
              map ExpRecordSelect (ignoreLeft (spacedCh #"#") coreLab),
              map ExpList (listBetween (ch #"[") coreExp many #"," (ch #"]")),
              map ExpSeq (listBetween (ch #"(") coreExp some #";" (ch #")")),
              map ExpLocalDecl
                         (chain2 (ignoreLeft (ignoreRight (str "let") space) coreDecl,
                                  (listBetween (str "in") coreExp many #";" (str "end"))))])
             ctx

  (* TODO: Infix and App correction required *)
  and coreAppExp ctx =
      memoizeExp "coreAppExp"
      (choose [map ExpApp
                         (map List.concat (chain [chain [coreATExp], some (ignoreLeft space coreATExp)])),
              coreATExp]) ctx

  and coreTypeAnnoteExp ctx =
      memoizeExp "coreTypeAnnoteExp"
      (choose [map ExpTypeAnnote
                         (chain2 (ignoreRight coreAppExp (spacedCh #":"), coreTyp)),
              coreAppExp]) ctx

  and coreConjExp ctx =
      memoizeExp "coreConjExp"
      (choose [map ExpConj
                         (chain2 (coreTypeAnnoteExp, ignoreLeft (between someSpace (str "andalso") someSpace) coreExp)),
              coreTypeAnnoteExp]) ctx

  and coreDisjExp ctx =
      memoizeExp "coreDisjExp"
      (choose [map ExpDisj
                         (chain2 (coreConjExp, ignoreLeft (between someSpace (str "orelse") someSpace) coreExp)),
              coreConjExp]) ctx

  and coreExp ctx =
      memoizeExp "coreExp"
      (choose [map ExpExceptionHandle
                         (chain2 (ignoreRight coreDisjExp (between someSpace (str "handle") someSpace), coreMatch)),
              coreDisjExp,
              map ExpExceptionRaise (ignoreLeft (ignoreRight (str "raise") someSpace) coreExp),
              map ExpCond (ignoreLeft (ignoreRight (str "if") someSpace) (chain3 (ignoreRight coreExp (between someSpace (str "then") someSpace), ignoreRight coreExp (between someSpace (str "else") someSpace), coreExp))),
              map ExpIter (ignoreLeft (ignoreRight (str "while") someSpace) (chain2 (ignoreRight coreExp (between someSpace (str "do") someSpace), coreExp))),
              map ExpMatch (ignoreLeft (ignoreRight (str "case") someSpace) (chain2 (ignoreRight coreExp (between someSpace (str "of") someSpace), coreMatch))),
              map ExpFn (ignoreLeft (ignoreRight (str "fn") someSpace) coreMatch)]) ctx
end

