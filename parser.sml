(* This Source Code Form is subject to the terms of the Mozilla Public
   License, v. 2.0. If a copy of the MPL was not distributed with this
   file, You can obtain one at http://mozilla.org/MPL/2.0/. *)
structure Parser = struct
  datatype con = ConInt of int
                | ConWord of word (* TODO: Currently unused *)
                | ConReal of real (* TODO: Currently unused *)
                | ConChar of char
                | ConString of string
  type longid = string list
  datatype pat = PatWildcard
          | PatCon of con
          | PatConstr of bool * longid * pat option
          | PatInfixApp of pat * (string * pat) list
          | PatTuple of pat list
          | PatLayered of bool * string * typ option * pat
          | PatRecord of rec_entry_pat list
          | PatList of pat list
          | PatTypeAnnote of pat * typ
  and rec_entry_pat = PatRecordEntryA of string * pat
                    | PatRecordEntryB of string * typ option * pat option
  and typ = TypVar of string
          | TypConstr of typ list * longid
          | TypFun of typ * typ
          | TypTuple of typ list
          | TypRecord of (string * typ) list
  and decl = DeclVal of string list * (bool * pat * exp) list
           | DeclFun of string list * decl_fun list
           | DeclTyp of (string list * string * typ) list
           | DeclDataTyp of ((string list * string * (string * typ option) list) list) * ((string list * string * typ) list)
           | DeclDataTypRepl of string * longid
           | DeclAbsTyp of ((string list * string * (string * typ option) list) list) * ((string list * string * typ) list) * decl
           | DeclExc of decl_exc list
           | DeclSeq of decl list
           | DeclLocal of decl * decl
           | DeclOpen of longid list
           | DeclNonfix of string list
           | DeclInfix of int option * string list
           (* | DeclStruct of TODO: MODULES *)
           | DeclEmpty
  and decl_fun = DeclFunNonfix of (bool * string * pat list * typ option * exp) list
               | DeclFunInfixOne of (pat * string * pat * typ option * exp) list
               | DeclFunInfixMany of (pat * string * pat * pat list * typ option * exp) list
  and decl_exc = DeclExcGen of string * typ option
               | DeclExcRen of string * longid
  and exp = ExpCon of con
          | ExpValId of bool * longid
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

  datatype ctx = Ctx of {str: string, idx: int,
                         htinfix: int HashArray.hash,
                         httyp: (typ * ctx, string * ctx) result HashArray.hash,
                         htexp: (exp * ctx, string * ctx) result HashArray.hash,
                         htpat: (pat * ctx, string * ctx) result HashArray.hash,
                         htdecl: (decl * ctx, string * ctx) result HashArray.hash}
  type 'a parser = ctx -> ('a * ctx, string * ctx) result

  fun mapRes f (Ok (ok, ctx)) = Ok (f ok, ctx)
    | mapRes f (Err (err, ctx)) = Err (err, ctx)

  fun map f p ctx = mapRes f (p ctx)
  fun mapFull f p ctx = Result.map f (p ctx)

  fun bindFull f p ctx = Result.bind f (p ctx)

  fun isOk (Ok _) = true
    | isOk (Err _) = false

  fun rewriteErr str p ctx =
      case p ctx of
          Ok ok => Ok ok
        | Err (err, ctx) => Err (str, ctx)

  fun memoizeDecl uniq (p : decl parser) (ctx as Ctx {idx, htdecl, ...}) =
      let val uniqid = uniq ^ (Int.toString idx)
      in case HashArray.sub (htdecl, uniqid) of
            SOME x => x
          | NONE => let val res = p ctx in
                        HashArray.update (htdecl, uniqid, res);
                        res
                    end
      end

  fun memoizePat uniq (p : pat parser) (ctx as Ctx {idx, htpat, ...}) =
      let val uniqid = uniq ^ (Int.toString idx)
      in case HashArray.sub (htpat, uniqid) of
            SOME x => x
          | NONE => let val res = p ctx in
                        HashArray.update (htpat, uniqid, res);
                        res
                    end
      end

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
                  httyp=HashArray.hash (String.size str),
                  htpat=HashArray.hash (String.size str),
                  htdecl=HashArray.hash (String.size str)})
      end

  fun const x ctx = Ok (x, ctx)

  datatype waste = Waste
  fun waste x ctx = map (fn _ => Waste) x ctx
  fun constWaste ctx = Ok (Waste, ctx)

  fun ch c (ctx as Ctx {str, idx, htinfix, htexp, httyp, htpat, htdecl}) =
      if idx < (String.size str) andalso String.sub (str, idx) = c
      then Ok (c, Ctx {str=str, idx=idx+1, htinfix=htinfix, htexp=htexp, httyp=httyp, htpat=htpat, htdecl=htdecl})
      else Err ("ERROR in ch with c = " ^ String.str c ^ "\n", ctx)

  fun str s (ctx as Ctx {str, idx, htinfix, htexp, httyp, htpat, htdecl}) =
      if String.size str - idx < String.size s then
        Err (("ERROR in str with s = \"" ^ s ^ "\", s is too large\n"), ctx)
      else let
        val subs = Substring.extract (s, 0, NONE)
        val substr = Substring.substring (str, idx, Substring.size subs)
      in
        if Substring.compare (substr, subs) = EQUAL
        then Ok (substr, Ctx {str=str, idx=idx + Substring.size substr, htinfix=htinfix, htexp=htexp, httyp=httyp, htpat=htpat, htdecl=htdecl})
        else Err ("ERROR in str with s = \"" ^ s ^ "\"\n", ctx)
      end

  fun notChs cs (ctx as Ctx {str, idx, htinfix, htexp, httyp, htpat, htdecl}) =
      if idx < (String.size str) andalso not (List.exists (fn c => c = String.sub (str, idx)) cs)
      then Ok (String.sub (str, idx), Ctx {str=str, idx=idx+1, htinfix=htinfix, htexp=htexp, httyp=httyp, htpat=htpat, htdecl=htdecl})
      else Err ("ERROR in ch with cs = [" ^ (String.concatWith "," (List.map String.str cs)) ^ "]\n", ctx)

  fun eof (ctx as Ctx {str, idx, htinfix, htexp, httyp, htpat, htdecl}) =
      if idx >= (String.size str)
      then constWaste ctx
      else Err ("ERROR in eof: Not EOF\n", ctx)

  fun chain2 (p, q) = bindFull (fn (rp, ctx) => map (fn rq => (rp, rq)) q ctx) p
  fun chain3 (p, q, r) = bindFull (fn (rp, ctx) => bindFull (fn (rq, ctx) => map (fn rr => (rp, rq, rr)) r ctx) q ctx) p
  fun chain4 (p, q, r, s) = bindFull (fn (rp, ctx) => bindFull (fn (rq, ctx) => bindFull (fn (rr, ctx) => map (fn rs => (rp, rq, rr, rs)) s ctx) r ctx) q ctx) p
  fun chain5 (p, q, r, s, t) = bindFull (fn (rp, ctx) => bindFull (fn (rq, ctx) => bindFull (fn (rr, ctx) => bindFull (fn (rs, ctx) => map (fn rt => (rp, rq, rr, rs, rt)) t ctx) s ctx) r ctx) q ctx) p

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
  val coreVar = ignoreLeft (ch #"'") (map (fn ls => String.implode (List.concat ls))
                                  (chain [map (fn x => [x]) letter,
                                          many (choose [letter, digit, ch #"_", ch #"'"])]))
  val coreLongId = map List.concat (chain [map (fn x => [x]) coreId, many (ignoreLeft (ch #".") coreId)])
  val coreLab = choose [coreId, map Int.toString conNonZeroNum]

  val coreNonEqLongId = check (fn [s] => String.compare (s, "=") <> EQUAL
                              | _ => true) coreLongId
  val coreNonEqId = check (fn s => String.compare (s, "=") <> EQUAL) coreId

  fun oneSep core repeat sepcore = map List.concat (chain [chain [core], repeat sepcore])

  fun listBetween left core repeat sep right =
      between (ignoreRight left space)
              (oneSep core repeat (ignoreLeft (spacedCh sep) core))
              (ignoreLeft space right)

  fun listBetweenStr left core repeat sep right =
      between (ignoreRight left space)
              (oneSep core repeat (ignoreLeft (between space (str sep) space) core))
              (ignoreLeft space right)

  fun listSpecial core =
      choose [between (ignoreRight (ch #"(") space)
                      (oneSep core many (ignoreLeft (spacedCh #",") core))
                      (ignoreLeft space (ch #")")),
              chain [core],
              const []]

  fun coreATTyp ctx =
      memoizeTyp "coreATTyp"
      (choose [map TypVar coreVar,
              between (ch #"(") coreTyp (ch #")"),
              map (fn _ => TypRecord []) (between (ch #"{") space (ch #"}")),
              map TypRecord (listBetween (ch #"{") (chain2 (ignoreRight coreLab (spacedCh #":"), coreTyp)) many #"," (ch #"}"))]) ctx
  and coreConstrTyp ctx =
      memoizeTyp "coreConstrTyp"
      (choose [map TypConstr (chain2 (listBetween (ch #"(") coreTyp many #"," (ch #")"), (ignoreLeft space coreLongId))),
              map TypConstr (chain2 (chain [coreATTyp], (ignoreLeft space coreLongId))),
              map TypConstr (chain2 (const [], coreLongId)),
              coreATTyp]) ctx
  and coreTupleTyp ctx =
      memoizeTyp "coreTupleTyp"
      (choose [map TypTuple (oneSep coreConstrTyp some (ignoreLeft (ignoreLeft space (ch #"*")) coreConstrTyp)),
              coreConstrTyp]) ctx
  and coreAppTyp ctx =
      memoizeTyp "coreAppTyp"
      (choose [map TypFun (chain2 (coreTupleTyp, ignoreLeft (between someSpace (str "->") someSpace) coreTyp)),
              coreTupleTyp]) ctx
  and coreTyp ctx = coreAppTyp ctx

  fun coreMatch ctx = oneSep (chain2 (ignoreRight corePat (between someSpace (str "=>") someSpace), coreExp))
                             many
                             (ignoreLeft (spacedCh #"|") (chain2 (ignoreRight corePat (between someSpace (str "=>") someSpace), coreExp))) ctx
  and coreRecordEntryPat ctx =
      choose [map PatRecordEntryA (chain2 (ignoreRight coreLab (spacedCh #"="), corePat)),
             map PatRecordEntryB (chain3 (coreId, opt NONE (map SOME (ignoreLeft (spacedCh #":") coreTyp)), opt NONE (map SOME (ignoreLeft (between space (str "as") space) corePat))))] ctx

  and coreATPat ctx =
      memoizePat "coreATPat"
      (choose [map PatCon coreCon,
              map (fn _ => PatWildcard) (ch #"_"),
              between (ch #"(") corePat (ch #")"),
              map (fn _ => PatTuple []) (between (ch #"(") space (ch #")")),
              map (fn _ => PatRecord []) (between (ch #"{") space (ch #"}")),
              map (fn _ => PatList []) (between (ch #"[") space (ch #"]")),
              map PatTuple (listBetween (ch #"(") corePat some #"," (ch #")")),
              map PatRecord (listBetween (ch #"{") coreRecordEntryPat many #"," (ch #"}")),
              map PatList (listBetween (ch #"[") corePat many #"," (ch #"]"))]) ctx

  and coreConstrPat ctx =
      memoizePat "coreConstrPat"
      (choose [map PatConstr (chain3 (opt false (map (fn _ => true) (chain2 (str "op", someSpace))), coreLongId, ignoreLeft space (map SOME coreATPat))),
              map PatConstr (chain3 (opt false (map (fn _ => true) (chain2 (str "op", someSpace))), coreLongId, const NONE)),
              coreATPat]) ctx

  and coreInfixPat ctx =
      memoizePat "coreInfixPat"
      (choose [map PatInfixApp
                         (chain2 (coreConstrPat, some (chain2 (ignoreLeft space coreId, ignoreLeft space coreConstrPat)))),
              coreConstrPat]) ctx

  and coreTypeAnnotePat ctx =
      memoizePat "coreTypeAnnotePat"
      (choose [map PatTypeAnnote
                         (chain2 (ignoreRight coreInfixPat (spacedCh #":"), coreTyp)),
              coreInfixPat]) ctx

  and corePat ctx =
      memoizePat "corePat"
      (choose [map PatLayered (chain4 (opt false (map (fn _ => true) (ignoreRight (str "op") someSpace)), coreId, opt NONE (map SOME (ignoreLeft (spacedCh #":") coreTyp)), (ignoreLeft (between space (str "as") space) corePat))),
              coreTypeAnnotePat]) ctx

  and coreNonEqConstrPat ctx =
      memoizePat "coreNonEqConstrPat"
      (choose [map PatConstr (chain3 (opt false (map (fn _ => true) (chain2 (str "op", someSpace))), coreNonEqLongId, ignoreLeft space (map SOME coreATPat))),
              map PatConstr (chain3 (opt false (map (fn _ => true) (chain2 (str "op", someSpace))), coreNonEqLongId, const NONE)),
              coreATPat]) ctx

  and coreNonEqInfixPat ctx =
      memoizePat "coreNonEqInfixPat"
      (choose [map PatInfixApp
                         (chain2 (coreNonEqConstrPat, some (chain2 (ignoreLeft space coreNonEqId, ignoreLeft space coreNonEqConstrPat)))),
              coreNonEqConstrPat]) ctx

  and coreNonEqTypeAnnotePat ctx =
      memoizePat "coreNonEqTypeAnnotePat"
      (choose [map PatTypeAnnote
                         (chain2 (ignoreRight coreNonEqInfixPat (spacedCh #":"), coreTyp)),
              coreNonEqInfixPat]) ctx

  and coreNonEqPat ctx =
      memoizePat "coreNonEqPat"
      (choose [map PatLayered (chain4 (opt false (map (fn _ => true) (ignoreRight (str "op") someSpace)), coreId, opt NONE (map SOME (ignoreLeft (spacedCh #":") coreTyp)), (ignoreLeft (between space (str "as") space) coreNonEqPat))),
              coreNonEqTypeAnnotePat]) ctx

  and coreValBind ctx = chain3 (opt false (map (fn _ => true) (ignoreRight (str "rec") someSpace)), coreNonEqPat, ignoreLeft (spacedCh #"=") coreExp) ctx
  and coreFunBindNonFix ctx = (chain5 (opt false (map (fn _ => true) (ignoreRight (str "op") someSpace)),
                                                           coreId,
                                                           some (ignoreLeft space coreNonEqPat),
                                                           opt NONE (map SOME (ignoreLeft (spacedCh #":") coreTyp)),
                                                           ignoreLeft (spacedCh #"=") coreExp)) ctx
  (* TODO: Handle infix functions *)
  and coreFunBind ctx = choose [map DeclFunNonfix (oneSep coreFunBindNonFix many (ignoreLeft (spacedCh #"|") coreFunBindNonFix))] ctx
  and coreTypBind ctx = chain3 (listSpecial coreVar, between space coreId (spacedCh #"="), coreTyp) ctx
  and coreExcBind ctx = choose [map DeclExcRen (chain2 (coreNonEqId, ignoreLeft (spacedCh #"=") coreLongId)),
                                map DeclExcGen (chain2 (coreId, opt NONE (map SOME (ignoreLeft (between space (str "of") space) coreTyp))))] ctx
  and coreConBind ctx = chain2 (coreId, opt NONE (map SOME (ignoreLeft (between space (str "of") space) coreTyp))) ctx
  and coreDataTypBind ctx = chain3 (listSpecial coreVar, between space coreId (spacedCh #"="), (oneSep coreConBind many (ignoreLeft (spacedCh #"|") coreConBind))) ctx

  and coreATDecl ctx =
      memoizeDecl "coreATDecl"
      (choose [map DeclVal (chain2 (ignoreLeft (ignoreRight (str "val") space) (listSpecial coreVar),
                                   ignoreLeft space (listBetweenStr space coreValBind many "and" constWaste))),
              map DeclFun (chain2 (ignoreLeft (ignoreRight (str "fun") space) (listSpecial coreVar),
                                   ignoreLeft space (listBetweenStr space coreFunBind many "and" constWaste))),
              map DeclTyp (ignoreLeft (ignoreRight (str "type") space)
                                      (listBetweenStr space coreTypBind many "and" constWaste)),
              map DeclExc (ignoreLeft (ignoreRight (str "exception") space)
                                      (listBetweenStr space coreExcBind many "and" constWaste)),
              map DeclLocal (chain2 (ignoreLeft (ignoreRight (str "local") space) coreDecl, between (between space (str "in") space) coreDecl (ignoreLeft space (str "end")))),
              map DeclOpen (ignoreLeft (str "open") (some (ignoreLeft space coreLongId))),
              map DeclNonfix (ignoreLeft (str "nonfix") (some (ignoreLeft space coreId))),
              map DeclInfix (ignoreLeft (ignoreRight (str "infixr") space) (chain2 (opt NONE (map (fn x => SOME (~x)) conDigit), (some (ignoreLeft space coreId))))),
              map DeclInfix (ignoreLeft (ignoreRight (str "infix") space) (chain2 (opt NONE (map SOME conDigit), (some (ignoreLeft space coreId))))),
              map DeclDataTypRepl (chain2 (ignoreLeft (ignoreRight (str "datatype") space) coreNonEqId, ignoreLeft (between (spacedCh #"=") (str "datatype") space) coreLongId)),
              map DeclDataTyp (chain2 (ignoreLeft (ignoreRight (str "datatype") space)
                                                  (listBetweenStr space coreDataTypBind many "and" constWaste),
                                       opt [] (ignoreLeft (ignoreLeft space (str "withtype")) (listBetweenStr space coreTypBind many "and" constWaste)))),
              map DeclAbsTyp (chain3 (ignoreLeft (ignoreRight (str "datatype") space)
                                                  (listBetweenStr space coreDataTypBind many "and" constWaste),
                                      opt [] (ignoreLeft (ignoreLeft space (str "withtype")) (listBetweenStr space coreTypBind many "and" constWaste)),
                                      between (between space (str "with") space)
                                              coreDecl
                                              (ignoreLeft space (str "end"))))]) ctx

  and coreDecl ctx =
      memoizeDecl "coreDecl"
      (map DeclSeq (some (ignoreLeft (choose [waste (some (spacedCh #";")), waste space]) coreATDecl))) ctx

  and coreATExp ctx =
      memoizeExp "coreATExp"
      (choose [map ExpCon coreCon,
              map ExpValId (chain2 (opt false (map (fn _ => true) (chain2 (str "op", someSpace))), coreLongId)),
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

