(* March 1992, Jussi Rintanen, Helsinki University of Technology *)

functor MAKEmain
  (structure Parser: PARSER
   and Automata: AUTOMATA
   sharing Automata.Parser = Parser):
sig
  val main: string -> unit
end =
struct

  open Parser Automata

  fun count (a, nil) = 0
    | count (a, h :: t) =
        (if a = h then 1 else 0) + count (a, t)

  fun member p = count p <> 0

  (* Output *)

  fun labellist (Leaf (Label l)) = [l]
    | labellist (Tree (_, cs)) =
        List.foldl (fn (c, ac) => ac @ (labellist c)) [] cs
    | labellist _ = []

  fun index (passed, nil) = []
    | index (passed, h :: t) =
        (if member (h, passed) orelse member (h, t) then
           h ^ (Int.toString (count (h, passed) + 1))
         else
           h) :: (index (h :: passed, t))

  fun emitlist' (e, nil) = ()
    | emitlist' (e, [a]) = e a
    | emitlist' (e, h :: t) =
        (e h; e ","; emitlist' (e, t))

  fun emitlist (e, l) =
    (e "["; emitlist' (e, l); e "]")

  fun emitcost (emit, rules, defaultcost) =
    ( emit "fun execute_cost (n:rule, ir, children) =\nlet open User\n"
    ; case defaultcost of
        NoCost => ()
      | Cost code =>
          (emit "val DC = ( "; app emit code; emit ") (map cost children)\n")
    ; emit "val ABORT = (fn () => raise MatchAbort)\n in\ncase n of\n  "
    ; app
        (fn (Rule {ruleno, pattern, cost = Cost ss, ...}) =>
           ( emit (Int.toString ruleno)
           ; emit " => (case map cost children of "
           ; emitlist (emit, index ([], labellist pattern))
           ; emit " => ("
           ; app emit ss
           ; emit ") | _ => raise InternalError \"S4\")\n  | "
           )
          | (Rule {ruleno, cost = NoCost, ...}) =>
           (emit (Int.toString ruleno); emit " => DC\n  | ")) rules
    ; emit "_ => raise InternalError \"S4.3.\"\nend\n\n"
    )

  fun tokens (passed, h :: t) =
        let
          val suffix =
            if member (h, passed) orelse member (h, t) then
              (Int.toString (count (h, passed) + 1))
            else
              ""
        in
          ( "X_" ^ h ^ " " ^ h ^ suffix
          , "execute (nth(children," ^ (Int.toString (length passed)) ^ "))"
          ) :: (tokens (h :: passed, t))
        end
    | tokens _ = []

  fun reftokens ls = tokens ([], ls)

  fun DOtokens (passed, h :: t) =
        let
          val suffix =
            if member (h, passed) orelse member (h, t) then
              (Int.toString (count (h, passed) + 1))
            else
              ""
        in
          ( "DO" ^ h ^ suffix
          , (*	 "let val C = nth(children,"^(Int.toString (length passed))^")in fn () => let val X_"^h^" V = execute C in V end end" *)
            "let val C = nth(children," ^ Int.toString (length passed)
            ^ ")in fn () => case execute C of X_" ^ h
            ^ " V => V | _ => raise InternalError \"S4.3\" end"
          ) :: (DOtokens (h :: passed, t))
        end
    | DOtokens _ = []

  fun DOreftokens ls = DOtokens ([], ls)

  fun emittuple' (e, nil) = ()
    | emittuple' (e, [a]) = e a
    | emittuple' (e, h :: t) =
        (e h; e ","; emittuple' (e, t))

  fun emittuple (e, t) =
    (e "("; emittuple' (e, t); e ")")

  fun emitval (e, l) =
    ( emittuple (e, map (fn (_, a) => a) l)
    ; e " of "
    ; emittuple (e, map (fn (a, _) => a) l)
    )

  fun emitaction (emit, rules) =
    ( emit
        "fun execute (Skeleton (n,_, ir, children)) =\n\
        \ let open User\n"
    ; emit "in\ncase n of\n"
    ; app
        (fn (Rule
               { ruleno
               , ruletype
               , replacement = Label l
               , pattern
               , action = Action ss
               , ...
               }) =>
           let
             val labels = labellist pattern
           in
             emit (Int.toString ruleno);
             emit " => ";
             (case ruletype of
                Ordinary => emit ("X_" ^ l)
              | Topdown => emit ("X_" ^ l)
              | Rewrite => emit "XXXrewrite");
             if labels <> nil then
               ( emit " ( case "
               ; (case ruletype of
                    Ordinary => emitval (emit, reftokens (labellist pattern))
                  | Topdown => emitval (emit, DOreftokens (labellist pattern))
                  | Rewrite => emitval (emit, [("_", "()")]))
               ; emit " => "
               )
             else
               ();
             app emit ss;
             if labels <> nil then
               case ruletype of
                 Ordinary => emit " | _ => raise InternalError \"S5\" )"
               | Topdown => emit " )"
               | Rewrite => emit " )"
             else
               ();
             emit "\n  | "
           end
          | _ => ()) rules
    ; emit "_ => raise Match\n"
    ; emit "end\n\n"
    )

  fun emitrewrite (emit, rules) =
    ( emit
        "fun rewriterule (r:rule) =\n\
        \ case r of\n"
    ; app
        (fn (Rule {ruleno, ruletype = Rewrite, ...}) =>
           (emit (Int.toString ruleno); emit " => true |")
          | _ => ()) rules
    ; emit "_ => false\n"
    )

  (* Symbol datatype declaration *)

  fun symbol2str (Label s) = "XXX" ^ s
    | symbol2str (Node (s, _)) = s

  fun emitsymbols (emit, symbols) =
    let
      val maxarity =
        List.foldl
          (fn (Node (_, a), max) => if a > max then a else max | (_, a) => a) 0
          symbols
    in
      emit "ARC of int";
      map (fn s => emit (" | " ^ (symbol2str s))) symbols;
      emit "\n"
    end

  (* Unit match trees *)

  fun leafs (Leaf _) = 1
    | leafs (Tree (_, cs)) =
        List.foldl (op+) 0 (map leafs cs)

  fun emitmatches (_, nil) = ()
    | emitmatches (emit, (Rule {ruleno, pattern, ...} :: rules)) =
        ( emit "val matchcounts = [\n"
        ; let
            val n =
              ( emit
                  ("(" ^ (Int.toString ruleno) ^ ","
                   ^ (Int.toString (leafs pattern)) ^ ")")
              ; List.foldl
                  (fn (Rule {ruleno, pattern, ...}, m) =>
                     ( emit
                         (",\n(" ^ (Int.toString ruleno) ^ ","
                          ^ (Int.toString (leafs pattern)) ^ ")")
                     ; if ruleno > m then ruleno else m
                     )) ruleno rules
              )
          in
            emit "]\nval matchtable = let val a = Array.array(";
            emit (Int.toString (n + 1));
            emit
              ",0) in ((app (fn(r,m)=>Array.update (a,r,m)) matchcounts); a) end\n\n\
              \fun matches r = Array.sub(matchtable, r)\n\n"
          end
        )

  (* Unit rules *)

  datatype matchtree =
    Chain of int * symbol * matchtree list

  fun closurize unitrules =
    let
      fun member (a, nil) = false
        | member (a, h :: t) =
            a = h orelse member (a, t)
      val initials =
        List.foldl (fn ((_, _, i), a) => if member (i, a) then a else i :: a)
          nil unitrules
      fun build_unittree (nt, visited) =
        List.foldl
          (fn ((r, n, p), ac) =>
             if p = nt andalso not (member (n, visited)) then
               Chain (r, n, build_unittree (n, n :: visited)) :: ac
             else
               ac) nil unitrules
    in
      map (fn i => (i, build_unittree (i, [i]))) initials
    end

  fun emitmatchtreelist (emit, nil) = ()
    | emitmatchtreelist (emit, [m]) = emitmatchtree (emit, m)
    | emitmatchtreelist (emit, (h :: t)) =
        (emitmatchtree (emit, h); emit ","; emitmatchtreelist (emit, t))
  and emitmatchtree (emit, Chain (i, j, ml)) =
    ( emit "Chain ("
    ; emit (Int.toString i)
    ; emit ","
    ; emit (symbol2str j)
    ; emit ",["
    ; emitmatchtreelist (emit, ml)
    ; emit "])"
    )

  fun emitunitrules (emit, matchtrees, symbols) =
    ( emit "datatype matchtree = Chain of int * symbol * matchtree list\n"
    ; emit "fun unitmatches nt = (case nt of\n"
    ; app
        (fn (s, ms) =>
           ( emit (symbol2str s)
           ; emit " => ["
           ; emitmatchtreelist (emit, ms)
           ; emit "]\n  | "
           )) matchtrees
    ; emit "_ => [])\n\n"
    )

  fun partition' (nil, u, n) = (u, n)
    | partition' (Rule {ruleno, replacement, pattern = Leaf s, ...} :: t, u, n) =
        partition' (t, (ruleno, replacement, s) :: u, n)
    | partition' (r :: t, u, n) =
        partition' (t, u, r :: n)

  fun partition l = partition' (l, nil, nil)

  (* Main *)

  fun fatal s =
    TextIO.output (TextIO.stdOut, "Fatal error: " ^ s ^ "\n")

  fun main inputfilename =
    let
      val outputfilename = inputfilename ^ ".sml"
      val (inputf, outputf) =
        (TextIO.openIn inputfilename, TextIO.openOut outputfilename)
      val emit = fn s => TextIO.output (outputf, s)
      val (inserts, rules, dcost, structuren, label_type, symbols) =
        specification inputf
      val (unitrules, otherrules) = partition rules
    in
      emit "structure ";
      emit structuren;
      emit
        " =\n\
        \struct\n\
        \  structure User =\n\
        \  struct\n\
        \datatype symbol =\n";
      emitsymbols (emit, symbols);
      app (fn Prologue ss => (app emit ss) | Insert ss => (app emit ss)) inserts;
      emit "\n\ndatatype result = XXXrewrite of tree | ";
      emit label_type;
      emit
        "\n end\n\n\
        \structure Specification =\n\
        \  struct\n\
        \structure User = User\n\nopen User\n\
        \type rule = int\n\
        \datatype skeletal = Skeleton of (rule * cost * tree * skeletal list)\n\
        \exception MatchAbort\n\
        \fun cost (Skeleton(_,c,_,_)) = c\n\
        \exception InternalError of string\n\n\
        \fun get_subtree (n,t) = nth (get_subtrees t,n-1)\n\n";
      emitcost (emit, rules, dcost);
      emitaction (emit, rules);
      emitmatches (emit, rules);
      build_automaton (outputf, symbols, otherrules);
      emitunitrules (emit, closurize unitrules, symbols);
      emitrewrite (emit, rules);
      emit
        "fun getreplacement (XXXrewrite t) = t | getreplacement _ = raise InternalError \"problem with rewrite 996\"\n\
        \  end\n\
        \structure Internal = MAKEtreeprocessor(Specification)\n\
        \exception NoCover = Internal.NoCover\n\
        \exception InternalError = Internal.InternalError\n\
        \val translate = Internal.translate\n\
        \end;\n";
      TextIO.closeIn inputf;
      TextIO.closeOut outputf
    end
    handle ParserError s => fatal s | AutomatonError s => fatal s

end

structure Parser =
  MAKEparser (structure Symboltable = Symboltable and Lexer = Lexer)

structure Main =
  MAKEmain
    (structure Parser = Parser
     and Automata = MAKEautomata (structure Parser = Parser))

val () = Main.main (List.hd (CommandLine.arguments ()))
