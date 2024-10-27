(* August 1990, Jussi Rintanen, Helsinki University of Technology *)

(* The tree pattern matching automata builder

  This is the final version of the machine builder of ML-Twig.
  The machine builder takes as input a list of rules, constructs
  a finite state automaton directly from the tree patterns. In the prototype
  version, a string was constructed and returned, but the complexity of
  constructing large strings from small constituent strings by catenating
  them is not very good, so we have a separate function for printing
  the automaton.

*)

signature AUTOMATA =
sig
  exception AutomatonError of string
  structure Parser: PARSER
  val build_automaton: TextIO.outstream * Parser.symbol list * Parser.rule list
                       -> unit
end

(* This is the second version of ML-Twig Automata Builder.
We note, that the first version was purely functional (without side-effects)
and was based on a general structure constructing Aho-Corasick automata
for string matching. However, the first version was considered too complex
and inefficient, and we decided to rewrite it from scratch.
  This revised version constructs a trie, which is represented by an array.
The trie is built directly from tree patterns, and explicit construction
of path strings is avoided.
For detailed description we refer to [Aho,Corasick] and [Hoffmann,O'Donnell].
*)

functor MAKEautomata (structure Parser: PARSER): AUTOMATA =
struct
  exception AutomatonError of string

  fun fatal s = raise AutomatonError s

  (* This structure represents an abstract trie with extensions for
     string pattern matching automaton construction. We have assumed,
     that the implementation has side-effects, and for efficiency
     an array is used. *)

  structure Implementation:
  sig
    structure Parser: PARSER
    datatype alpha = Sym of Parser.symbol | Child of int
    type automaton
    type final = {length: int, ruleno: int, nonterminal: Parser.symbol}
    val empty_automaton: unit -> automaton
    val add_arc: automaton * int * alpha -> automaton * int
    val add_finals: automaton * int * final list -> automaton
    val set_failure: automaton * int * int -> automaton
    val get_failure: automaton * int -> int
    val get_finals: automaton * int -> final list
    val get_transitions: automaton * int -> (alpha * int) list
    val last_state: automaton -> int
  end =
  struct
    structure Parser: PARSER = Parser
    open Parser
    datatype alpha = Sym of symbol | Child of int
    type final = {length: int, ruleno: int, nonterminal: Parser.symbol}
    type state =
      {finals: final list, transitions: (alpha * int) list, failure: int}
    val empty_state: state = {finals = [], transitions = [], failure = 0}
    type automaton = {states: state Array.array, size: int, counter: int}

    fun empty_automaton () =
      {states = Array.array (400, empty_state), size = 400, counter = 1}

    fun add_arc (trie as {states, size, counter}, i, iota) =
      let
        val {finals = finals, transitions = transitions, failure = failure} =
          Array.sub (states, i)
        fun go nil = ~1
          | go ((on, to) :: t) =
              if iota = on then to else go t
        val destination = go transitions
      in
        if destination <> ~1 then
          (trie, destination)
        else if size = counter then
          let
            val newsize = size * 3 div 2
            val newstates: state array = Array.array (newsize, empty_state)
            val rec copya =
              fn 0 => Array.update (newstates, 0, Array.sub (states, 0))
               | n =>
                ( Array.update (newstates, n, Array.sub (states, n))
                ; copya (n - 1)
                )
          in
            copya (size - 1);
            ( {states = newstates, size = newsize, counter = counter + 1}
            , counter
            )
          end
        else
          ( Array.update
              ( states
              , i
              , { finals = finals
                , transitions = (iota, counter) :: transitions
                , failure = failure
                }
              )
          ; ({states = states, size = size, counter = counter + 1}, counter)
          )
      end

    fun set_failure (trie as {states, ...}: automaton, i, failure) =
      let
        val {finals, transitions, ...} = Array.sub (states, i)
      in
        ( Array.update
            ( states
            , i
            , {finals = finals, transitions = transitions, failure = failure}
            )
        ; trie
        )
      end

    fun add_finals (trie as {states, ...}: automaton, i, new_finals) =
      let
        val {finals, transitions, failure} = Array.sub (states, i)
      in
        ( Array.update
            ( states
            , i
            , { finals = new_finals @ finals
              , transitions = transitions
              , failure = failure
              }
            )
        ; trie
        )
      end

    fun get_finals ({states, ...}: automaton, i) =
      #finals (Array.sub (states, i))
    fun get_failure ({states, ...}: automaton, i) =
      #failure (Array.sub (states, i))
    fun get_transitions ({states, ...}: automaton, i) =
      #transitions (Array.sub (states, i))
    fun last_state ({counter, ...}: automaton) = counter - 1

  end

  structure Parser = Parser

  open Implementation Parser

  (* This function traverses a tree pattern and concurrently adds arcs
     to the trie representation of a tree pattern matching automaton. *)

  val rec
    add_pattern:
      automaton * int * Parser.symbol * Parser.tree_pattern * int * int
      -> automaton = fn (autom, rule1, nont, pattern, state, len) =>
    case pattern of
      Leaf (n: Parser.symbol) =>
        let
          val (autom, state) = add_arc (autom, state, Sym n)
        in
          add_finals
            (autom, state, [{length = len, ruleno = rule1, nonterminal = nont}])
        end
    | Tree (n: Parser.symbol, children: Parser.tree_pattern list) =>
        let
          val (autom, state) = add_arc (autom, state, Sym n)
          val (autom, _) =
            List.foldl
              (fn (child_pattern: Parser.tree_pattern, (autom, child_number)) =>
                 let
                   val (autom, state) =
                     add_arc (autom, state, Child child_number)
                 in
                   ( add_pattern
                       (autom, rule1, nont, child_pattern, state, len + 1)
                   , child_number + 1
                   )
                 end) (autom, 1) children
        in
          autom
        end

  (* Steps the automaton with the given alpha (symbol or child). If the transition
     doesn't exist, then it returns -1.
  *)
  fun step_automaton (au: automaton, s: int, i: alpha) : int =
    let
      val transitions: (alpha * int) list = get_transitions (au, s)
      fun go [] = ~1
        | go ((p: alpha, q: int) :: rest) =
            if p = i then q else go rest
    in
      go transitions
    end

  fun oflevel1 (au: automaton) : int list =
    let val transitions: (alpha * int) list = get_transitions (au, 0)
    in map (fn (p, q) => q) transitions
    end

  val construct_failure: automaton -> automaton =
    let
      val rec iterate: automaton * int list * int list -> automaton =
        fn (autom, nil, nil) => autom
         | (autom, nil, next) => iterate (autom, next, nil)
         | (autom, from_root :: rest, next) =>
          let
            val failure: int = get_failure (autom, from_root)
            val transitions: (alpha * int) list =
              get_transitions (autom, from_root)
            val autom: automaton =
              List.foldl
                (fn ((i: alpha, s: int), autom: automaton) =>
                   let
                     val rec fail: int -> int = fn state =>
                       if step_automaton (autom, state, i) <> ~1 then
                         step_automaton (autom, state, i)
                       else if state = 0 then
                         0
                       else
                         fail (get_failure (autom, state))
                   in
                     add_finals
                       ( set_failure (autom, s, fail failure)
                       , s
                       , get_finals (autom, fail failure)
                       )
                   end) autom transitions
          in
            iterate (autom, rest, (map (fn (p, q) => q) transitions) @ next)
          end
    in
      fn autom => iterate (autom, oflevel1 autom, [])
    end

  fun construct_automaton (rules: Parser.rule list) : automaton =
    let
      val trie: automaton = (* Trie & final state values *)
        List.foldl
          (fn ( Rule
                  { ruleno: int
                  , replacement: Parser.symbol
                  , pattern: Parser.tree_pattern
                  , ...
                  }
              , a: automaton
              ) => add_pattern (a, ruleno, replacement, pattern, 0, 1))
          (empty_automaton ()) rules
    in
      construct_failure trie (* Failure & final state values *)
    end

  fun symbol2str (Label s) = "XXX" ^ s
    | symbol2str (Node (s, _)) = s

  fun arc2str (Sym s) = symbol2str s
    | arc2str (Child n) =
        "(ARC " ^ Int.toString n ^ ")"

  fun output_symbols (out: string -> unit, symbols: Parser.symbol list) =
    ( out "datatype symbols = ARC of int"
    ; map (fn s => out (" | " ^ (symbol2str s))) symbols
    ; out "\n"
    )

  fun output_finals' (out: string -> unit, au: automaton, n: int) =
    if n <= last_state au then
      let
        val finals: final list = get_finals (au, n)
        fun outfinal {length: int, ruleno: int, nonterminal: Parser.symbol} =
          ( out "("
          ; out (Int.toString length)
          ; out ","
          ; out (Int.toString ruleno)
          ; out ","
          ; out (symbol2str nonterminal)
          ; out ")"
          )
      in
        out (Int.toString n);
        out " => [";
        case finals of
          nil => ()
        | [h] => outfinal h
        | (h :: t) => (outfinal h; app (fn h => (out ","; outfinal h)) t);
        out "]\n  | ";
        output_finals' (out, au, n + 1)
      end
    else
      ()

  fun output_finals (out: string -> unit, au: automaton) : unit =
    ( out "fun get_finals s =\n"
    ; out "  case s of\n"
    ; output_finals' (out, au, 0)
    ; out "_ => nil\n\n"
    )

  fun output_goto' (out: string -> unit, au: automaton, n: int) : unit =
    if n <= last_state au then
      let
        val transitions: (alpha * int) list = get_transitions (au, n)
      in
        out (Int.toString n);
        out " => (case a of ";
        app
          (fn (i: alpha, s: int) =>
             (out (arc2str i); out " => "; out (Int.toString s); out " | "))
          transitions;
        out " _ => ";
        if n = 0 then (out "0")
        else (out "go ("; out (Int.toString (get_failure (au, n))); out ",a)");
        out ")\n  | ";
        output_goto' (out, au, n + 1)
      end
    else
      ()

  fun output_goto (out: string -> unit, au: automaton) : unit =
    ( out "fun go (s,a) =\n"
    ; out "  case s of\n"
    ; output_goto' (out, au, 0)
    ; out "_ => 0\n\n"
    )

  fun output_automaton
    (outstr: TextIO.outstream, au: automaton, symbols: Parser.symbol list) :
    unit =
    let
      val out = fn s => TextIO.output (outstr, s)
    in
      output_finals (out, au);
      output_goto (out, au);
      out "val go_f = get_finals o go\n";
      out "fun childsymbol s = ARC s\n";
      out "val initialstate = 0\n";
      out "type state = int\n"
    end

  fun build_automaton
    ( outstr: TextIO.outstream
    , symbols: Parser.symbol list
    , rules: Parser.rule list
    ) : unit =
    output_automaton (outstr, construct_automaton rules, symbols)

end
