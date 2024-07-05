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

fun revfold _ [] b = b
  | revfold f (a :: r) b =
      let
        fun f2 (e, [], b) = f (e, b)
          | f2 (e, a :: r, b) =
              f2 (a, r, f (e, b))
      in
        f2 (a, r, b)
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
    val empty_automaton: unit -> automaton
    val add_arc: automaton * int * alpha -> automaton * int
    val add_finals: automaton * int * (int * int * Parser.symbol) list
                    -> automaton
    val set_failure: automaton * int * int -> automaton
    val get_failure: automaton * int -> int
    val get_finals: automaton * int -> (int * int * Parser.symbol) list
    val get_transitions: automaton * int -> (alpha * int) list
    val last_state: automaton -> int
  end =
  struct
    structure Parser: PARSER = Parser
    open Parser
    datatype alpha = Sym of symbol | Child of int
    type state =
      { finals: (int * int * symbol) list
      , transitions: (alpha * int) list
      , failure: int
      }
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

  val int2str: int -> string = Int.toString

  val accum: ('a * 'b -> 'b) -> 'a list -> 'b -> 'b = revfold

  (* This function traverses a tree pattern and concurrently adds arcs
     to the trie representation of a tree pattern matching automaton. *)

  val rec
    add_pattern:
      automaton * int * Parser.symbol * Parser.tree_pattern * int * int
      -> automaton =
    fn (autom, rule1, nont, Leaf n, state, len) =>
      let val (autom', state') = add_arc (autom, state, Sym n)
      in add_finals (autom', state', [(len, rule1, nont)])
      end
     | (autom, rule1, nont, Tree (n, cs), state, len) =>
      let
        val (autom': automaton, state': int) = add_arc (autom, state, Sym n)
        val (autom'''': automaton, _) =
          accum
            (fn (c: Parser.tree_pattern, (autom'': automaton, cn: int)) =>
               let
                 val (autom''': automaton, state'': int) =
                   add_arc (autom'', state', Child cn)
               in
                 ( add_pattern (autom''', rule1, nont, c, state'', len + 1)
                 , cn + 1
                 )
               end) cs (autom', 1)
      in
        autom''''
      end

  fun go (au: automaton, s: int, i: alpha) : int =
    let
      val transitions: (alpha * int) list = get_transitions (au, s)
      val rec go' =
        fn nil => ~1 | ((p: alpha, q: int) :: t) => if p = i then q else go' t
    in
      go' transitions
    end

  fun oflevel1 (au: automaton) : int list =
    let val transitions: (alpha * int) list = get_transitions (au, 0)
    in map (fn (p, q) => q) transitions
    end

  val rec iterate: automaton * int list * int list -> automaton =
    fn (au, nil, nil) => au
     | (au, nil, next) => iterate (au, next, nil)
     | (au, h :: t, next) =>
      let
        val failure: int = get_failure (au, h)
        val transitions: (alpha * int) list = get_transitions (au, h)
        val au': automaton =
          accum
            (fn ((i: alpha, s: int), aut: automaton) =>
               let
                 val rec fail: int -> int = fn state =>
                   if go (aut, state, i) <> ~1 then go (aut, state, i)
                   else if state = 0 then 0
                   else fail (get_failure (aut, state))
               in
                 add_finals
                   ( set_failure (aut, s, fail failure)
                   , s
                   , get_finals (aut, fail failure)
                   )
               end) transitions au
      in
        iterate (au', t, (map (fn (p, q) => q) transitions) @ next)
      end

  fun construct_failure (au: automaton) : automaton =
    iterate (au, oflevel1 au, [])

  fun construct_automaton (rules: Parser.rule list) : automaton =
    let
      val t1 = (* Trie & final state values *)
        accum
          (fn ( Rule (n: int, _, r: Parser.symbol, p: Parser.tree_pattern, _, _)
              , a: automaton
              ) => add_pattern (a, n, r, p, 0, 1)) rules (empty_automaton ())
    in
      construct_failure t1 (* Failure & final state values *)
    end

  fun symbol2str (Label s) = "XXX" ^ s
    | symbol2str (Node (s, _)) = s

  fun arc2str (Sym s) = symbol2str s
    | arc2str (Child n) =
        "(ARC " ^ (int2str n) ^ ")"

  fun output_symbols (out: string -> unit, symbols: Parser.symbol list) =
    ( out "datatype symbols = ARC of int"
    ; map (fn s => out (" | " ^ (symbol2str s))) symbols
    ; out "\n"
    )

  fun output_finals' (out: string -> unit, au: automaton, n: int) =
    if n <= last_state au then
      let
        val finals: (int * int * Parser.symbol) list = get_finals (au, n)
        fun outfinal (i: int, j: int, s: Parser.symbol) =
          ( out "("
          ; out (int2str i)
          ; out ","
          ; out (int2str j)
          ; out ","
          ; out (symbol2str s)
          ; out ")"
          )
      in
        out (int2str n);
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
        out (int2str n);
        out " => (case a of ";
        app
          (fn (i: alpha, s: int) =>
             (out (arc2str i); out " => "; out (int2str s); out " | "))
          transitions;
        out " _ => ";
        if n = 0 then (out "0")
        else (out "go ("; out (int2str (get_failure (au, n))); out ",a)");
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
