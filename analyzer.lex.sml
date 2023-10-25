structure TwigLexer=
   struct
    structure UserDeclarations =
      struct

(* November 1988, Jussi Rintanen, Helsinki University of Technology *)

(* This is the specification of ML-Twig lexical analyzer.

   This lexer correctly recognizes all Standard ML tokens, as specified
   in [Harper, MacQueen and Milner, 1986].
*)

datatype lexresult =
      IDENTIFIER of string
      | INT of string
      | EQ
      | RPAREN
      | LPAREN
      | COLON
      | SEMICOLON
      | COMMA
      | TREEREF of int list
      | OTHER of string
      | SPACE of string
      | EOF

fun inc r = r := !r + 1
fun dec r = r := !r - 1

fun revfold _ [] b = b
  | revfold f (a::r) b =
	let fun f2(e,[],b) = f(e,b)
	      | f2(e,a::r,b) = f2(a,r,f(e,b))
	in f2(a,r,b)
  end

local
  fun digit c = (#"0" <= c) andalso (c <= #"9")
  fun str2 (a,c::r) =
    if digit c
      then str2 (a*10 + ord c - ord #"0" ,r)
    else (a,c::r)
    | str2 r = r
in
  fun str0int s = str2 (0,s)
end

local
  fun parse_treeref' nil = nil
    | parse_treeref' [#"$"] = nil
    | parse_treeref' s =
      let val (i,r) = str0int s
      in
	i :: parse_treeref' (tl r)
      end
in
  val parse_treeref = (parse_treeref' o tl o explode)
end

val current_line_number : int ref = ref 1
val commentlevel : int ref = ref 0

fun current_line () = !current_line_number

fun eof() = EOF

end (* end of user routines *)
exception LexError (* raised if illegal leaf action tried *)
structure Internal =
	struct

datatype yyfinstate = N of int
type statedata = {fin : yyfinstate list, trans: string}
(* transition & final state table *)
val tab = let
val s0 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s1 =
"\000\000\000\000\000\000\000\000\000\049\050\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\049\005\042\040\034\005\005\033\031\030\005\005\029\005\026\005\
\\020\020\020\020\020\020\020\020\020\020\005\019\005\005\005\005\
\\005\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\018\005\017\005\016\
\\000\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\014\005\014\005\000\
\\000"
val s3 =
"\051\051\051\051\051\051\051\051\051\051\059\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\057\051\054\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051"
val s5 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\005\000\005\005\005\005\005\000\000\005\005\000\005\006\005\
\\000\000\000\000\000\000\000\000\000\000\005\000\005\005\005\005\
\\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\005\000\005\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\005\000\005\000\
\\000"
val s6 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\007\000\007\007\007\007\013\000\000\007\007\000\007\000\007\
\\000\000\000\000\000\000\000\000\000\000\007\000\007\007\007\007\
\\007\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\000\007\000\007\012\
\\000\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\000\007\000\007\000\
\\000"
val s7 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\007\000\007\007\007\007\007\000\000\007\007\000\007\008\007\
\\000\000\000\000\000\000\000\000\000\000\007\000\007\007\007\007\
\\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\007\000\007\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\007\000\007\000\
\\000"
val s8 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\009\000\009\009\009\009\011\000\000\009\009\000\009\000\009\
\\000\000\000\000\000\000\000\000\000\000\009\000\009\009\009\009\
\\009\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\009\000\009\010\
\\000\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\009\000\009\000\
\\000"
val s9 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\009\000\009\009\009\009\009\000\000\009\009\000\009\008\009\
\\000\000\000\000\000\000\000\000\000\000\009\000\009\009\009\009\
\\009\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\009\000\009\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\009\000\009\000\
\\000"
val s10 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\010\000\000\000\000\000\000\008\000\
\\010\010\010\010\010\010\010\010\010\010\000\000\000\000\000\000\
\\000\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\000\000\000\010\
\\000\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\000\000\000\000\
\\000"
val s11 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\009\000\009\009\009\009\011\000\000\009\009\000\009\008\009\
\\010\010\010\010\010\010\010\010\010\010\009\000\009\009\009\009\
\\009\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\009\000\009\010\
\\000\010\010\010\010\010\010\010\010\010\010\010\010\010\010\010\
\\010\010\010\010\010\010\010\010\010\010\010\000\009\000\009\000\
\\000"
val s12 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\012\000\000\000\000\000\000\008\000\
\\012\012\012\012\012\012\012\012\012\012\000\000\000\000\000\000\
\\000\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\000\000\000\000\012\
\\000\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\000\000\000\000\000\
\\000"
val s13 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\007\000\007\007\007\007\013\000\000\007\007\000\007\008\007\
\\012\012\012\012\012\012\012\012\012\012\007\000\007\007\007\007\
\\007\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\000\007\000\007\012\
\\000\012\012\012\012\012\012\012\012\012\012\012\012\012\012\012\
\\012\012\012\012\012\012\012\012\012\012\012\000\007\000\007\000\
\\000"
val s15 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\015\000\000\000\000\000\000\006\000\
\\015\015\015\015\015\015\015\015\015\015\000\000\000\000\000\000\
\\000\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\000\000\000\000\015\
\\000\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\000\000\000\000\000\
\\000"
val s20 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\024\000\
\\020\020\020\020\020\020\020\020\020\020\000\000\000\000\000\000\
\\000\000\000\000\000\021\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s21 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\023\023\023\023\023\023\023\023\023\023\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\022\000\
\\000"
val s22 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\023\023\023\023\023\023\023\023\023\023\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s24 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\025\025\025\025\025\025\025\025\025\025\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s25 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\025\025\025\025\025\025\025\025\025\025\000\000\000\000\000\000\
\\000\000\000\000\000\021\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s26 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\027\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s27 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\028\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s31 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\032\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s33 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\005\000\005\005\005\005\033\000\000\005\005\000\005\006\005\
\\015\015\015\015\015\015\015\015\015\015\005\000\005\005\005\005\
\\005\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\000\005\000\005\015\
\\000\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\000\005\000\005\000\
\\000"
val s34 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\005\000\005\039\005\005\005\000\000\005\005\000\005\006\005\
\\035\035\035\035\035\035\035\035\035\035\005\000\005\005\005\005\
\\005\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\005\000\005\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\005\000\005\000\
\\000"
val s35 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\038\000\000\000\000\000\000\000\000\000\036\000\
\\035\035\035\035\035\035\035\035\035\035\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s36 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\037\037\037\037\037\037\037\037\037\037\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s37 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\038\000\000\000\000\000\000\000\000\000\036\000\
\\037\037\037\037\037\037\037\037\037\037\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s40 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\041\041\041\041\041\041\041\041\041\041\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s42 =
"\042\042\042\042\042\042\042\042\042\042\000\042\042\042\042\042\
\\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\
\\042\042\048\042\042\042\042\042\042\042\042\042\042\042\042\042\
\\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\
\\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\
\\042\042\042\042\042\042\042\042\042\042\042\042\043\042\042\042\
\\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\
\\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\
\\042"
val s43 =
"\000\000\000\000\000\000\000\000\000\047\047\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\047\000\042\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\045\045\045\045\045\045\045\045\045\045\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\042\000\044\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\042\000\
\\000\000\000\000\042\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s44 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\
\\042\042\042\042\042\042\042\042\042\042\042\000\000\000\000\000\
\\000\042\042\042\042\042\042\042\042\042\042\042\042\042\042\042\
\\042\042\042\042\042\042\042\042\042\042\042\000\000\000\000\000\
\\000"
val s45 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s46 =
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\042\042\042\042\042\042\042\042\042\042\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s47 =
"\000\000\000\000\000\000\000\000\000\047\047\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\047\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\042\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s49 =
"\000\000\000\000\000\000\000\000\000\049\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\049\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
val s51 =
"\051\051\051\051\051\051\051\051\051\051\000\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\053\051\052\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051"
val s52 =
"\051\051\051\051\051\051\051\051\051\051\000\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\000\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051"
val s53 =
"\051\051\051\051\051\051\051\051\051\051\000\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\000\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051"
val s54 =
"\051\051\051\051\051\051\051\051\051\051\056\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\055\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051"
val s57 =
"\051\051\051\051\051\051\051\051\051\051\000\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\058\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\051\
\\051"
in Vector.fromList
[{fin = [], trans = s0},
{fin = [], trans = s1},
{fin = [], trans = s1},
{fin = [], trans = s3},
{fin = [], trans = s3},
{fin = [(N 23)], trans = s5},
{fin = [], trans = s6},
{fin = [(N 41)], trans = s7},
{fin = [], trans = s8},
{fin = [(N 41)], trans = s9},
{fin = [(N 41)], trans = s10},
{fin = [(N 41)], trans = s11},
{fin = [(N 41)], trans = s12},
{fin = [(N 41)], trans = s13},
{fin = [(N 79)], trans = s0},
{fin = [(N 26)], trans = s15},
{fin = [(N 26),(N 79)], trans = s15},
{fin = [(N 51)], trans = s0},
{fin = [(N 53)], trans = s0},
{fin = [(N 47)], trans = s0},
{fin = [(N 10),(N 20)], trans = s20},
{fin = [], trans = s21},
{fin = [], trans = s22},
{fin = [(N 20)], trans = s22},
{fin = [], trans = s24},
{fin = [(N 20)], trans = s25},
{fin = [], trans = s26},
{fin = [], trans = s27},
{fin = [(N 57)], trans = s0},
{fin = [(N 49)], trans = s0},
{fin = [(N 45)], trans = s0},
{fin = [(N 43)], trans = s31},
{fin = [(N 87)], trans = s0},
{fin = [(N 23),(N 26)], trans = s33},
{fin = [(N 23)], trans = s34},
{fin = [], trans = s35},
{fin = [], trans = s36},
{fin = [], trans = s37},
{fin = [(N 7)], trans = s0},
{fin = [(N 7),(N 23)], trans = s5},
{fin = [], trans = s40},
{fin = [(N 61)], trans = s40},
{fin = [], trans = s42},
{fin = [], trans = s43},
{fin = [], trans = s44},
{fin = [], trans = s45},
{fin = [], trans = s46},
{fin = [], trans = s47},
{fin = [(N 75)], trans = s0},
{fin = [(N 82)], trans = s49},
{fin = [(N 84)], trans = s0},
{fin = [(N 109)], trans = s51},
{fin = [], trans = s52},
{fin = [], trans = s53},
{fin = [], trans = s54},
{fin = [(N 93)], trans = s0},
{fin = [(N 98)], trans = s0},
{fin = [], trans = s57},
{fin = [(N 90)], trans = s0},
{fin = [(N 95)], trans = s0}]
end
structure StartStates =
	struct
	datatype yystartstate = STARTSTATE of int

(* start state definitions *)

val C = STARTSTATE 3
val INITIAL = STARTSTATE 1

end
type result = UserDeclarations.lexresult
	exception LexerError (* raised if illegal leaf action tried *)
end

fun makeLexer yyinput =
let
	val yyb = ref "\n" 		(* buffer *)
	val yybl = ref 1		(*buffer length *)
	val yybufpos = ref 1		(* location of next character to use *)
	val yygone = ref 1		(* position in file of beginning of buffer *)
	val yydone = ref false		(* eof found yet? *)
	val yybegin = ref 1		(*Current 'start state' for lexer *)

	val YYBEGIN = fn (Internal.StartStates.STARTSTATE x) =>
		 yybegin := x

fun lex () : Internal.result =
let fun continue() = lex() in
  let fun scan (s,AcceptingLeaves : Internal.yyfinstate list list,l,i0) =
	let fun action (i,nil) = raise LexError
	| action (i,nil::l) = action (i-1,l)
	| action (i,(node::acts)::l) =
		case node of
		    Internal.N yyk =>
			(let val yytext = substring(!yyb,i0,i-i0)
			     val yypos = i0+ !yygone
			open UserDeclarations Internal.StartStates
 in (yybufpos := i; case yyk of

			(* Application actions *)

  10 => (INT yytext)
| 109 => ( SPACE yytext )
| 20 => (OTHER yytext)
| 23 => (case yytext of
      	      	      	  ":" => COLON
      	      	      	  | "=" => EQ
      	      	      	  | _ => OTHER yytext)
| 26 => (IDENTIFIER yytext)
| 41 => (OTHER yytext)
| 43 => (LPAREN)
| 45 => (RPAREN)
| 47 => (SEMICOLON)
| 49 => (COMMA)
| 51 => (OTHER yytext)
| 53 => (OTHER yytext)
| 57 => (OTHER yytext)
| 61 => (OTHER yytext)
| 7 => (TREEREF (parse_treeref yytext))
| 75 => (let val dummy = (current_line_number :=
		      List.foldl (fn (a,b) => b+(if a = #"\n" then 1 else 0))
		      (!current_line_number) (explode yytext))
	in
	  OTHER yytext
	end)
| 79 => (OTHER yytext)
| 82 => (SPACE yytext)
| 84 => ( inc current_line_number; SPACE yytext)
| 87 => ( YYBEGIN C; inc commentlevel; SPACE yytext )
| 90 => ( inc commentlevel; SPACE yytext )
| 93 => ( dec commentlevel; if !commentlevel = 0 then YYBEGIN INITIAL else (); SPACE yytext )
| 95 => ( inc current_line_number; SPACE yytext )
| 98 => ( inc current_line_number; SPACE yytext )
| _ => raise Internal.LexerError

		) end )

	val {fin,trans} = Vector.sub(Internal.tab, s)
	val NewAcceptingLeaves = fin::AcceptingLeaves
	in if l = !yybl then
	     if trans = #trans(Vector.sub(Internal.tab,0))
	       then action(l,NewAcceptingLeaves
) else	    let val newchars= if !yydone then "" else yyinput 1024
	    in if (size newchars)=0
		  then (yydone := true;
		        if (l=i0) then UserDeclarations.eof ()
		                  else action(l,NewAcceptingLeaves))
		  else (if i0=l then yyb := newchars
		     else yyb := substring(!yyb,i0,l-i0)^newchars;
		     yygone := !yygone+i0;
		     yybl := size (!yyb);
		     scan (s,AcceptingLeaves,l-i0,0))
	    end
	  else let val NewChar = ord (String.sub (!yyb,l))
		val NewState = ord (if NewChar<128 then String.sub (trans,NewChar) else String.sub(trans,128))
		in if NewState=0 then action(l,NewAcceptingLeaves)
		else scan(NewState,NewAcceptingLeaves,l+1,i0)
	end
	end
(*
	val start= if substring(!yyb,!yybufpos-1,1)="\n"
then !yybegin+1 else !yybegin
*)
	in scan(!yybegin (* start *),nil,!yybufpos,!yybufpos)
    end
end
  in lex
  end
end
