structure Vaxcg =
struct
  structure User =
  struct
datatype symbol =
ARC of int | XXXresult | XXXzero | XXXargs | XXXname | XXXcvtopu | XXXcvtop | XXXrelop | XXXunop | XXXbinop | XXXbigval | XXXflag | XXXntest | XXXtest | XXXcomputation | XXXdestination | XXXioperand | XXXlocation | XXXoperand | XXXreg | XXXstm | XXXbody | RETURN | CVTFF | CVTFS | CVTUS | CVTUU | CVTSF | CVTSS | CVTSU | FNEG | COMP | NEG | FGEQ | FGT | FLEQ | FLT | FNEQ | FEQ | UGEQ | UGT | ULEQ | ULT | GEQ | GT | LEQ | LT | NEQ | EQ | XOR | RSHIFT | LSHIFT | OR | AND | MOD | DIV | MUL | MINUS | PLUS | FDIV | FMUL | FMINUS | FPLUS | NOARGS | ARG | NOT | CAND | CALL | TEMP | ALLOC | CONSTF | CONST | NAME | BOOL | ESEQ | MOVE | MEM | UNOP | OP | CJUMP | JUMP | LABEL | SEQ | PROC


  exception CodeGeneration of string

  fun fatal s = raise CodeGeneration s

  fun int2str (i:int) = if i<0 then ("-"^(makestring (0-i))) else makestring i

  val next_label = ref 0
  fun newLabel () = (inc next_label; "_Label" ^ (int2str (!next_label - 1)))

(* Tree functions *)

(* Registers *)

  structure Registers :
    sig
      type Reg
      val reg2str : Reg -> string
      val resultReg : unit -> Reg
      val FPregister : Reg
      val APregister : Reg
      val regmask : unit -> int
      val decreaseusage : Reg -> unit
      val increaseusage : Reg -> unit
      val usage : Reg -> int
      val allocate : unit -> Reg
      val calling : unit -> unit
      val initialize_registers : unit -> unit
    end
  =
  struct
    datatype extension = Ext of { name: string, usage: int ref, modif: bool ref }
    type Reg = extension ref

    fun reg2str (ref (Ext { name = s, ...})) = s

    val registers =
      [Ext {name="r1",usage= ref 0, modif = ref false},
       Ext {name="r2",usage= ref 0, modif = ref false},
       Ext {name="r3",usage= ref 0, modif = ref false},
       Ext {name="r4",usage= ref 0, modif = ref false},
       Ext {name="r5",usage= ref 0, modif = ref false},
       Ext {name="r6",usage= ref 0, modif = ref false},
       Ext {name="r7",usage= ref 0, modif = ref false},
       Ext {name="r8",usage= ref 0, modif = ref false},
       Ext {name="r9",usage= ref 0, modif = ref false},
       Ext {name="r10",usage= ref 0, modif = ref false},
       Ext {name="r11",usage= ref 0, modif = ref false},
       Ext {name="r12",usage= ref 0, modif = ref false}]

    val R0register = Ext {name="r0",usage= ref 0, modif = ref false}
    val FPregister = ref (Ext {name="fp",usage= ref 1, modif = ref false})
    val APregister = ref (Ext {name="ap",usage= ref 1, modif = ref false})
    val SPregister = ref (Ext {name="r15",usage= ref 1, modif = ref false})

    fun choose ((r as Ext {usage = ru as (ref 0), modif = m,...})::_) =
	(m := true; ru := 1; r)
      | choose (h::t) = choose t
      | choose nil = fatal "run out of registers"

    fun allocate () = ref (choose registers)
    fun decreaseusage (ref (Ext{ usage = u, ... })) = dec u
    fun increaseusage (ref (Ext{ usage = u, ... })) = inc u
    fun usage (ref (Ext{ usage = ref u, ... })) = u

    datatype rsr = UNUSED | REFERS of Reg

    val rsr = ref UNUSED

    fun resultReg () =
      let val newreg = ref R0register
      in
	( rsr := REFERS newreg;
	  newreg )
      end

    fun calling () =
      (case !rsr of
	UNUSED => ()
      | REFERS r =>
	  let val Ext { usage=u, ... } = R0register
	  in
	    if !u <> 0
	      then
		let val newreg as Ext {name=s,...} = choose registers
		in
		  (output (std_out,"mov\tr0,"^s^"\n");
		   r := newreg;
		   u := 0)
		end
	    else ()
	  end)

    fun initialize_registers' ((Ext{usage=u,modif=m,...})::rest) =
	(u:=0;m:=false;initialize_registers' rest;rsr:=UNUSED)
      | initialize_registers' _ = ()

    fun initialize_registers () = initialize_registers' registers

    fun calcula ((Ext{modif=ref true,...})::t,n,ac:int) = calcula (t,n+n,ac+n)
      | calcula ((Ext{modif=ref false,...})::t,n,ac) = calcula (t,n+n,ac)
      | calcula (_,_,ac:int) = ac

    fun regmask() = calcula (registers, 2, 0)

  end

  open Registers


  datatype sizecodefun = nofun
    | unaryfun of (int -> string)
    | binaryfun of ((int -> string) * (int -> string))

  datatype Kind = Op of symbol | numbered of int | none

  datatype reg = register of Reg | ghostregister of Reg | noreg

  type support = { regre: reg ref,
		  kind: Kind ref,
		  truebranch : string ref,
		  sizcod : sizecodefun ref }

  fun initialized_support () = { regre = ref noreg,
				kind = ref none,
				truebranch = ref "",
				sizcod = ref nofun }

  datatype attribute = proclabel of string | label of string |
    ivalue of int | temp of Reg | size of int

  datatype tree = tree of (symbol * tree list * attribute list * support)

  fun givereg (tree(_,_,_,{regre = rr as ref (register r),...})) =
      (decreaseusage r;
       if (usage r) = 0
	 then rr := ghostregister r
       else ())
    | givereg _ = fatal "does not have"

  fun get_reg (tree(_,_,_,{regre = ref (register r),...})) = r
    | get_reg (tree(_,_,_,{regre = ref (ghostregister r),...})) = r
    | get_reg _ = fatal "have not"

  fun set_reg (t as tree(_,_,_,{regre = rr as ref (register r),...}),s) =
    (rr := register s; increaseusage s)
    | set_reg (tree(_,_,_,{regre = r,...}),s) =
      (r := register s; increaseusage s)

  fun getreg (tree(_,_,_,{regre = rr as ref (register r),...})) = rr := register (allocate())
    | getreg (tree(_,_,_,{regre = r,...})) = r := register (allocate())


  fun node_value (tree(v,_,_,_)) = v
  fun get_subtrees (tree(_,t,_,_)) = t

  fun map2 f ([],[]) = []
    | map2 f (h :: t, i :: u) = f(h,i) :: (map2 f (t,u))
    | map2 f _ = fatal "map2 failure"

  fun equal (tree(i,s1,a1,_), tree(j,s2,a2,_)) =
    (i = j) andalso (a1 = a2) andalso (length s1 = length s2)
     andalso (List.foldl (fn (a,b) => a andalso b) true (map2 equal (s1,s2)))

  fun count_arguments (tree(ARG,[_,t],_,_)) = 1+(count_arguments t)
    | count_arguments _ = 0

  val get_op = node_value

  fun child0 (tree(_,h :: _,_,_)) = h
    | child0 _ = fatal "no child 0"

  fun child1 (tree(_,_ :: h :: _,_,_)) = h
    | child1 _ = fatal "no child 1"

  fun child2 (tree(_,_ :: _ :: h :: _,_,_)) = h
    | child2 _ = fatal "no child 2"

  fun get_kind (tree(_,_,_,{ kind = ref ir, ... })) = ir

  fun get_truebranch (tree(_,_,_,{ truebranch = ref l, ... })) = l

  fun attrLabel (label l :: _) = l
    | attrLabel (_ :: t) = attrLabel t
    | attrLabel nil = fatal "no attribute label"

  fun attrSize (size i :: _) = i
    | attrSize (_ :: t) = attrSize t
    | attrSize nil = fatal "no attribute size"

  fun attrIvalue (ivalue i :: _) = i
    | attrIvalue (_ :: t) = attrIvalue t
    | attrIvalue nil = fatal "no attribute ivalue"

  fun attrProclabel (proclabel l :: _) = l
    | attrProclabel (_ :: t) = attrProclabel t
    | attrProclabel nil = fatal "no attribute proclabel"

  fun attrTemp (temp t :: _) = t
    | attrTemp (_ :: t) = attrTemp t
    | attrTemp nil = fatal "no attribute temp"

  fun pickAttrs (tree(_,_,a,_)) = a

  val get_label = (attrLabel o pickAttrs)
  val get_size = (attrSize o pickAttrs)
  val get_ivalue = (attrIvalue o pickAttrs)
  val get_proclabel = (attrProclabel o pickAttrs)

  val get_temp = (attrTemp o pickAttrs)

  fun set_kind_n (tree(_,_,_,{ kind = ir, ... }), n) = ir := numbered n
  fun set_kind (tree(_,_,_,{ kind = ir, ... }), ope) = ir := Op ope

  fun set_truebranch (tree(_,_,_,{ truebranch = lr, ... }), l) = lr := l

  fun get_sizecode (tree(_,_,_,{ sizcod = ref (unaryfun f), ...})) = f
    | get_sizecode _ = fatal "no attribute sizcod = ref unaryfun"

  fun get_sizecodecvt (tree(_,_,_,{ sizcod=ref(binaryfun f),...})) = f
    | get_sizecodecvt _ = fatal "no attribute sizcod = ref binaryfun"

  fun set_sizecode (tree(_,_,_,{sizcod = r,...}), s) = r := unaryfun s

  fun set_sizecodecvt (tree(_,_,_,{sizcod = r,...}),s1,s2) =
    r := binaryfun (s1,s2)

(*
 The fields of cost

 int	space
 int	time
 bool	setFlags: true, if the instruction sets condition code flags
 bool	sideEffect: true, if the instruction causes sideeffects. This
	is required, if the computations of the subtrees are reordered
	for minimal register usage (Sethi-Ullman).
 bool	dontDestroy: true, if the register allocated for the node may
	not be destroyed. eg. the register is a temporary
 int	hold: number of registers for holding the value of the node
 int	maxregs: number of registers needed sometime  during the computation
	of the tree
 bool	dontEval: true, if ???
 int	isize: ???
*)

  type cost = (int * int * bool * bool * bool * int * int * bool ref * int)

  (* space * time * setFlags * sideEffect * dontDestroy * hold *
   maxregs * dontEval * isize *)

  val zerocost:cost = (0,0,false,false,false,0,0,ref false,0)

  val get_sideEffect = (fn (_,_,_,e,_,_,_,_,_) => e)

  fun cost_plus ((s,t,f,e,d,m,h,v,i):cost,(s2,t2,f2,e2,d2,m2,h2,v2,i2)) =
    (s+s2,t+t2,false,f orelse f2,false,0,0,ref false,0)

  fun sum_costs [] = zerocost
  | sum_costs (h :: t) = List.foldl (fn (a,b) => cost_plus (a,b)) h t

  fun cost_less ((s1,t1,_,_,_,_,_,_,_):cost, (s2,t2,_,_,_,_,_,_,_):cost) =
    (s1+t1) < (s2+t2)

  fun C (s,t,f,e,d,m) = (s,t,f,e,d,m,0,ref false,0)

    (* space * time * setFlags * sideEffect * dontDestroy * maxregs *)

  fun WD ((S,T,F,E,D,M,H,V,I):cost,s,t,f,e,d,m) =
    (S+s,T+t,false,f orelse F,false,0,0,ref false,0)

  fun WDH1 ((S,T,F,E,D,M,H,V,I):cost,s,t,f,e,d,m) =
    (S+s,T+t,false,f orelse F,false,0,1,ref false,0)

  fun WDHA ((S,T,F,E,D,M,H,V,I):cost,s,t,f,e,d,m) =
    (S+s,T+t,false,f orelse F,false,0,0,ref false,0)

  fun WDHAs ((S,T,F,E,D,M,H,V,I):cost,s,t,f,e,d,m,isize) =
    (S+s,T+t,false,f orelse F,false,0,0,ref false,isize)

      (* space * time * setFlags * sideEffect * dontDestroy * maxregs *)

  val emit = fn s => output (std_out,s)

(* emitname constructs a string of form label n or label+n. The tree node
  it gets as a parameter is name, i.e. NAME or CONST or OP(PLUS,NAME,CONST) *)

  fun emitname t =
    case node_value t of
    NAME => emit (get_label t)
    | CONST => (emit ((int2str o get_ivalue) t))
    | LABEL =>
	(emit ((get_label o child1 o child0) t); emit "+";
      	 emit ((int2str o get_ivalue o child2 o child0) t))
    | _ => fatal "incorrect node for emitname"

  fun emitlocation t =
    case (get_kind t) of
    numbered 1 =>
      (emit "("; emit (reg2str (get_reg t)); emit ")"; givereg t)
    | numbered 2 =>
	(emitname (child1 t); emit "(";	emit ((reg2str o get_reg o child2) t);
	 emit ")"; (givereg o child2) t)
    | numbered 3 =>
	(emitname (child2 t); emit "("; emit ((reg2str o get_reg o child1) t);
	 emit ")"; (givereg o child1) t)
    | numbered 4 =>
	(emit "*"; emitname (child1 (child0 t)); emit "(";
	 emit ((reg2str o get_reg o child2) (child0 t)); emit ")";
      	 (givereg o child2) (child0 t))
    | numbered 5 =>
	(emit "*";emitname (child2 (child0 t)); emit "(";
	 emit ((reg2str o get_reg o child1) (child0 t)); emit ")";
	 (givereg o child1) (child0 t))
    | numbered 6 => emitname t
    | _ => fatal "incorrect node for emitlocation"

  val initialize = fn () => (initialize_registers();next_label := 0)


  val get_cost_space = (fn (s,_,_,_,_,_,_,_,_) => s)
  val get_cost_time = (fn (_,t,_,_,_,_,_,_,_) => t)
  val get_cost_isize = (fn (_,_,_,_,_,_,_,_,i) => i)
  val get_cost_setFlags =(fn (_,_,f,_,_,_,_,_,_) => f)
  val get_cost_dontDestroy = (fn (_,_,_,_,d,_,_,_,_) => d)

  fun emitioperand t =
  case get_kind t of
    numbered 11 =>
      (emitlocation (child1 t); emit "[";
       emit ((reg2str o get_reg o child1 o child2) t); emit "]";
       (givereg o child1 o child2) t )
  | numbered 12 =>
      (emit "("; emit ((reg2str o get_reg o child2) t); emit ")";
      emitlocation (child1 t); (givereg o child2) t )
  | numbered 13 =>
      (emitlocation (child2 t); emit "[";
       emit ((reg2str o get_reg o child2 o child2) t); emit "]";
       (givereg o child2 o child2) t )
  | numbered 14 =>
      (emit "("; emit ((reg2str o get_reg o child1) t); emit ")";
       emitlocation (child2 t); (givereg o child1) t )
  | n => fatal "incorrect node for emitioperand"

  fun emitoperand t =
    case get_kind t of
      numbered 21 => (emit ((reg2str o get_reg) t); givereg t)
    | numbered 22 => (emit "$"; emitname t)
    | numbered 24 => emitlocation (child0 t)
    | numbered 25 => emitioperand (child0 t)
    | n => fatal "incorrect node for emitoperand"



  fun commutative PLUS = true
    | commutative MUL = true
    | commutative OR = true
    | commutative EQ = true
    | commutative _  = false

  fun vaxop i =
    case i of
      Op PLUS => "add"
    | Op MINUS => "sub"
    | Op MUL => "mul"
    | Op DIV => "div"
    | Op OR => "bis"
    | Op XOR => "xor"
    | Op EQ => "eql"
    | Op NEQ => "neq"
    | Op LT => "lss"
    | Op LEQ => "leq"
    | Op GT => "gtr"
    | Op GEQ => "geq"
    | Op ULT => "lssu"
    | Op ULEQ => "lequ"
    | Op UGT => "gtru"
    | Op UGEQ => "gequ"
    | _ => fatal "not an opcode"

  fun negate c =
    Op
    (case c of
       Op EQ => NEQ
     | Op NEQ => EQ
     | Op LT => GEQ
     | Op GEQ => LT
     | Op GT => LEQ
     | Op LEQ => GT
     | Op ULEQ => UGT
     | Op UGT => ULEQ
     | Op ULT => UGEQ
     | Op UGEQ => ULT
     | _ => fatal "cannot negate")

  fun sizecodei 1 = "b"
    | sizecodei 2 = "w"
    | sizecodei 4 = "l"
    | sizecodei 8 = "q"
    | sizecodei _ = "X"

  fun sizecodef 4 = "f"
    | sizecodef 8 = "d"
    | sizecodef _ = "X"

  val sizecode = sizecodei

  val sizeioperand = get_size

  fun emitcomputation t =
    let val kind = get_kind t
    in
      case kind of
	numbered 31 =>
	  (emit ((vaxop o Op o get_op o child0) t);
	   emit (get_sizecode (child0 t) (get_size t));
	   emit "3\t"; ((emitoperand o child2) t); emit ",";
	   (emitoperand o child1) t; emit ",")
      | numbered 32 =>
	  (emit ((vaxop o Op o get_op o child0) t);
	   emit (sizecode (get_size t)); emit "\t";
	   emitoperand (child1 t); emit ",")
      | numbered 33 =>
	  let val (sf,st) = get_sizecodecvt (child0 t)
	      in
		emit "cvt"; emit (sf ((get_size o child1) t));
		emit (st (get_size t)); emit "\t";
		(emitoperand o child1) t; emit ","
	      end
      | numbered 34 => emitcomputation (child1 t)
      | Op RSHIFT =>
	  (emit "ashl\t"; (emitoperand o child2) t; emit ",";
	   (emitoperand o child1) t; emit ",")
      | numbered 37 =>
	  (emit "extzv\t$"; emit ((int2str o get_ivalue o child2) t);
	   emit ",$"; emit (int2str (32 - ((get_ivalue o child2) t)));
	   emit ","; emit ((reg2str o get_reg o child1) t); emit ",";
	   (givereg o child1) t )
      | numbered k =>
	  (if 1 <= k andalso k <= 8
	     then (emit "movab\t"; emitlocation t; emit ",")
	   else if 11 <= k andalso k <= 15
		  then (emit "mova"; emit ((sizecode o sizeioperand) t);
			emit "\t"; emitioperand t; emit "," )
		else if 21 <= k andalso k <= 27
		       then (emit "mov"; emit (sizecode (get_size t));
			     emit "\t"; emitoperand t; emit "," )
			else (emit "# strange kind of computation"))
      | _ => ()
    end



datatype result = XXXrewrite of tree | X_result of  unit | X_zero of  unit  | X_args of  unit
	 | X_name of  unit	 | X_cvtopu of  unit  | X_cvtop of  unit  | X_relop of  unit
	 | X_unop of  unit  | X_binop of  unit  | X_bigval of  unit  | X_flag of  unit
	 | X_ntest of  unit  | X_test of  unit  | X_computation of  unit  | X_destination of  unit
	 | X_ioperand of  unit  | X_location of  unit  | X_operand of  unit
	 | X_reg of  unit  | X_stm of  unit  | X_body of  unit 
 end

structure Specification =
  struct
structure User = User

open User
type rule = int
datatype skeletal = Skeleton of (rule * cost * tree * skeletal list)
exception MatchAbort
fun cost (Skeleton(_,c,_,_)) = c
exception InternalError of string

fun get_subtree (n,t) = nth (get_subtrees t,n-1)

fun execute_cost (n:rule, ir, children) =
let open User
val DC = (  sum_costs ) (map cost children)
val ABORT = (fn () => raise MatchAbort)
 in
case n of
  86 => (case map cost children of [stm,reg] => ((  WDH1(DC,0,0,get_cost_setFlags reg,false,get_cost_dontDestroy reg,0 ) )) | _ => raise InternalError "S4")
  | 85 => (case map cost children of [] => ((  if (get_ivalue ir ) <> 0 then ABORT( ) else DC  )) | _ => raise InternalError "S4")
  | 84 => DC
  | 83 => (case map cost children of [operand,args] => ((  WD (DC,1,6,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 82 => (case map cost children of [args,location] => ((  WD (DC,6,20,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 81 => (case map cost children of [result] => ((  WD (DC,2,2,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 80 => (case map cost children of [reg] => ((  WD(DC,2,2,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 79 => DC
  | 78 => (case map cost children of [reg] => ((  if not ((get_ivalue (get_subtree (3,ir)) ) = 1 orelse (get_ivalue (get_subtree (3,ir)) ) = ~1 ) orelse
      	    get_cost_dontDestroy reg then ABORT( )
      	else WDH1 (DC,2,4,true,false,false,0 )  )) | _ => raise InternalError "S4")
  | 77 => (case map cost children of [binop,operand,reg] => ((  if get_cost_dontDestroy reg orelse
      	   not ((commutative o get_op ) (get_subtree (1,ir)) ) then ABORT( )
      	else WDH1 (DC,2,0,true,false,false,0 )  )) | _ => raise InternalError "S4")
  | 76 => (case map cost children of [binop,reg,operand] => ((  if get_cost_dontDestroy reg
      	then ABORT( )
      	else WDH1 (DC,2,0,true,false,false,0 )  )) | _ => raise InternalError "S4")
  | 75 => (case map cost children of [destination,zero] => ((  WD (DC,1,4,true,true,false,0 )  )) | _ => raise InternalError "S4")
  | 74 => (case map cost children of [destination,operand] => ((  if not ((equal ((get_subtree (1,ir)), (get_subtree (2,(get_subtree (2,ir)))) ) ) andalso
      	  ((get_ivalue (get_subtree (3,(get_subtree (2,ir)))) ) = 1 orelse (get_ivalue (get_subtree (3,(get_subtree (2,ir)))) ) = ~1 ) )
      	then ABORT( )
      	else WD (DC,1-(get_cost_space operand ), 8-(get_cost_time operand ),
      	      	  true,true,false,0 )  )) | _ => raise InternalError "S4")
  | 73 => (case map cost children of [destination,binop,operand1,operand2] => ((  if not ((commutative o get_op ) (get_subtree (1,(get_subtree (2,ir)))) ) orelse
      	  (get_sideEffect DC ) orelse not (equal ((get_subtree (1,ir)), (get_subtree (3,(get_subtree (2,ir)))) ) )
      	  then ABORT( )
      	  else WD (DC,1-(get_cost_space operand2 ),
      	      	    8-(get_cost_time operand2 ),true,true,false,0 )  )) | _ => raise InternalError "S4")
  | 72 => (case map cost children of [destination,binop,operand1,operand2] => ((  if (get_sideEffect DC ) orelse not (equal((get_subtree (1,ir)), (get_subtree (2,(get_subtree (2,ir)))) ) )
      	  then ABORT( )
      	  else WD (DC,1-(get_cost_space operand1 ),
      	      	    8-(get_cost_time operand1 ),true,true,false,0 )
      	 )) | _ => raise InternalError "S4")
  | 71 => (case map cost children of [destination,computation] => ((  WD (DC,0,8,true,true,false,0 )  )) | _ => raise InternalError "S4")
  | 70 => (case map cost children of [destination,reg] => ((  WDH1 (DC,2,12,true,true,false,0 )  )) | _ => raise InternalError "S4")
  | 69 => (case map cost children of [] => ((  C (4,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 68 => (case map cost children of [] => ((  C (4,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 67 => (case map cost children of [] => ((  let val i = get_ivalue ir in
      	C (if i>= 0
      	then
      	  if i > 32767
      	  then 4
      	  else if i>127 then 2 else 1
      	else
      	  if i < ~32768
      	  then 4
      	  else if i < ~128 then 2 else 1, 0, false,false,false,0 )
      	end )) | _ => raise InternalError "S4")
  | 66 => DC
  | 65 => DC
  | 64 => DC
  | 63 => (case map cost children of [] => ((  C (0,4,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 62 => DC
  | 61 => DC
  | 60 => DC
  | 59 => DC
  | 58 => DC
  | 57 => DC
  | 56 => DC
  | 55 => DC
  | 54 => DC
  | 53 => DC
  | 52 => (case map cost children of [] => ((  C(0,4,false,false,false,0 ) )) | _ => raise InternalError "S4")
  | 51 => (case map cost children of [] => ((  C(0,4,false,false,false,0 ) )) | _ => raise InternalError "S4")
  | 50 => (case map cost children of [] => ((  C(0,4,false,false,false,0 ) )) | _ => raise InternalError "S4")
  | 49 => (case map cost children of [] => (( C(0,100,false,false,false,0 ) )) | _ => raise InternalError "S4")
  | 48 => (case map cost children of [] => ((  C(0,16,false,false,false,0 ) )) | _ => raise InternalError "S4")
  | 47 => (case map cost children of [] => ((  C(0,4,false,false,false,0 ) )) | _ => raise InternalError "S4")
  | 46 => (case map cost children of [] => ((  C(0,4,false,false,false,0 ) )) | _ => raise InternalError "S4")
  | 45 => (case map cost children of [] => ((  C(0,4,false,false,false,0 ) )) | _ => raise InternalError "S4")
  | 44 => (case map cost children of [] => ((  C(0,4,false,false,false,0 ) )) | _ => raise InternalError "S4")
  | 43 => (case map cost children of [test] => ((  WDH1 (DC,9,12,true,false,false,0 )  )) | _ => raise InternalError "S4")
  | 42 => (case map cost children of [relop,stm,zero] => ((  if get_cost_setFlags stm then DC else ABORT( )  )) | _ => raise InternalError "S4")
  | 41 => (case map cost children of [relop,operand,zero] => ((  WD (DC,1,4,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 40 => (case map cost children of [relop,operand1,operand2] => ((  WD (DC,1,4,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 39 => (case map cost children of [flag] => (( WD (DC,4,8,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 38 => (case map cost children of [flag] => ((  WD (DC,4,8,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 37 => DC
  | 36 => DC
  | 35 => DC
  | 34 => DC
  | 33 => (case map cost children of [ioperand] => ((  if (get_cost_isize ioperand ) > 8
      	orelse ((((sizecode o get_cost_isize ) ioperand ) = "X" ) )
      	then ABORT( )
      	else WDHA (DC,1,4,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 32 => (case map cost children of [location] => ((  WDHA (DC,1,4,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 31 => (case map cost children of [cvtop,operand] => ((  WDHA (DC,1,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 30 => (case map cost children of [unop,operand] => ((  WDHA (DC,1,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 29 => (case map cost children of [binop,operand1,operand2] => ((  WDHA (DC,1,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 28 => (case map cost children of [operand] => ((  if (get_size ir ) > 8 orelse
      	((((sizecode o get_size ) ir ) = "X" ) )
      	then ABORT( )
      	else WDHA (DC,1,4,get_cost_setFlags operand,false,false,0 )  )) | _ => raise InternalError "S4")
  | 27 => (case map cost children of [destination] => ((  WDHA (DC,0,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 26 => (case map cost children of [] => ((  if not ((get_ivalue ir ) >= 0 andalso (get_ivalue ir ) < 64 )
      	then ABORT( )
      	else WD (DC,1,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 25 => (case map cost children of [name] => ((  WD (DC,1,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 24 => (case map cost children of [reg] => ((  WDHA (DC,1,0,get_cost_setFlags reg,false,false,0 )  )) | _ => raise InternalError "S4")
  | 23 => (case map cost children of [ioperand] => ((  if (get_size ir ) <> (get_cost_isize ioperand )
      	then ABORT( )
      	else WDHA (DC,0,4,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 22 => (case map cost children of [location] => ((  WDHA (DC,0,4,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 21 => (case map cost children of [reg,location] => ((  WDHAs (DC,1,6,false,false,false,0, 1 ) )) | _ => raise InternalError "S4")
  | 20 => (case map cost children of [reg,location] => ((  WDHAs (DC,1,6,false,false,false,0, get_ivalue (get_subtree (3,(get_subtree (2,ir)))) ) )) | _ => raise InternalError "S4")
  | 19 => (case map cost children of [location,reg] => ((  WDHAs (DC,1,6,false,false,false,0, 1 ) )) | _ => raise InternalError "S4")
  | 18 => (case map cost children of [location,reg] => ((  WDHAs (DC,1,6,false,false,false,0, get_ivalue (get_subtree (3,(get_subtree (3,ir)))) ) )) | _ => raise InternalError "S4")
  | 17 => (case map cost children of [name] => ((  WD (DC,1,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 16 => (case map cost children of [reg,name] => ((  WDHA (DC,1,4,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 15 => (case map cost children of [name,reg] => ((  WDHA (DC,1,4,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 14 => (case map cost children of [reg,name] => ((  WDHA (DC,1,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 13 => (case map cost children of [name,reg] => ((  WDHA (DC,1,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 12 => (case map cost children of [reg] => ((  WDHA (DC,1,0,false,false,false,0 )  )) | _ => raise InternalError "S4")
  | 11 => (case map cost children of [] => ((  WD (DC,0,0,false,false,true,0 ) )) | _ => raise InternalError "S4")
  | 10 => (case map cost children of [computation] => ((  WD (DC,1,0,true,true,true,0 ) )) | _ => raise InternalError "S4")
  | 9 => (case map cost children of [computation] => ((  WDH1 (DC,1,0,true,false,false,0 )  )) | _ => raise InternalError "S4")
  | 8 => DC
  | 7 => DC
  | 6 => (case map cost children of [ntest,location] => ((  WD (DC,1,4,false,true,false,0 ) )) | _ => raise InternalError "S4")
  | 5 => (case map cost children of [test] => ((  WD (DC,0,0,false,true,false,0 ) )) | _ => raise InternalError "S4")
  | 4 => (case map cost children of [location] => ((  WD (DC,1,8,false,true,false,0 ) )) | _ => raise InternalError "S4")
  | 3 => (case map cost children of [name] => ((  WD (DC,3,8,false,true,false,0 ) )) | _ => raise InternalError "S4")
  | 2 => DC
  | 1 => DC
  | 0 => DC
  | _ => raise InternalError "S4.3."
end

fun execute (Skeleton (n,_, ir, children)) =
 let open User
in
case n of
86 => X_reg ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_stm stm,X_reg reg) => (  set_reg(ir, get_reg (get_subtree (2,ir)) ); givereg (get_subtree (2,ir))  ) | _ => raise InternalError "S5" )
  | 85 => X_zero(  )
  | 84 => X_args(  )
  | 83 => X_args ( case (let val C = nth(children,0)in fn () => case execute C of X_operand V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,1)in fn () => case execute C of X_args V => V | _ => raise InternalError "S4.3" end) of (DOoperand,DOargs) => (  DOoperand( );
        emit "movl\t"; emitoperand (get_subtree (1,ir)); emit ",-(sp)\n";
	DOargs( ) ) )
  | 82 => X_result ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_args args,X_location location) => (  calling( );
	    emit "calls\t$"; emit ((int2str o count_arguments ) (get_subtree (1,ir)) );
	    emit ","; emitlocation (get_subtree (2,ir)); emit "\n"  ) | _ => raise InternalError "S5" )
  | 81 => X_reg ( case (execute (nth(children,0))) of (X_result result) => (  set_reg (ir,resultReg( ) )  ) | _ => raise InternalError "S5" )
  | 80 => X_stm ( case (execute (nth(children,0))) of (X_reg reg) => (  emit "movl\t"; emit (reg2str (get_reg (get_subtree (1,ir)) ) );
	    emit ",r0\nret\n"  ) | _ => raise InternalError "S5" )
  | 79 => X_stm ( case (execute (nth(children,0))) of (X_result result) => (  emit "ret\n"  ) | _ => raise InternalError "S5" )
  | 78 => X_reg ( case (execute (nth(children,0))) of (X_reg reg) => (  set_reg (ir, get_reg (get_subtree (2,ir)) ); givereg (get_subtree (2,ir));
      	emit (if (get_ivalue (get_subtree (3,ir)) ) > 0 then "inc" else "dec" );
	emit (sizecode (get_size ir ) ); emit "\t";
	emit (reg2str (get_reg ir ) ); emit "\n" ) | _ => raise InternalError "S5" )
  | 77 => X_reg ( case (execute (nth(children,0)),execute (nth(children,1)),execute (nth(children,2))) of (X_binop binop,X_operand operand,X_reg reg) => (  emit ((vaxop o Op o get_op ) (get_subtree (1,ir)) );
        emit (get_sizecode (get_subtree (1,ir)) (get_size ir ) ); emit "2\t";
	emitoperand (get_subtree (2,ir)); emit ","; emit (reg2str (get_reg (get_subtree (3,ir)) ) );
	emit "\n";
	set_reg (ir, get_reg (get_subtree (3,ir)) );
	givereg (get_subtree (3,ir))  ) | _ => raise InternalError "S5" )
  | 76 => X_reg ( case (execute (nth(children,0)),execute (nth(children,1)),execute (nth(children,2))) of (X_binop binop,X_reg reg,X_operand operand) => ( 
      	set_reg(ir,get_reg (get_subtree (2,ir)) );
      	givereg (get_subtree (2,ir));
        emit ((vaxop o Op o get_op ) (get_subtree (1,ir)) );
        emit (get_sizecode (get_subtree (1,ir)) (get_size ir ) );
	emit "2\t"; emitoperand (get_subtree (3,ir)); emit ",";
	emit (reg2str (get_reg ir ) ); emit "\n"
       ) | _ => raise InternalError "S5" )
  | 75 => X_stm ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_destination destination,X_zero zero) => (  emit "clr"; emit (sizecode (get_size (get_subtree (1,ir)) ) ); emit "\t";
        emitoperand (get_subtree (1,ir)); emit "\n" ) | _ => raise InternalError "S5" )
  | 74 => X_stm ( case (let val C = nth(children,0)in fn () => case execute C of X_destination V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,1)in fn () => case execute C of X_operand V => V | _ => raise InternalError "S4.3" end) of (DOdestination,DOoperand) => (  DOdestination( );
      	emit (if (get_ivalue (get_subtree (3,(get_subtree (2,ir)))) ) > 0 then "inc" else "dec" );
	emit (sizecode (get_size (get_subtree (1,ir)) ) ); emit "\t"; emitoperand (get_subtree (1,ir));
	emit "\n"  ) )
  | 73 => X_stm ( case (let val C = nth(children,0)in fn () => case execute C of X_destination V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,1)in fn () => case execute C of X_binop V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,2)in fn () => case execute C of X_operand V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,3)in fn () => case execute C of X_operand V => V | _ => raise InternalError "S4.3" end) of (DOdestination,DObinop,DOoperand1,DOoperand2) => (  DOdestination( ); DObinop( ); DOoperand1( );
      	emit ((vaxop o Op o get_op ) (get_subtree (1,(get_subtree (2,ir)))) );
	emit (get_sizecode (get_subtree (1,(get_subtree (2,ir)))) (get_size ir ) );
      	emit "2\t"; emitoperand (get_subtree (2,(get_subtree (2,ir)))); emit ","; emitoperand (get_subtree (1,ir));
	emit "\n"
       ) )
  | 72 => X_stm ( case (let val C = nth(children,0)in fn () => case execute C of X_destination V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,1)in fn () => case execute C of X_binop V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,2)in fn () => case execute C of X_operand V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,3)in fn () => case execute C of X_operand V => V | _ => raise InternalError "S4.3" end) of (DOdestination,DObinop,DOoperand1,DOoperand2) => (  DOdestination( ); DObinop( ); DOoperand2( );
      	emit ((vaxop o Op o get_op ) (get_subtree (1,(get_subtree (2,ir)))) );
	emit (get_sizecode (get_subtree (1,(get_subtree (2,ir)))) (get_size ir ) ); emit "2\t";
	emitoperand (get_subtree (3,(get_subtree (2,ir)))); emit ","; emitoperand (get_subtree (1,ir)); emit "\n"
       ) )
  | 71 => X_stm ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_destination destination,X_computation computation) => (  emitcomputation (get_subtree (2,ir)); emitoperand (get_subtree (1,ir)); emit "\n"  ) | _ => raise InternalError "S5" )
  | 70 => X_reg ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_destination destination,X_reg reg) => (  set_reg (ir, get_reg (get_subtree (2,ir)) );
      	givereg (get_subtree (2,ir));
        emit "mov"; emit ((sizecode o get_size ) (get_subtree (2,ir)) ); emit "\t";
      	emit (reg2str (get_reg ir ) ); emit ","; emitoperand (get_subtree (1,ir));
      	emit "\n"  ) | _ => raise InternalError "S5" )
  | 69 => X_name(  )
  | 68 => X_name(  )
  | 67 => X_name(  )
  | 66 => X_cvtopu(  )
  | 65 => X_cvtopu(  )
  | 64 => X_cvtopu(  )
  | 63 => X_cvtop(  set_sizecodecvt (ir, sizecodei, sizecodei )  )
  | 62 => X_relop(  set_sizecode (ir, sizecodei )  )
  | 61 => X_relop(  set_sizecode (ir, sizecodei )  )
  | 60 => X_relop(  set_sizecode (ir, sizecodei )  )
  | 59 => X_relop(  set_sizecode (ir, sizecodei )  )
  | 58 => X_relop(  set_sizecode (ir, sizecodei )  )
  | 57 => X_relop(  set_sizecode (ir, sizecodei )  )
  | 56 => X_relop(  set_sizecode (ir, sizecodei )  )
  | 55 => X_relop(  set_sizecode (ir, sizecodei )  )
  | 54 => X_relop(  set_sizecode (ir, sizecodei )  )
  | 53 => X_relop(  set_sizecode (ir, sizecodei )  )
  | 52 => X_binop(  set_sizecode(ir, sizecodei ) )
  | 51 => X_binop(  set_sizecode(ir, sizecodei ) )
  | 50 => X_binop(  set_sizecode(ir, sizecodei ) )
  | 49 => X_binop(  set_sizecode(ir, sizecodei ) )
  | 48 => X_binop(  set_sizecode(ir, sizecodei ) )
  | 47 => X_binop(  set_sizecode(ir, sizecodei ) )
  | 46 => X_binop(  set_sizecode(ir, sizecodei ) )
  | 45 => X_unop(  set_sizecode(ir, sizecodei ) )
  | 44 => X_unop(  set_sizecode(ir, sizecodei ) )
  | 43 => X_reg ( case (let val C = nth(children,0)in fn () => case execute C of X_test V => V | _ => raise InternalError "S4.3" end) of (DOtest) => (  let val merge = newLabel( )
	in
	  set_truebranch ((get_subtree (1,ir)), newLabel( ) );
	  DOtest( );
	  getreg ir;
	  emit "movb\t$0,"; emit (reg2str (get_reg ir ) ); emit "\njbr\t";
	  emit merge; emit "\n"; emit (get_truebranch (get_subtree (1,ir)) );
	  emit ":\nmovb\t$1,"; emit (reg2str (get_reg ir ) ); emit "\n";
	  emit merge; emit ":\n"
	end ) )
  | 42 => X_flag ( case (execute (nth(children,0)),execute (nth(children,1)),execute (nth(children,2))) of (X_relop relop,X_stm stm,X_zero zero) => (  set_kind (ir, get_op (get_subtree (1,ir)) )  ) | _ => raise InternalError "S5" )
  | 41 => X_flag ( case (execute (nth(children,0)),execute (nth(children,1)),execute (nth(children,2))) of (X_relop relop,X_operand operand,X_zero zero) => (  emit "tst"; emit (get_sizecode (get_subtree (1,ir)) (get_size (get_subtree (2,ir)) ) ); emit "\t";
        emitoperand (get_subtree (2,ir)); emit "\n";
      	set_kind (ir, get_op (get_subtree (1,ir)) )  ) | _ => raise InternalError "S5" )
  | 40 => X_flag ( case (execute (nth(children,0)),execute (nth(children,1)),execute (nth(children,2))) of (X_relop relop,X_operand operand1,X_operand operand2) => (  emit "cmp"; emit (get_sizecode (get_subtree (1,ir)) (get_size (get_subtree (2,ir)) ) ); emit "\t";
        emitoperand (get_subtree (2,ir)); emit ","; emitoperand (get_subtree (3,ir)); emit "\n";
      	set_kind (ir, get_op (get_subtree (1,ir)) )  ) | _ => raise InternalError "S5" )
  | 39 => X_test ( case (execute (nth(children,0))) of (X_flag flag) => (  emit "j"; emit ((vaxop o get_kind ) ir ); emit "\t";
      	emit (get_truebranch ir ); emit "\n"  ) | _ => raise InternalError "S5" )
  | 38 => X_ntest ( case (execute (nth(children,0))) of (X_flag flag) => (  emit "j"; emit ((vaxop o negate o get_kind ) ir ); emit "\t";
      	emit (get_truebranch ir ); emit "\n"  ) | _ => raise InternalError "S5" )
  | 37 => X_ntest ( case (let val C = nth(children,0)in fn () => case execute C of X_test V => V | _ => raise InternalError "S4.3" end) of (DOtest) => (  set_truebranch ((get_subtree (1,ir)), get_truebranch ir );
      	DOtest( ); ( ) ) )
  | 36 => X_test ( case (let val C = nth(children,0)in fn () => case execute C of X_ntest V => V | _ => raise InternalError "S4.3" end) of (DOntest) => (  set_truebranch ((get_subtree (1,ir)), get_truebranch ir );
      	DOntest( ); ( )  ) )
  | 35 => X_ntest ( case (let val C = nth(children,0)in fn () => case execute C of X_ntest V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,1)in fn () => case execute C of X_ntest V => V | _ => raise InternalError "S4.3" end) of (DOntest1,DOntest2) => (  set_truebranch ((get_subtree (1,ir)), get_truebranch ir );
      	set_truebranch ((get_subtree (2,ir)), get_truebranch ir );
      	DOntest1( ); DOntest2( ); ( ) ) )
  | 34 => X_test ( case (let val C = nth(children,0)in fn () => case execute C of X_ntest V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,1)in fn () => case execute C of X_test V => V | _ => raise InternalError "S4.3" end) of (DOntest,DOtest) => (  let val l = newLabel( ) in
        set_truebranch ((get_subtree (1,ir)), l );
        set_truebranch ((get_subtree (2,ir)), get_truebranch ir );
      	DOntest( ); DOtest( );
      	emit l; emit ":\n"
	end ) )
  | 33 => X_computation ( case (execute (nth(children,0))) of (X_ioperand ioperand) => (  ) | _ => raise InternalError "S5" )
  | 32 => X_computation ( case (execute (nth(children,0))) of (X_location location) => (  ) | _ => raise InternalError "S5" )
  | 31 => X_computation ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_cvtop cvtop,X_operand operand) => (  set_kind_n (ir,33 )  ) | _ => raise InternalError "S5" )
  | 30 => X_computation ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_unop unop,X_operand operand) => (  set_kind_n (ir,32 )  ) | _ => raise InternalError "S5" )
  | 29 => X_computation ( case (execute (nth(children,0)),execute (nth(children,1)),execute (nth(children,2))) of (X_binop binop,X_operand operand1,X_operand operand2) => (  set_kind_n (ir,31 )  ) | _ => raise InternalError "S5" )
  | 28 => X_computation ( case (execute (nth(children,0))) of (X_operand operand) => (  ) | _ => raise InternalError "S5" )
  | 27 => X_operand ( case (execute (nth(children,0))) of (X_destination destination) => (  ) | _ => raise InternalError "S5" )
  | 26 => X_operand(  set_kind_n (ir,22 )  )
  | 25 => X_operand ( case (execute (nth(children,0))) of (X_name name) => (  set_kind_n (ir,22 )  ) | _ => raise InternalError "S5" )
  | 24 => X_operand ( case (execute (nth(children,0))) of (X_reg reg) => (  set_kind_n (ir,21 )  ) | _ => raise InternalError "S5" )
  | 23 => X_destination ( case (execute (nth(children,0))) of (X_ioperand ioperand) => (  set_kind_n (ir,25 )  ) | _ => raise InternalError "S5" )
  | 22 => X_destination ( case (execute (nth(children,0))) of (X_location location) => (  set_kind_n (ir,24 )  ) | _ => raise InternalError "S5" )
  | 21 => X_ioperand ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_reg reg,X_location location) => (  set_kind_n (ir,14 )  ) | _ => raise InternalError "S5" )
  | 20 => X_ioperand ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_reg reg,X_location location) => (  set_kind_n (ir,13 )  ) | _ => raise InternalError "S5" )
  | 19 => X_ioperand ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_location location,X_reg reg) => (  set_kind_n (ir,12 )  ) | _ => raise InternalError "S5" )
  | 18 => X_ioperand ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_location location,X_reg reg) => (  set_kind_n (ir,11 )  ) | _ => raise InternalError "S5" )
  | 17 => X_location ( case (execute (nth(children,0))) of (X_name name) => (  set_kind_n (ir,6 )  ) | _ => raise InternalError "S5" )
  | 16 => X_location ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_reg reg,X_name name) => (  set_kind_n (ir,5 )  ) | _ => raise InternalError "S5" )
  | 15 => X_location ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_name name,X_reg reg) => (  set_kind_n (ir,4 )  ) | _ => raise InternalError "S5" )
  | 14 => X_location ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_reg reg,X_name name) => (  set_kind_n (ir,3 )  ) | _ => raise InternalError "S5" )
  | 13 => X_location ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_name name,X_reg reg) => (  set_kind_n (ir,2 )  ) | _ => raise InternalError "S5" )
  | 12 => X_location ( case (execute (nth(children,0))) of (X_reg reg) => (  set_kind_n (ir,1 )  ) | _ => raise InternalError "S5" )
  | 11 => X_reg(  set_reg (ir,get_temp ir )  )
  | 10 => X_reg ( case (execute (nth(children,0))) of (X_computation computation) => (  emitcomputation (get_subtree (2,ir));
      	set_reg (ir, get_temp (get_subtree (1,ir)) );
      	emit (reg2str (get_temp (get_subtree (1,ir)) ) ); emit "\n" ) | _ => raise InternalError "S5" )
  | 9 => X_reg ( case (execute (nth(children,0))) of (X_computation computation) => (  emitcomputation ir; getreg ir;
      	emit (reg2str (get_reg ir ) ); emit "\n" ) | _ => raise InternalError "S5" )
  | 8 => X_stm ( case (execute (nth(children,0))) of (X_bigval bigval) => (  emit "# throw away "; emit ((reg2str o get_reg ) ir );
	       givereg ir  ) | _ => raise InternalError "S5" )
  | 7 => X_stm ( case (execute (nth(children,0))) of (X_operand operand) => (  emit "# throw away "; emitoperand ir; emit "\n"  ) | _ => raise InternalError "S5" )
  | 6 => X_stm ( case (let val C = nth(children,0)in fn () => case execute C of X_ntest V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,1)in fn () => case execute C of X_location V => V | _ => raise InternalError "S4.3" end) of (DOntest,DOlocation) => (  set_truebranch ((get_subtree (1,ir)), newLabel( ) ); DOntest( ); DOlocation( );
	 emit "jmp\t"; emitlocation (get_subtree (2,ir)); emit "\n";
	 emit (get_truebranch (get_subtree (1,ir)) ); emit ":\n"  ) )
  | 5 => X_stm ( case (let val C = nth(children,0)in fn () => case execute C of X_test V => V | _ => raise InternalError "S4.3" end) of (DOtest) => (  set_truebranch ((get_subtree (1,ir)), get_label (get_subtree (2,ir)) ) ; DOtest( ); ( ) ) )
  | 4 => X_stm ( case (execute (nth(children,0))) of (X_location location) => (  emit "jmp\t"; emitlocation (get_subtree (1,ir)); emit "\n"  ) | _ => raise InternalError "S5" )
  | 3 => X_stm ( case (execute (nth(children,0))) of (X_name name) => (  emit "jbr\t"; emitname (get_subtree (1,ir)); emit "\n"  ) | _ => raise InternalError "S5" )
  | 2 => X_stm(  emit (get_label ir ); emit ":\n"  )
  | 1 => X_stm ( case (execute (nth(children,0)),execute (nth(children,1))) of (X_stm stm1,X_stm stm2) => (   ) | _ => raise InternalError "S5" )
  | 0 => X_body ( case (let val C = nth(children,0)in fn () => case execute C of X_operand V => V | _ => raise InternalError "S4.3" end,let val C = nth(children,1)in fn () => case execute C of X_stm V => V | _ => raise InternalError "S4.3" end) of (DOoperand,DOstm) => (  let val masklabel = newLabel( )
      	      and proclab = get_proclabel ir
      	  in
	    emit ".text.align\t1\n.globl\t"; emit proclab; emit "\n";
      	    emit proclab; emit ":\n.word\t"; emit masklabel; emit "\n";
	    DOoperand( );
	    emit "subl2\t"; emitoperand (get_subtree (1,ir)); emit ",sp\n";
	    DOstm( );
	    emit "ret\n.set\t"; emit masklabel; emit ",";
	    emit (int2str (regmask( ) ) ); emit "\n"
      	  end  ) )
  | _ => raise Match
end

val matchcounts = [
(86,2),
(85,1),
(84,1),
(83,2),
(82,2),
(81,1),
(80,1),
(79,1),
(78,3),
(77,3),
(76,3),
(75,2),
(74,4),
(73,4),
(72,4),
(71,2),
(70,2),
(69,3),
(68,1),
(67,1),
(66,1),
(65,1),
(64,1),
(63,1),
(62,1),
(61,1),
(60,1),
(59,1),
(58,1),
(57,1),
(56,1),
(55,1),
(54,1),
(53,1),
(52,1),
(51,1),
(50,1),
(49,1),
(48,1),
(47,1),
(46,1),
(45,1),
(44,1),
(43,1),
(42,3),
(41,3),
(40,3),
(39,1),
(38,1),
(37,1),
(36,1),
(35,2),
(34,2),
(33,1),
(32,1),
(31,2),
(30,2),
(29,3),
(28,1),
(27,1),
(26,1),
(25,1),
(24,1),
(23,1),
(22,1),
(21,3),
(20,5),
(19,3),
(18,5),
(17,1),
(16,3),
(15,3),
(14,3),
(13,3),
(12,1),
(11,1),
(10,2),
(9,1),
(8,1),
(7,1),
(6,2),
(5,2),
(4,1),
(3,1),
(2,1),
(1,2),
(0,2)]
val matchtable = let val a = Array.array(87,0) in ((app (fn(r,m)=>Array.update (a,r,m)) matchcounts); a) end

fun matches r = Array.sub(matchtable, r)

fun get_finals s =
  case s of
0 => []
  | 1 => []
  | 2 => []
  | 3 => [(2,0,XXXbody)]
  | 4 => []
  | 5 => [(2,0,XXXbody)]
  | 6 => []
  | 7 => []
  | 8 => [(2,1,XXXstm)]
  | 9 => []
  | 10 => [(2,1,XXXstm)]
  | 11 => []
  | 12 => []
  | 13 => [(2,3,XXXstm)]
  | 14 => [(2,4,XXXstm)]
  | 15 => []
  | 16 => []
  | 17 => [(2,5,XXXstm)]
  | 18 => []
  | 19 => [(2,5,XXXstm)]
  | 20 => [(2,6,XXXstm)]
  | 21 => [(2,6,XXXstm)]
  | 22 => []
  | 23 => []
  | 24 => [(2,10,XXXreg)]
  | 25 => []
  | 26 => [(2,71,XXXstm),(2,10,XXXreg)]
  | 27 => []
  | 28 => []
  | 29 => [(2,78,XXXreg),(2,69,XXXname),(2,21,XXXioperand),(2,20,XXXioperand),(2,19,XXXioperand),(2,18,XXXioperand),(2,14,XXXlocation),(2,13,XXXlocation)]
  | 30 => []
  | 31 => [(2,13,XXXlocation)]
  | 32 => []
  | 33 => [(2,77,XXXreg),(2,19,XXXioperand),(2,13,XXXlocation)]
  | 34 => [(2,78,XXXreg),(2,76,XXXreg),(2,21,XXXioperand),(2,14,XXXlocation)]
  | 35 => [(2,14,XXXlocation)]
  | 36 => []
  | 37 => []
  | 38 => []
  | 39 => []
  | 40 => [(2,78,XXXreg),(2,69,XXXname),(2,21,XXXioperand),(2,20,XXXioperand),(2,19,XXXioperand),(2,18,XXXioperand),(2,14,XXXlocation),(2,13,XXXlocation),(3,16,XXXlocation),(3,15,XXXlocation)]
  | 41 => []
  | 42 => [(2,13,XXXlocation),(3,15,XXXlocation)]
  | 43 => []
  | 44 => [(2,77,XXXreg),(2,19,XXXioperand),(2,13,XXXlocation),(3,15,XXXlocation)]
  | 45 => [(2,78,XXXreg),(2,76,XXXreg),(2,21,XXXioperand),(2,14,XXXlocation),(3,16,XXXlocation)]
  | 46 => [(2,14,XXXlocation),(3,16,XXXlocation)]
  | 47 => [(2,19,XXXioperand),(2,18,XXXioperand)]
  | 48 => []
  | 49 => []
  | 50 => [(3,18,XXXioperand)]
  | 51 => []
  | 52 => [(2,78,XXXreg),(2,76,XXXreg),(2,21,XXXioperand),(2,14,XXXlocation),(3,18,XXXioperand)]
  | 53 => []
  | 54 => [(2,78,XXXreg),(2,69,XXXname),(3,18,XXXioperand)]
  | 55 => []
  | 56 => []
  | 57 => [(3,20,XXXioperand)]
  | 58 => []
  | 59 => [(2,78,XXXreg),(2,76,XXXreg),(2,21,XXXioperand),(2,14,XXXlocation),(3,20,XXXioperand)]
  | 60 => []
  | 61 => [(2,78,XXXreg),(2,69,XXXname),(3,20,XXXioperand)]
  | 62 => [(2,21,XXXioperand),(2,20,XXXioperand)]
  | 63 => [(2,22,XXXdestination)]
  | 64 => [(2,23,XXXdestination)]
  | 65 => [(2,77,XXXreg),(2,76,XXXreg),(2,29,XXXcomputation)]
  | 66 => [(2,77,XXXreg),(2,41,XXXflag),(2,40,XXXflag),(2,29,XXXcomputation)]
  | 67 => [(2,76,XXXreg),(2,40,XXXflag),(2,29,XXXcomputation)]
  | 68 => []
  | 69 => []
  | 70 => [(2,30,XXXcomputation)]
  | 71 => []
  | 72 => [(2,31,XXXcomputation),(2,30,XXXcomputation)]
  | 73 => [(2,31,XXXcomputation)]
  | 74 => []
  | 75 => []
  | 76 => [(2,35,XXXntest),(2,34,XXXtest)]
  | 77 => []
  | 78 => [(2,34,XXXtest)]
  | 79 => [(2,35,XXXntest)]
  | 80 => []
  | 81 => []
  | 82 => [(2,36,XXXtest)]
  | 83 => [(2,37,XXXntest)]
  | 84 => [(2,42,XXXflag),(2,41,XXXflag),(2,40,XXXflag)]
  | 85 => [(2,42,XXXflag),(2,41,XXXflag)]
  | 86 => [(2,42,XXXflag)]
  | 87 => []
  | 88 => []
  | 89 => [(2,43,XXXreg)]
  | 90 => [(2,69,XXXname)]
  | 91 => [(2,78,XXXreg),(2,69,XXXname)]
  | 92 => [(2,75,XXXstm),(2,74,XXXstm),(2,73,XXXstm),(2,72,XXXstm),(2,71,XXXstm),(2,70,XXXreg)]
  | 93 => [(2,70,XXXreg)]
  | 94 => []
  | 95 => []
  | 96 => [(2,77,XXXreg),(2,76,XXXreg),(2,29,XXXcomputation),(3,73,XXXstm),(3,72,XXXstm)]
  | 97 => []
  | 98 => [(2,77,XXXreg),(2,41,XXXflag),(2,40,XXXflag),(2,29,XXXcomputation),(3,74,XXXstm),(3,73,XXXstm),(3,72,XXXstm)]
  | 99 => []
  | 100 => [(2,76,XXXreg),(2,40,XXXflag),(2,29,XXXcomputation),(3,73,XXXstm),(3,72,XXXstm)]
  | 101 => [(2,78,XXXreg),(2,69,XXXname),(2,21,XXXioperand),(2,20,XXXioperand),(2,19,XXXioperand),(2,18,XXXioperand),(2,14,XXXlocation),(2,13,XXXlocation),(3,74,XXXstm)]
  | 102 => [(2,78,XXXreg),(2,69,XXXname),(3,74,XXXstm)]
  | 103 => [(2,75,XXXstm)]
  | 104 => []
  | 105 => []
  | 106 => [(2,79,XXXstm)]
  | 107 => [(2,80,XXXstm)]
  | 108 => []
  | 109 => []
  | 110 => [(2,82,XXXresult)]
  | 111 => []
  | 112 => [(2,82,XXXresult)]
  | 113 => []
  | 114 => []
  | 115 => [(2,83,XXXargs)]
  | 116 => []
  | 117 => [(2,83,XXXargs)]
  | 118 => []
  | 119 => []
  | 120 => [(2,86,XXXreg)]
  | 121 => []
  | 122 => [(2,86,XXXreg)]
  | _ => nil

fun go (s,a) =
  case s of
0 => (case a of ESEQ => 118 | ARG => 113 | CALL => 108 | RETURN => 104 | BOOL => 87 | NOT => 80 | CAND => 74 | UNOP => 68 | MEM => 36 | OP => 27 | MOVE => 22 | CJUMP => 15 | JUMP => 11 | SEQ => 6 | PROC => 1 |  _ => 0)
  | 1 => (case a of (ARC 2) => 4 | (ARC 1) => 2 |  _ => go (0,a))
  | 2 => (case a of XXXoperand => 3 |  _ => go (0,a))
  | 3 => (case a of  _ => go (0,a))
  | 4 => (case a of XXXstm => 5 |  _ => go (0,a))
  | 5 => (case a of  _ => go (0,a))
  | 6 => (case a of (ARC 2) => 9 | (ARC 1) => 7 |  _ => go (0,a))
  | 7 => (case a of XXXstm => 8 |  _ => go (0,a))
  | 8 => (case a of  _ => go (0,a))
  | 9 => (case a of XXXstm => 10 |  _ => go (0,a))
  | 10 => (case a of  _ => go (0,a))
  | 11 => (case a of (ARC 1) => 12 |  _ => go (0,a))
  | 12 => (case a of XXXlocation => 14 | XXXname => 13 |  _ => go (0,a))
  | 13 => (case a of  _ => go (0,a))
  | 14 => (case a of  _ => go (0,a))
  | 15 => (case a of (ARC 2) => 18 | (ARC 1) => 16 |  _ => go (0,a))
  | 16 => (case a of XXXntest => 20 | XXXtest => 17 |  _ => go (0,a))
  | 17 => (case a of  _ => go (0,a))
  | 18 => (case a of XXXlocation => 21 | NAME => 19 |  _ => go (0,a))
  | 19 => (case a of  _ => go (0,a))
  | 20 => (case a of  _ => go (0,a))
  | 21 => (case a of  _ => go (0,a))
  | 22 => (case a of (ARC 2) => 25 | (ARC 1) => 23 |  _ => go (0,a))
  | 23 => (case a of XXXdestination => 92 | TEMP => 24 |  _ => go (0,a))
  | 24 => (case a of  _ => go (0,a))
  | 25 => (case a of XXXzero => 103 | OP => 94 | XXXreg => 93 | XXXcomputation => 26 |  _ => go (0,a))
  | 26 => (case a of  _ => go (0,a))
  | 27 => (case a of (ARC 3) => 32 | (ARC 2) => 30 | (ARC 1) => 28 |  _ => go (0,a))
  | 28 => (case a of XXXrelop => 84 | XXXbinop => 65 | PLUS => 29 |  _ => go (0,a))
  | 29 => (case a of  _ => go (0,a))
  | 30 => (case a of NAME => 90 | XXXstm => 86 | XXXoperand => 66 | OP => 55 | XXXlocation => 47 | XXXreg => 34 | XXXname => 31 |  _ => go (0,a))
  | 31 => (case a of  _ => go (0,a))
  | 32 => (case a of CONST => 91 | XXXzero => 85 | XXXoperand => 67 | XXXlocation => 62 | OP => 48 | XXXname => 35 | XXXreg => 33 |  _ => go (0,a))
  | 33 => (case a of  _ => go (0,a))
  | 34 => (case a of  _ => go (0,a))
  | 35 => (case a of  _ => go (0,a))
  | 36 => (case a of (ARC 1) => 37 |  _ => go (0,a))
  | 37 => (case a of XXXioperand => 64 | XXXlocation => 63 | OP => 38 |  _ => go (0,a))
  | 38 => (case a of (ARC 3) => 43 | (ARC 2) => 41 | (ARC 1) => 39 |  _ => go (27,a))
  | 39 => (case a of PLUS => 40 |  _ => go (28,a))
  | 40 => (case a of  _ => go (29,a))
  | 41 => (case a of XXXreg => 45 | XXXname => 42 |  _ => go (30,a))
  | 42 => (case a of  _ => go (31,a))
  | 43 => (case a of XXXname => 46 | XXXreg => 44 |  _ => go (32,a))
  | 44 => (case a of  _ => go (33,a))
  | 45 => (case a of  _ => go (34,a))
  | 46 => (case a of  _ => go (35,a))
  | 47 => (case a of  _ => go (0,a))
  | 48 => (case a of (ARC 3) => 53 | (ARC 2) => 51 | (ARC 1) => 49 |  _ => go (27,a))
  | 49 => (case a of MUL => 50 |  _ => go (28,a))
  | 50 => (case a of  _ => go (0,a))
  | 51 => (case a of XXXreg => 52 |  _ => go (30,a))
  | 52 => (case a of  _ => go (34,a))
  | 53 => (case a of CONST => 54 |  _ => go (32,a))
  | 54 => (case a of  _ => go (91,a))
  | 55 => (case a of (ARC 3) => 60 | (ARC 2) => 58 | (ARC 1) => 56 |  _ => go (27,a))
  | 56 => (case a of MUL => 57 |  _ => go (28,a))
  | 57 => (case a of  _ => go (0,a))
  | 58 => (case a of XXXreg => 59 |  _ => go (30,a))
  | 59 => (case a of  _ => go (34,a))
  | 60 => (case a of CONST => 61 |  _ => go (32,a))
  | 61 => (case a of  _ => go (91,a))
  | 62 => (case a of  _ => go (0,a))
  | 63 => (case a of  _ => go (0,a))
  | 64 => (case a of  _ => go (0,a))
  | 65 => (case a of  _ => go (0,a))
  | 66 => (case a of  _ => go (0,a))
  | 67 => (case a of  _ => go (0,a))
  | 68 => (case a of (ARC 2) => 71 | (ARC 1) => 69 |  _ => go (0,a))
  | 69 => (case a of XXXcvtop => 73 | XXXunop => 70 |  _ => go (0,a))
  | 70 => (case a of  _ => go (0,a))
  | 71 => (case a of XXXoperand => 72 |  _ => go (0,a))
  | 72 => (case a of  _ => go (0,a))
  | 73 => (case a of  _ => go (0,a))
  | 74 => (case a of (ARC 2) => 77 | (ARC 1) => 75 |  _ => go (0,a))
  | 75 => (case a of XXXntest => 76 |  _ => go (0,a))
  | 76 => (case a of  _ => go (0,a))
  | 77 => (case a of XXXntest => 79 | XXXtest => 78 |  _ => go (0,a))
  | 78 => (case a of  _ => go (0,a))
  | 79 => (case a of  _ => go (0,a))
  | 80 => (case a of (ARC 1) => 81 |  _ => go (0,a))
  | 81 => (case a of XXXtest => 83 | XXXntest => 82 |  _ => go (0,a))
  | 82 => (case a of  _ => go (0,a))
  | 83 => (case a of  _ => go (0,a))
  | 84 => (case a of  _ => go (0,a))
  | 85 => (case a of  _ => go (0,a))
  | 86 => (case a of  _ => go (0,a))
  | 87 => (case a of (ARC 1) => 88 |  _ => go (0,a))
  | 88 => (case a of XXXtest => 89 |  _ => go (0,a))
  | 89 => (case a of  _ => go (0,a))
  | 90 => (case a of  _ => go (0,a))
  | 91 => (case a of  _ => go (0,a))
  | 92 => (case a of  _ => go (0,a))
  | 93 => (case a of  _ => go (0,a))
  | 94 => (case a of (ARC 3) => 99 | (ARC 2) => 97 | (ARC 1) => 95 |  _ => go (27,a))
  | 95 => (case a of PLUS => 101 | XXXbinop => 96 |  _ => go (28,a))
  | 96 => (case a of  _ => go (65,a))
  | 97 => (case a of XXXoperand => 98 |  _ => go (30,a))
  | 98 => (case a of  _ => go (66,a))
  | 99 => (case a of CONST => 102 | XXXoperand => 100 |  _ => go (32,a))
  | 100 => (case a of  _ => go (67,a))
  | 101 => (case a of  _ => go (29,a))
  | 102 => (case a of  _ => go (91,a))
  | 103 => (case a of  _ => go (0,a))
  | 104 => (case a of (ARC 1) => 105 |  _ => go (0,a))
  | 105 => (case a of XXXreg => 107 | XXXresult => 106 |  _ => go (0,a))
  | 106 => (case a of  _ => go (0,a))
  | 107 => (case a of  _ => go (0,a))
  | 108 => (case a of (ARC 2) => 111 | (ARC 1) => 109 |  _ => go (0,a))
  | 109 => (case a of XXXargs => 110 |  _ => go (0,a))
  | 110 => (case a of  _ => go (0,a))
  | 111 => (case a of XXXlocation => 112 |  _ => go (0,a))
  | 112 => (case a of  _ => go (0,a))
  | 113 => (case a of (ARC 2) => 116 | (ARC 1) => 114 |  _ => go (0,a))
  | 114 => (case a of XXXoperand => 115 |  _ => go (0,a))
  | 115 => (case a of  _ => go (0,a))
  | 116 => (case a of XXXargs => 117 |  _ => go (0,a))
  | 117 => (case a of  _ => go (0,a))
  | 118 => (case a of (ARC 2) => 121 | (ARC 1) => 119 |  _ => go (0,a))
  | 119 => (case a of XXXstm => 120 |  _ => go (0,a))
  | 120 => (case a of  _ => go (0,a))
  | 121 => (case a of XXXreg => 122 |  _ => go (0,a))
  | 122 => (case a of  _ => go (0,a))
  | _ => 0

val go_f = get_finals o go
fun childsymbol s = ARC s
val initialstate = 0
type state = int
datatype matchtree = Chain of int * symbol * matchtree list
fun unitmatches nt = (case nt of
NOARGS => [Chain (84,XXXargs,[])]
  | XXXresult => [Chain (81,XXXreg,[Chain (24,XXXoperand,[Chain (28,XXXcomputation,[]),Chain (7,XXXstm,[])]),Chain (12,XXXlocation,[Chain (32,XXXcomputation,[])])])]
  | NAME => [Chain (68,XXXname,[Chain (25,XXXoperand,[Chain (28,XXXcomputation,[Chain (9,XXXreg,[Chain (12,XXXlocation,[])])]),Chain (7,XXXstm,[])]),Chain (17,XXXlocation,[Chain (32,XXXcomputation,[Chain (9,XXXreg,[Chain (24,XXXoperand,[Chain (7,XXXstm,[])])])])])])]
  | CVTUS => [Chain (66,XXXcvtopu,[])]
  | CVTUU => [Chain (65,XXXcvtopu,[])]
  | CVTSU => [Chain (64,XXXcvtopu,[])]
  | CVTSS => [Chain (63,XXXcvtop,[])]
  | UGEQ => [Chain (62,XXXrelop,[])]
  | UGT => [Chain (61,XXXrelop,[])]
  | GEQ => [Chain (60,XXXrelop,[])]
  | GT => [Chain (59,XXXrelop,[])]
  | ULEQ => [Chain (58,XXXrelop,[])]
  | ULT => [Chain (57,XXXrelop,[])]
  | LEQ => [Chain (56,XXXrelop,[])]
  | LT => [Chain (55,XXXrelop,[])]
  | NEQ => [Chain (54,XXXrelop,[])]
  | EQ => [Chain (53,XXXrelop,[])]
  | AND => [Chain (52,XXXbinop,[])]
  | XOR => [Chain (51,XXXbinop,[])]
  | OR => [Chain (50,XXXbinop,[])]
  | DIV => [Chain (49,XXXbinop,[])]
  | MUL => [Chain (48,XXXbinop,[])]
  | MINUS => [Chain (47,XXXbinop,[])]
  | PLUS => [Chain (46,XXXbinop,[])]
  | COMP => [Chain (45,XXXunop,[])]
  | NEG => [Chain (44,XXXunop,[])]
  | XXXflag => [Chain (39,XXXtest,[]),Chain (38,XXXntest,[])]
  | XXXioperand => [Chain (33,XXXcomputation,[Chain (9,XXXreg,[Chain (24,XXXoperand,[Chain (7,XXXstm,[])]),Chain (12,XXXlocation,[])])])]
  | XXXlocation => [Chain (32,XXXcomputation,[Chain (9,XXXreg,[Chain (24,XXXoperand,[Chain (7,XXXstm,[])])])])]
  | XXXdestination => [Chain (27,XXXoperand,[Chain (28,XXXcomputation,[Chain (9,XXXreg,[Chain (12,XXXlocation,[])])]),Chain (7,XXXstm,[])])]
  | CONST => [Chain (85,XXXzero,[]),Chain (67,XXXname,[Chain (25,XXXoperand,[Chain (28,XXXcomputation,[Chain (9,XXXreg,[Chain (12,XXXlocation,[])])]),Chain (7,XXXstm,[])]),Chain (17,XXXlocation,[Chain (32,XXXcomputation,[Chain (9,XXXreg,[Chain (24,XXXoperand,[Chain (7,XXXstm,[])])])])])]),Chain (26,XXXoperand,[Chain (28,XXXcomputation,[Chain (9,XXXreg,[Chain (12,XXXlocation,[])])]),Chain (7,XXXstm,[])])]
  | XXXname => [Chain (25,XXXoperand,[Chain (28,XXXcomputation,[Chain (9,XXXreg,[Chain (12,XXXlocation,[])])]),Chain (7,XXXstm,[])]),Chain (17,XXXlocation,[Chain (32,XXXcomputation,[Chain (9,XXXreg,[Chain (24,XXXoperand,[Chain (7,XXXstm,[])])])])])]
  | XXXreg => [Chain (24,XXXoperand,[Chain (28,XXXcomputation,[]),Chain (7,XXXstm,[])]),Chain (12,XXXlocation,[Chain (32,XXXcomputation,[])])]
  | TEMP => [Chain (11,XXXreg,[Chain (24,XXXoperand,[Chain (28,XXXcomputation,[]),Chain (7,XXXstm,[])]),Chain (12,XXXlocation,[Chain (32,XXXcomputation,[])])])]
  | XXXcomputation => [Chain (9,XXXreg,[Chain (24,XXXoperand,[Chain (7,XXXstm,[])]),Chain (12,XXXlocation,[])])]
  | XXXbigval => [Chain (8,XXXstm,[])]
  | XXXoperand => [Chain (28,XXXcomputation,[Chain (9,XXXreg,[Chain (12,XXXlocation,[])])]),Chain (7,XXXstm,[])]
  | LABEL => [Chain (2,XXXstm,[])]
  | _ => [])

fun rewriterule (r:rule) =
 case r of
_ => false
fun getreplacement (XXXrewrite t) = t | getreplacement _ = raise InternalError "problem with rewrite 996"
  end
structure Internal = MAKEtreeprocessor(Specification)
exception NoCover = Internal.NoCover
exception InternalError = Internal.InternalError
val translate = Internal.translate
end;
