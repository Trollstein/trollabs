(* Coursera Programming Languages, Homework 3, Provided Code *)

exception NoAnswer

datatype pattern = Wildcard
		 | Variable of string
		 | UnitP
		 | ConstP of int
		 | TupleP of pattern list
		 | ConstructorP of string * pattern

datatype valu = Const of int
	      | Unit
	      | Tuple of valu list
	      | Constructor of string * valu

fun g f1 f2 p =
    let
	val r = g f1 f2
    in
	case p of
	    Wildcard          => f1 ()
	  | Variable x        => f2 x
	  | TupleP ps         => List.foldl (fn (p,i) => (r p) + i) 0 ps
	  | ConstructorP(_,p) => r p
	  | _                 => 0
    end

(**** for the challenge problem only ****)

datatype typ = Anything
	     | UnitT
	     | IntT
	     | TupleT of typ list
	     | Datatype of string

(**** you can put all your code here ****)

fun curry f x y = f (x, y)
fun uncurry f (x, y) = f x y
fun flip f x y = f y x
val flipCurry = fn f => flip (curry f)
fun makeTuple fst x = (fst, x)
val mapTuple = fn fst => List.map (makeTuple fst)
fun someify (x, y) = (SOME x, SOME y)
fun all_or_none_option f xs  = SOME (List.map (valOf o f) xs) handle Option => NONE
fun foldl_option f init [] = SOME init
|   foldl_option f init (x::xs) = case f (x, init) of
                                    NONE => NONE
                                  | SOME acc => foldl_option f acc xs

val only_capitals = List.filter (Char.isUpper o flipCurry String.sub 0)

val longest_string1 = List.foldl
  (fn (i, acc) => if String.size acc >= String.size i then acc else i) ""

val longest_string2 = List.foldl (fn (i, acc) => if String.size acc > String.size i then acc else i) ""

fun longest_string_helper (f : int * int -> bool) =
  List.foldl (fn (i, acc) => if f (String.size i, String.size acc) then i else acc) ""

val longest_string3 = longest_string_helper (fn (x, y) => x > y)

val longest_string4 = longest_string_helper (fn (x, y) => x >= y)

val longest_capitalized = longest_string1 o only_capitals

val rev_string = implode o List.rev o explode

fun first_answer f [] = raise NoAnswer
|   first_answer f (x::xs) = case (f x) of
                              NONE => first_answer f xs
                            | SOME v => v
fun all_answers f xs = (SOME o List.concat o (List.map (valOf o f))) xs
                                  handle Option => NONE
fun const a b = a

val count_wildcards = g (const 1) (const 0)

val count_wild_and_variable_lengths = g (const 1) String.size

fun count_some_var (name, p) = g (const 0) (fn var => if (name = var) then 1 else 0) p

fun check_pat p =
  let fun var_names (Variable x) = [x]
      |   var_names (ConstructorP(_, p)) = var_names p
      |   var_names (TupleP ps) = List.foldl (fn (p,acc) => (var_names p) @ acc) [] ps
      |   var_names _ = []
      fun repeats [] = false
      |   repeats (x::xs) = List.exists (fn a => a = x) xs orelse repeats xs
  in
    (not o repeats o var_names) p
  end

fun match (_, Wildcard) = SOME []
|   match (v, Variable s) = SOME [(s, v)]
|   match (Unit, UnitP) = SOME []
|   match (Const x, ConstP y) = if x = y then SOME [] else NONE
|   match (Constructor (n, v), ConstructorP (np, p)) =
      if n = np then match (v, p) else NONE
|   match (Tuple vs, TupleP ps) =
      let
        val result = all_answers match (ListPair.zipEq (vs, ps)) handle UnequalLengths => NONE
      in  result
      end
|   match (_, _) = NONE

fun first_match valu ps = (SOME o (first_answer match) o (mapTuple valu)) ps
                                handle NoAnswer => NONE


exception InvalidConstructor

Anything (non-nullable)
Nullable<Anything>
null - Null
int
long

unify(Nullable(Anything), y) =


fun typecheck_patterns (ds, ps) =
  let
    fun unify (x, y) =
      let
        fun score Anything = 1
        |   score UnitT = 2
        |   score IntT = 3
        |   score (Datatype _) = 4
        |   score (TupleT _) = 5
        val (sx, sy) = (score x, score y)
        fun unify_int (Anything, y) = SOME y
        |   unify_int (UnitT, UnitT) = SOME UnitT
        |   unify_int (UnitT, _) = NONE
        |   unify_int (IntT, IntT) = SOME IntT
        |   unify_int (IntT, _) = NONE
        |   unify_int (Datatype d1, Datatype d2) = if d1 = d2 then SOME (Datatype d1) else NONE
        |   unify_int (Datatype _, _) = NONE
        |   unify_int (TupleT ts1, TupleT ts2) =
            Option.map TupleT (all_or_none_option unify (ListPair.zipEq (ts1, ts2)))
                  handle UnequalLengths => NONE
      in
        if sx < sy
        then unify_int (x, y)
        else unify_int (y, x)
      end
    fun same_constructor (name, inner_type) (n, _, dtype) = name = n andalso isSome (unify (dtype, inner_type))
    fun pattern_type (_, UnitP) = UnitT
    |   pattern_type (_, ConstP x) = IntT
    |   pattern_type (_, Wildcard) = Anything
    |   pattern_type (_, Variable x) = Anything
    |   pattern_type (ds, TupleP ps) = TupleT (List.map pattern_type (mapTuple ds ps))
    |   pattern_type ([], ConstructorP (name, p)) = raise InvalidConstructor
    |   pattern_type (ds, ConstructorP (name, p)) =
                case List.find (same_constructor (name, pattern_type (ds, p))) ds of
                    NONE => raise InvalidConstructor
                  | SOME (_, tname, _) => Datatype tname
in
  foldl_option unify Anything (List.map (pattern_type o (makeTuple ds)) ps)
    handle InvalidConstructor => NONE
end

