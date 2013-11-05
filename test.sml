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


(*Exceptions *)
exception Unmatchable;
exception Undefined;

fun reduce (f, []) = raise Unmatchable |
    reduce (f, a::z) = foldl f a z;

fun pairWise (a::[],b::[]) = (a,b) :: [] |
    pairWise([], _) = raise Unmatchable |
    pairWise(_, []) = raise Unmatchable |
    pairWise(a::alist, b::blist) = (a,b) :: pairWise(alist,blist)
	;

(*Find most lenient Type for a pattern implementation*)
fun matchPatternWithType (Wildcard,_) = 1 |
    matchPatternWithType (Variable(_),_) = 1 |
    matchPatternWithType (UnitP, UnitT) = 1 |
    matchPatternWithType (ConstP(_), IntT) = 1|
    matchPatternWithType (TupleP(p), TupleT(t)) =  
       reduce((fn (a,b)=>a*b), (map matchPatternWithType (pairWise(p,t))) )
    |matchPatternWithType(ConstructorP(s,p),Datatype(sprime)) = if(s=sprime) then 1 else raise Unmatchable
    |matchPatternWithType(_,_) = raise Unmatchable;
 
fun most_lenient_type (Wildcard,_) = Anything|
    most_lenient_type (Variable(_),_) = Anything|
    most_lenient_type (UnitP,_) = UnitT|
    most_lenient_type (ConstP(_),_) = IntT|
    most_lenient_type (TupleP(patternL),definedTypes) = 
    let 
	fun f (x) = most_lenient_type (x, definedTypes);
	val mappingResults = map f patternL;
    in
	TupleT(mappingResults)
    end|
    most_lenient_type (ConstructorP(s,p),definedTypes) = 
     let
	 val intm = List.find (fn(cN,xdd,ydd) => cN=s) definedTypes
	 val inputType =  ((fn (SOME(x,y,z)) => z | NONE => raise Unmatchable) intm);
	 val dataTypeName =  ((fn (SOME(x,y,z)) => y | NONE => raise Unmatchable) intm);
	 val pattern_matched  =  matchPatternWithType (p,inputType)
     in     
	 if(pattern_matched = 1) then  
		Datatype(dataTypeName)
	else
	    raise Unmatchable
     end
;

(* combine most lenient types into single most lenient type*)
fun combineLenientTypeInternal(Anything,b) = b |
    combineLenientTypeInternal(Datatype(s),Datatype(sd)) = if(s = sd) then Datatype(s) else raise Unmatchable |
    combineLenientTypeInternal(UnitT,UnitT) = UnitT |
    combineLenientTypeInternal(IntT,IntT) = IntT |
    combineLenientTypeInternal(_) = raise Unmatchable;


fun combineLenientType (TupleT(xlist),  TupleT(ylist))  = 
TupleT((map combineLenientType (pairWise(xlist,ylist))))
|

combineLenientType (a, b)  = 
let
val combined =  combineLenientTypeInternal(a, b)  
in
 combined
end
handle Unmatchable => combineLenientTypeInternal(b, a)  
;

(* All in *)

fun only_capitals l = (List.filter (fn (s) => (s <> "" andalso Char.isUpper(String.sub(s,0)))) l);
fun longest_string1 l = (List.foldl (fn (a,b) => if String.size(a) > String.size(b) then a else b) "" l);
fun longest_string2 l = (List.foldl (fn (a,b) => if String.size(a) >= String.size(b) then a else b) "" l);

fun typecheck_pattern plist tlist  = let
    fun f(p) = most_lenient_type(p,tlist)
    in
    SOME (reduce(combineLenientType,(map (fn (x) => most_lenient_type(x,tlist)) plist)))
    end
    handle Unmatchable => NONE;

