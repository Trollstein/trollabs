(* Datatypes *)
datatype pattern = Wildcard | Variable of string | UnitP | ConstP of int
| TupleP of pattern list | ConstructorP of string * pattern;

datatype typ = Anything (* any type of value is okay, the Anons *)
| UnitT (* type for Unit *)
| IntT (* type for integers *)
| TupleT of typ list (* tuple types *)
| Datatype of string (* some named datatype also called as Namefags/ Tripfags in 4chanese *);

datatype result = NONE |
		  SOME of typ
;

(*Exceptions *)
exception Unmatchable;
exception Undefined;

(*Utility functions*)
fun map (f, []) = []
| map (f, (a::l)) = (f a)::(map (f, l));

fun reduce(f, []) = raise Unmatchable |
    reduce(f, a::[]) = a |
    reduce(f, a::(b::l)) = reduce(f , f(a,b)::l); 

fun findWithFunction (f,[],a) = raise Unmatchable |
    findWithFunction (f,b::l,a) = if f(b,a) then b else findWithFunction(f,l,a); 				

fun find ([],a) = raise Unmatchable |
    find (a::l,b) = if(a=b) then a else find(l,b);

(*Find most lenient Type for a pattern implementation*)
fun matchPatternWithType (Wildcard,Anything) = 1 |
    matchPatternWithType (UnitP, UnitT) = 1 |
    matchPatternWithType (ConstP(_), IntT) = 1|
    matchPatternWithType (TupleP(p), TupleT(t)) =  
    let

	fun f (a::[],b::[]) = (a,b) :: [] |
            f([], _) = raise Unmatchable |
            f(_, []) = raise Unmatchable |
            f(a::alist, b::blist) = (a,b) :: f(alist,blist)
	;
	fun g(a,b) = a * b;
	in
        reduce(g, map(matchPatternWithType,f(p,t)) )
    end
    |matchPatternWithType(ConstructorP(s,p),Datatype(sprime)) = if(s=sprime) then 1 else raise Unmatchable
    |matchPatternWithType(_,_) = raise Unmatchable;
 
fun most_lenient_type (Wildcard,_) = Anything|
    most_lenient_type (Variable(_),_) = Anything|
    most_lenient_type (UnitP,_) = UnitT|
    most_lenient_type (ConstP(_),_) = IntT|
    most_lenient_type (TupleP(patternL),definedTypes) = 
    let 
	fun f (x) = most_lenient_type (x, definedTypes);
	val mappingResults = map(f,patternL);
    in
	TupleT(mappingResults)
    end|
    most_lenient_type (ConstructorP(s,p),definedTypes) = 
     let
	 fun f((cN,_,_),c) = (cN = c);
	 val (cName, tName, inputType) = findWithFunction(f,definedTypes,s);
	 val pattern_matched  =  matchPatternWithType (p,inputType);
     in     
	 if(pattern_matched = 1) then  
		Datatype(cName)
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


fun combineLenientType(TupleT(xlist), TupleT(ylist)) = let

fun f([], []) = [] |
    f(a::alist, b::blist) = (a,b) :: f(alist,blist) |
    f(_,_) = raise Unmatchable;

in
TupleT(map( combineLenientType, f(xlist,ylist)))
end |

combineLenientType(a,b) = 
let
val combined =  combineLenientTypeInternal(a,b); 
in
 combined
end
handle Unmatchable => combineLenientTypeInternal(b,a) 
;

(* All in *)
fun findMostLenientTypeFor(plist,tlist) = let
    fun f(p) = most_lenient_type(p,tlist)
    in
    SOME(reduce(combineLenientType,map(f, plist)))
    end
    handle Unmatchable => NONE;

