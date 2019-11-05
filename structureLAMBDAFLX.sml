use "signatureLAMBDAFLX.sml";

structure LambdaFlx : LAMBDAFLX =
  	struct

  		(*define all exception*)
	   	exception Not_wellformed;
	    exception Not_nf;
	    exception Not_int;
	    exception Not_welltyped;

	    (*define datatype*)
    	datatype lterm = term (* term from FLX *)
			| VAR of string      (* variables *)
			| Z                  (* zero *)
			| T                  (* true *)
			| F                  (* false *)
			| P of lterm         (* Predecessor *)
			| S of lterm         (* Successor *)
			| ITE of lterm * lterm * lterm       (* If then else *)
			| IZ of lterm        (* is zero *)
			| GTZ of lterm       (* is greater than zero *)
			| LAMBDA of lterm * lterm    (* lambda x [lterm] *)
			| APP of lterm * lterm       (* application of lambda terms, i.e. (L M) *)


	    (*fun fromString s = Z*)
	    (*fun toString t = "a"*)
	    (*fun fromInt n = Z*)
	    (*fun toInt t = 1*)
	    (*fun isWellTyped t = true*)
	    (*fun betanf t = t*)


		(*convert lterm to string*)
		fun toString (VAR x) = x
			| toString Z = "Z"
			| toString T = "T"
			| toString F = "F"
			| toString (S t) = "(S " ^ toString(t) ^ ")"
			| toString (P t) = "(P " ^ toString(t) ^ ")"
			| toString (ITE(b, x, y)) = "(ITE <" ^ toString(b) ^ "," ^ toString(x) ^ "," ^toString(y) ^ ">)"
			| toString(IZ t) = "(IZ " ^ toString(t) ^ ")"
			| toString(GTZ t) = "(GTZ " ^ toString(t) ^ ")"
			| toString(LAMBDA(t1, t2)) = "LAMBDA " ^ toString(t1) ^ "[" ^ toString(t2) ^ "]"
			| toString(APP(t1, t2)) = "(" ^ toString(t1) ^ " " ^ toString(t2) ^ ")"


		(*convert integer to term*)
		fun fromInt 0 = Z
			| fromInt n = 
				if(n > 0) then S(fromInt (n-1))
				else P(fromInt (n+1))



		(*check for valid nf integer start at S*)
		fun isIntegerS Z = true
			| isIntegerS (S n) = isIntegerS n
			| isIntegerS t = false

		(*check for valid nf integer start at P*)
		fun isIntegerP Z = true
			| isIntegerP (P n) = isIntegerP n
			| isIntegerP t = false

		(*check for valid nf integer*)
		fun isInteger Z = true
			| isInteger (S n) = isIntegerS (S n)
			| isInteger (P n) = isIntegerP(P n)
			| isInteger t = false

		(*check for valid integer not necessary nf*)
		fun isInt Z = true
			| isInt (S n) = isInt n
			| isInt (P n) = isInt n
			| isInt (ITE(b, x, y)) = 
				if isInt(x) andalso isInt(y) then true else false
			| isInt t = false


		(*convert term to integer*)
		fun toInt Z = 0
			| toInt (S (P t:lterm)) = if(isInt t) then raise Not_nf else raise Not_int
			| toInt (P (S t:lterm)) = if(isInt t) then raise Not_nf else raise Not_int
			| toInt (S t:lterm) = if(isInt t) then (1 + toInt(t)) else raise Not_int
			| toInt (P t:lterm) = if(isInt t) then (~1 + toInt(t)) else raise Not_int
			| toInt n  = raise Not_int


		(*output term1/term2 of ite*)
		fun scan1([], bc, term_string) = raise Not_wellformed
			| scan1(l as h::t, bc, term_string) = 
				if(h = #"," andalso bc = 0 andalso term_string<> []) then ( String.implode(List.rev(term_string)), t)
				else if(h = #"," andalso bc = 0 andalso term_string =  []) then raise Not_wellformed
				else if(h = #"(") then scan1(t, bc+1, h::term_string)
				else if(h = #")") then scan1(t, bc-1, h::term_string)
				else scan1(t, bc, h::term_string)

		(*output term3 of ite*)
		fun scan3([], bc, []) = raise Not_wellformed
			| scan3([], bc, term_string as a::b) = if (bc = 0) then String.implode(List.rev(term_string)) else raise Not_wellformed
			| scan3(l as h::t, bc, term_string) = 
				if(h = #"(") then scan3(t, bc+1, h::term_string)
				else if(h = #")") then scan3(t, bc-1, h::term_string)
				else scan3(t, bc, h::term_string)

		fun scanLamda1([], term_string) = raise Not_wellformed
			| scanLamda1(l as h::t, term_string) = 
				if (h = #"[") then (String.implode(List.rev(term_string)), t)
				else scanLamda1(t, h::term_string)

		fun scanLamda2([], []) = raise Not_wellformed
			| scanLamda2([], term_string) = String.implode(List.rev(term_string))
			| scanLamda2(l as h::t, term_string) = 
				scanLamda2(t, h::term_string)

		(*output term1 of app*)
		fun scanApp1([], bc, term_string) = raise Not_wellformed
			| scanApp1(l as h::t, bc, term_string) = 
				if(h = #" " andalso bc = 0 andalso term_string<> []) then ( String.implode(List.rev(term_string)), t)
				else if(h = #" " andalso bc = 0 andalso term_string =  []) then raise Not_wellformed
				else if(h = #"(") then scanApp1(t, bc+1, h::term_string)
				else if(h = #")") then scanApp1(t, bc-1, h::term_string)
				else scanApp1(t, bc, h::term_string)

		fun scanApp2([], bc, []) = raise Not_wellformed
			| scanApp2([], bc, term_string as a::b) = if (bc = 0) then String.implode(List.rev(term_string)) else raise Not_wellformed
			| scanApp2(l as h::t, bc, term_string) = 
				if(h = #"(") then scanApp2(t, bc+1, h::term_string)
				else if(h = #")") then scanApp2(t, bc-1, h::term_string)
				else scanApp2(t, bc, h::term_string)

		fun scanAppLambda1([], term_string) = raise Not_wellformed
			| scanAppLambda1(l as h::t, term_string) = 
				if (h = #"[") then (String.implode(List.rev(term_string)), l)
				else scanAppLambda1(t, h::term_string)

		fun scanAppLambda2([], sc , term_string) = raise Not_wellformed
			| scanAppLambda2(l as h::t, sc, term_string) = 
				if(h = #" " andalso sc = 0 andalso term_string<> []) then ( String.implode(List.rev(term_string)), t)
				else if(h = #" " andalso sc = 0 andalso term_string =  []) then raise Not_wellformed
				else if(h = #"[") then scanAppLambda2(t, sc+1, h::term_string)
				else if(h = #"]") then scanAppLambda2(t, sc-1, h::term_string)
				else scanAppLambda2(t, sc, h::term_string)

		(*convert input string to term*)
		fun fromString "" = raise Not_wellformed
			| fromString "Z" = Z
			| fromString "T" = T
			| fromString "F" = F
			| fromString s = 
				if(String.isPrefix (" ") s) then fromString(String.substring(s, 1, (String.size s) - 1) )
				else if(String.isPrefix ("(S ") s  andalso String.isSuffix (")") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 4;
						val start_index = 3;
						val remaining_str = String.substring(s, start_index, remaining_len);
					in
						(S (fromString(remaining_str)))
					end

				else if(String.isPrefix ("(P ") s  andalso String.isSuffix (")") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 4;
						val start_index = 3;
						val remaining_str = String.substring(s, start_index, remaining_len);
					in
						(P (fromString(remaining_str)))
					end

				else if(String.isPrefix ("(IZ ") s  andalso String.isSuffix (")") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 5;
						val start_index = 4;
						val remaining_str = String.substring(s, start_index, remaining_len);
					in
						(IZ (fromString(remaining_str)))
					end

				else if(String.isPrefix ("(GTZ ") s  andalso String.isSuffix (")") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 6;
						val start_index = 5;
						val remaining_str = String.substring(s, start_index, remaining_len);
					in
						(GTZ (fromString(remaining_str)))
					end

				else if(String.isPrefix ("(ITE <") s  andalso String.isSuffix (">)") s ) then
					let

						val s_len = String.size s;
						val remaining_len = s_len - 8;
						val start_index = 6;
						val remaining_str = String.substring(s, start_index, remaining_len);


						val (term1_string, r1) = scan1( String.explode(remaining_str), 0, []);
						val (term2_string, r2) = scan1( r1, 0, []);
						val term3_string = scan3( r2, 0, []);

						val t1_term = fromString(term1_string);
						val t2_term = fromString(term2_string);
						val t3_term = fromString(term3_string);


					in
						(ITE(t1_term,t2_term,t3_term))
					end
				else if(String.isPrefix ("LAMBDA ") s  andalso String.isSuffix ("]") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 8;
						val start_index = 7;
						val remaining_str = String.substring(s, start_index, remaining_len);

						val (term1_string, r1) = scanLamda1( String.explode(remaining_str), [])
						val term2_string = scanLamda2(r1, [])

						val t1_term = fromString(term1_string)
						val t2_term = fromString(term2_string)


					in
						(*LAMBDA(t1_term, t2_term)*)
						(case t1_term of
							(VAR x) => LAMBDA(t1_term, t2_term)
							| _ => raise Not_wellformed
						)
					end
				else if(String.isPrefix ("(LAMBDA ") s  andalso String.isSuffix (")") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 9;
						val start_index = 8;
						val remaining_str = String.substring(s, start_index, remaining_len);

						val (term1_string, r1) = scanAppLambda1( String.explode(remaining_str), []);
						val (term2_string, r2) = scanAppLambda2( r1, 0, []);

						val term2_string = String.substring(term2_string, 1, (String.size term2_string)-2);

						val term3_string = String.implode(r2);

						val term1 = fromString(term1_string);
						val term2 = fromString(term2_string);
						val term3 = fromString(term3_string);

					in
						(case term1 of
							(VAR x) => APP(LAMBDA(term1, term2), term3)
							| _ => raise Not_wellformed
						)
						(*APP(LAMBDA(term1, term2), term3)*)
					end

				else if(String.isPrefix ("(") s  andalso String.isSuffix (")") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 2; 
						val start_index = 1;

						(*remove start/end bracket*)
						val remaining_str = String.substring(s, start_index, remaining_len); 

						(*logic: (t1 t2)::  removed "(" and ")"  
							scan t1 such that bracket count=0 and next char is "space"
							scan t2 such that bracket count=0 and input exhausted"
						*)

						val (term1_string, r1) = scanApp1(String.explode(remaining_str), 0, [])
						val term2_string = scanApp2(r1, 0, [])

						val t1_term = fromString(term1_string);
						val t2_term = fromString(term2_string);
					in
						APP(t1_term, t2_term)
					end


				else if(List.all Char.isLower (explode s)) then
					VAR(s)
				else raise  Not_wellformed


		(*fun isReallyBool T = true
			| isReallyBool F = true
			| isReallyBool (IZ n) = if (isReallyInteger n) then true else false
			| isReallyBool (GTZ n) = if (isReallyInteger n) then true else false
			| isReallyBool (ITE(b, x, y)) = 
				if isReallyBool(b) andalso isReallyBool(x) andalso isReallyBool(y) then true
				else false
			| isReallyBool _ = false*)

		fun isBool T = true
			| isBool F = true
			| isBool (IZ n) = if (isInt n) then true else false
			| isBool (GTZ n) = if (isInt n) then true else false
			| isBool (ITE(b, x, y)) = 
				if isBool(b) andalso isBool(x) andalso isBool(y) then true
				else false
			| isBool _ = false


		fun delete (_, []) = []
			| delete (x, y::t) =
				if x = y then delete (x, t)
				else y::(delete (x, t))

		fun belongs (x, []) = false
			| belongs (x, y::t) = 
				if x = y then true else (belongs (x, t))

		fun fv (VAR x) = [x]
			| fv T = []
			| fv F = []
			| fv Z = []
			| fv (P t) = fv t
			| fv (S t) = fv t
			| fv (ITE(b, x, y)) = (fv b)@(fv x)@(fv y)
			| fv (IZ t) = fv t
			| fv (GTZ t) = fv t
			| fv (LAMBDA (VAR x, M)) = delete (x, fv M)
			| fv (LAMBDA (_, M)) = raise Not_wellformed
			| fv (APP (L, M)) = (fv L)@(fv M)

			
		fun isfreein (x, L) = belongs (x, fv L)


		(*subst e x v  : e[v/x] where x is free in v*)
		fun subst (LAMBDA(y, e), x, v) = 
			if x = y then (LAMBDA(y, e))
			else
				let
				 	val e' = subst(e, x, v)
				 in
				 	(LAMBDA(y, e'))
				 end 
			| subst ((VAR y), x, v) = if x = (VAR y) then v else (VAR y)
			| subst ((APP (e1, e2)), x, v) = (APP(subst(e1, x, v), subst (e2, x, v)))
			| subst ((S e), x, v) = (S (subst(e, x, v)))
			| subst ((P e), x, v) = (P (subst(e, x, v)))
			| subst ((IZ e), x, v) = (IZ (subst(e, x, v)))
			| subst ((GTZ e), x, v) = (GTZ (subst(e, x, v)))
			| subst ((ITE(e1, e2, e3)), x, v) = (ITE(subst(e1, x, v), subst(e2, x, v), subst(e3, x, v)))
			| subst (e, x, v) = e

			 (*one leftmost beta step*)
		
		fun eval (APP (LAMBDA (x, e), v)) = subst (e, x, v)
			| eval (APP(APP(e1, e2) , v)) = 
				let 
					val e = eval (APP (e1, e2)); 
				in 
					(APP (e, v)) 
				end
			| eval n = n

				(*beta until a value is obtained*)
		fun beta (LAMBDA (x, e)) = LAMBDA (x, e)
			| beta (APP (e1, e2)) = 
				let 
					val 
						e = eval (APP(e1, e2)) 
					in 
						beta e
					end
			| beta n = n



		(*val symbolTable = ref [(VAR "9", 1)];
		!symbolTable := [];
*)

		(*bool: 0 int: 1 other: 2*)
(*		fun getTypeVar x [] = 2 
			| getTypeVar x h::t = 
			if (#1 h) = x then (#2 h)
			else getTypeVar x t

		fun setTypeVar x t = symbolTable := (x, t)::(!symbolTable)*)

(*		fun getType ((VAR (x:string)),n) = 
				let
					val type_x = getTypeVar x !symbolTable
				in
					if(type_x <> 2) then type_x
					else 
				end
				
			| getType T = 0
			| getType F = 0
			| getType Z = 1
			| getType (S t) = 
			let
				val t_type = getType(t)
			in
				body
			end
*)
		(*term, list, expected*)

		fun checkLambda (LAMBDA(x,y)) = true
			| checkLambda _ = false

		fun isInList(x, []) = false
			| isInList(x, (h::t):(lterm * int) list) = if (#1 h) = x then true else isInList(x, t)

		fun getType(x, []) = ~1
			| getType(x, (h::t):(lterm * int) list) = if (#1 h) = x then (#2 h) else getType(x, t)


		fun setAndGetType(x, L, t_type) = 
			let
				val t = getType(x, L)
			in
				if (t = ~1 andalso t_type <> ~1) then (t_type, (x, t_type)::L, true)
				else if (t = t_type) then (t_type, L, true)
				else if (t <> t_type) then (t_type, L, false)
				else (t_type, L, true)
			end

		(*fun findAndSet(x, L) = 
			if(isInList(x, L)) then 
		*)	

		(*term, list, expected : bool,type*) 
		fun isWellTypedHelper ((VAR (x:string)), expected, lst) = 
			let
				val (t_type, lst, b) = setAndGetType((VAR (x)), lst, expected)
			in
				if b = true then (true, t_type, lst) else (false, t_type, lst)
				
			end

			| isWellTypedHelper (T, expected, lst) = if (expected = 0 orelse expected = ~1) then (true, 0, lst) else (false, 0, lst)
			| isWellTypedHelper (F, expected, lst) = if (expected = 0 orelse expected = ~1) then (true, 0, lst) else (false, 0, lst) 
			| isWellTypedHelper (Z, expected, lst) = if (expected = 1 orelse expected = ~1) then (true, 1, lst) else (false, 1, lst)
			| isWellTypedHelper ((S n), expected, lst) = 
				if (expected = 1 orelse expected = ~1) then
					let
						val (b ,t_type, lst) = isWellTypedHelper(n, 1, lst)
					in
						if b = true then (true, 1, lst) else (false, 1, lst)
					end
				else
					(false, 1, lst)
			| isWellTypedHelper ((P n), expected, lst) = 
				if (expected = 1 orelse expected = ~1) then
					let
						val (b ,t_type, lst) = isWellTypedHelper(n, 1, lst)
					in
						if b = true then (true, 1, lst) else (false, 1, lst)
					end
				else
					(false, 1, lst)

			| isWellTypedHelper ((GTZ n), expected, lst) = 
				if (expected = 0 orelse expected = ~1) then
					let
						val (b ,t_type, lst) = isWellTypedHelper(n, 1, lst)
					in
						if b = true then (true, 0, lst) else (false, 0, lst)
					end
				else
					(false, 1, lst)

			| isWellTypedHelper ((IZ n), expected, lst) = 
				if (expected = 0 orelse expected = ~1) then
					let
						val (b ,t_type, lst) = isWellTypedHelper(n, 1, lst)
					in
						if b = true then (true, 0, lst) else (false, 0, lst)
					end
				else
					(false, 1, lst)

			| isWellTypedHelper((ITE(t1, t2, t3)), expected, lst) = 
				if(checkLambda(t1) orelse checkLambda(t2) orelse checkLambda(t3) ) then
					(false, expected, lst)
				else

					if(expected = 0 orelse expected = 1) then 
						let
							val (b1 ,t1_type, lst) = isWellTypedHelper(t1, 0, lst);
							val (b2 ,t2_type, lst) = isWellTypedHelper(t2, expected, lst);
							val (b3 ,t3_type, lst) = isWellTypedHelper(t3, expected, lst);
	(*
							val (b1 ,t1_type, lst) = isWellTypedHelper(t1, 0, lst);
							val (b2 ,t2_type, lst) = isWellTypedHelper(t2, expected, lst);
							val (b3 ,t3_type, lst) = isWellTypedHelper(t3, expected, lst);
	*)

						in
							if b1 andalso b2 andalso b3 then (true, 1, lst) else (false, 1, lst)
						end
		
					else if(expected = ~1) then 
						let
							val (b1 ,t1_type, lst) = isWellTypedHelper(t1, 0, lst);
							val (b2 ,t2_type, lst) = isWellTypedHelper(t2, ~1, lst);
							val (b3 ,t3_type, lst) = isWellTypedHelper(t3, t2_type, lst);


							val (b2 ,t2_type_r, lst) = isWellTypedHelper(t2, t3_type, lst);
							val (b1 ,t1_type_r, lst) = isWellTypedHelper(t1, 0, lst);
							


						in
							if b1 andalso b2 andalso b3 then
								(*if(t2_type <> t3_type) then
									if(t2_type <> ~1 andalso (t3_type = 1 orelse t3_type = 0 ) ) then
										isWellTypedHelper(t2, t3_type, lst)
									else if(t3_type <> ~1 andalso (t2_type = 1 orelse t2_type = 0 ) ) then
										isWellTypedHelper(t3, t2_type, lst)
									else
										(false, 0, lst)
								else
									(true, t2_type, lst)*)
								if(t3_type = 0 andalso t2_type <> 1) then 
									let
										val (b2 ,t2_type, lst) = isWellTypedHelper(t2, 0, lst);
									in
										if b2 then (true, 0, lst) else (false, 0, lst)
										
									end
								else if(t3_type = 1 andalso t2_type<> 0) then
									let
										val (b2 ,t2_type, lst) = isWellTypedHelper(t2, 1, lst);
									in
										if b2 then (true, 1, lst) else (false, 0, lst)
										(*(true, 1, lst)*)
									end
								else if(t2_type = 0 andalso t3_type <> 1) then 
									let
										val (b3 ,t3_type, lst) = isWellTypedHelper(t3, 0, lst);
									in
										if b3 then (true, 0, lst) else (false, 0, lst)
										(*(true, 0, lst)*)
									end
								else if(t2_type = 1 andalso t3_type<> 0) then
									let
										val (b3 ,t3_type, lst) = isWellTypedHelper(t3, 1, lst);
									in
										if b3 then (true, 1, lst) else (false, 0, lst)
										(*(true, 1, lst)*)
									end

								else if (t3_type = ~1 andalso t2_type = ~1) then
									(true , ~1, lst)
								else
									(false , 1, lst)
							else
								(false , 1, lst)

						end
					else 
						(false, expected, lst)

			| isWellTypedHelper(LAMBDA(t1, t2), expected, lst) = 
				(case t1 of
					VAR x => 
						let
							val (b, t_type, lst) = isWellTypedHelper(t2, ~1, lst);
						in
							(b, expected, lst)
						end
					| _ => raise Not_wellformed
				)
			
			| isWellTypedHelper((APP (LAMBDA (t1, t2), t3)), expected, lst) = 
				(case t1 of
					VAR x => 
						let
							val (b2, t2_type, lst) = isWellTypedHelper(t2, ~1, lst);
							val (b3, t3_type, lst) = isWellTypedHelper(t3, expected, lst);

						in
							if b2 andalso b3 then
								let
									val reduced = beta( (APP (LAMBDA (t1, t2), t3))  )
									val (rb, r_typed, lst) = isWellTypedHelper(reduced, expected, lst)
								in
									if rb then (true, expected, lst)  else (false, ~1, lst)
								end

							else
								(false, expected, lst)
						end
					| _ => raise Not_wellformed
				)

			| isWellTypedHelper((APP(APP(t1, t2) , t3)), expected, lst) = 
				let
					val (b1, t1_type, lst) = isWellTypedHelper(t1, ~1, lst);
					val (b2, t2_type, lst) = isWellTypedHelper(t2, ~1, lst);
					val (b3, t3_type, lst) = isWellTypedHelper(t2, ~1, lst);

				in
					if b1 andalso b2 andalso b3 then
						let
							val reduced = beta( (APP(APP(t1, t2) , t3)) );
							val (rb, r_typed, lst) = isWellTypedHelper(reduced, expected, lst)

						in
							if rb then (true, expected, lst)  else (false, ~1, lst)
						end
					else 
						(false, ~1, lst)

				end

			| isWellTypedHelper((APP (VAR x, t2)), expected, lst) = 
				let
					val (b2, t2_type, lst) = isWellTypedHelper(t2, ~1, lst);
				in
					(b2, expected, lst)
				end

			| isWellTypedHelper((APP (_, _)), expected, lst) = 
				(false, expected, lst)


			(*| isWellTypedHelper*)


				(*	
				let
					val (b1 ,t1_type, lst) = isWellTypedHelper(t1, 0, lst)
				in
					
				end*)






		fun isWellTyped t =
			#1 (isWellTypedHelper (t, ~1, []))

		
		fun rename (LAMBDA(t1, t2), n) = 
			(case t1 of
				VAR x => 
					let
						val new_var = VAR (x^Int.toString(n));
						val t2' = subst (t2, t1, new_var);
						val (new_t2, next_n) =  rename(t2', n+1)
					in
						(LAMBDA(new_var, new_t2), next_n+1) 
					end
				| _ => raise Not_wellformed
			)

			| rename (APP(LAMBDA(t1, t2), t3), n) = 
				(case t1 of
					VAR x => 
						let
							val new_var = VAR (x^Int.toString(n));
							val t2' = subst (t2, t1, new_var);
							val (new_t2, next_n) = rename(t2', n+1);

							val (new_t3, next_n) = rename(t3, next_n)
						in
							(APP(LAMBDA(new_var, new_t2), new_t3), next_n+1)
						end
					| _ => raise Not_wellformed
				)
			| rename ((APP(APP(e1, e2) , e3)), n) = 
				let
					val (new_e1, next_n) = rename(e1, n+1);
					val (new_e2, next_n) = rename(e2, next_n);
					val (new_e3, next_n) = rename(e3, next_n);
				in
					((APP(APP(new_e1, new_e2) , new_e3)), next_n+1)
				end
			| rename ((S t), n) = 
				let
					val (new_t, next_n) = rename(t, n);
				in
					((S new_t), next_n+1)
				end

			| rename ((P t), n) = 
				let
					val (new_t, next_n) = rename(t, n);
				in
					((P new_t), next_n+1)
				end
			| rename (ITE(b, x, y), n) = 
				let
					val (new_b, next_n) = rename(b, n);
					val (new_x, next_n) = rename(x, next_n);
					val (new_y, next_n) = rename(y, next_n);
				in
					(ITE(new_b, new_x, new_y), next_n+1)
				end
			| rename ((IZ t), n)= 
				let
					val (new_t, next_n) = rename(t, n);
				in
					((IZ new_t), next_n+1)
				end

			| rename ((GTZ t), n) = 
				let
					val (new_t, next_n) = rename(t, n);
				in
					((GTZ new_t), next_n+1)
				end
			| rename (t, n) = (t, n)




		fun betanfHelper (VAR x) = (VAR x)
			| betanfHelper Z = Z
			| betanfHelper (S t) = 
				let 
					val nft = betanfHelper t;
				in
					(S nft)
				end
			| betanfHelper (P t) = 
				let 
					val nft = betanfHelper t;
				in
					(P nft)
				end
			| betanfHelper T = T
			| betanfHelper F = F
			| betanfHelper (ITE(b, x, y)) = 
				let
					val nb = betanfHelper(b);
					val nx = betanfHelper(x);
					val ny = betanfHelper(y);
				in
					(ITE(nb, nx, ny))
				end
			| betanfHelper (IZ Z) = T
			| betanfHelper (IZ t) = 
				let
					val nt = betanfHelper(t);
				in
					(IZ nt)
				end
			| betanfHelper (GTZ Z) = F
			| betanfHelper (GTZ t) = 
				let
					val nt = betanfHelper(t);
				in
					(GTZ nt)
				end
			| betanfHelper (LAMBDA(t1, t2)) = 
				(case t1 of
					VAR x => 
						let
							val bnf_t1 = betanfHelper(t1);
							val bnf_t2 = betanfHelper(t2);
						in
							beta((LAMBDA(bnf_t1, bnf_t2))) 
						end
					| _ => raise Not_wellformed
				)

			| betanfHelper (APP(LAMBDA(t1, t2), t3)) = 
				(case t1 of
					VAR x => 
						let
							val bnf_t1 = betanfHelper(t1)
							val bnf_t2 = betanfHelper(t2);
							val bnf_t3 = betanfHelper(t3);
						in
							beta((APP(LAMBDA(bnf_t1, bnf_t2), bnf_t3))) 
						end
					| _ => raise Not_wellformed
				)
				(*let
					val bnf_t1 = betanfHelper(t1);
					val bnf_t2 = betanfHelper(t2);
				in
					beta(APP(bnf_t1, bnf_t2))
				end	*)
			| betanfHelper (APP(t1, t2)) = 
				let
					val bnf_t1 = betanfHelper(t1);
					val bnf_t2 = betanfHelper(t2);
				in
					(APP(bnf_t1, bnf_t2))
				end	


		fun normalize (VAR x) = (VAR x)
			| normalize Z = Z
			| normalize (S t) = 
				let 
					val nft = normalize t;
				in
					(case nft of 
						Z => S Z
						| S nft' => S nft
						| P nft' => nft'
						| _ => (S nft)

					)
				end
			| normalize (P t) = 
				let 
					val nft = normalize t;
				in
					(case nft of 
						Z => P Z
						| S nft' => nft'
						| P nft' => P nft
						| _ => (P nft)
					)
				end
			| normalize T = T
			| normalize F = F
			| normalize (ITE(b, x, y)) = 
				let
					val nb = normalize(b);
					val nx = normalize(x);
					val ny = normalize(y);
				in
					if(nx = ny) then nx
					else 
						(case nb of 
							T => nx
							| F => ny
							| _ => (ITE(nb, nx, ny))
						)
				end
			| normalize (IZ Z) = T
			| normalize (IZ t) = 
				let
					val nt = normalize(t);
				in
					(case nt of 
						S n => F
						| P n => F
						| Z => T
						| _ => (IZ nt)
					)
				end
			| normalize (GTZ Z) = F
			| normalize (GTZ t) = 
				let
					val nt = normalize(t);
				in
					(case nt of 
						S n => T
						| P n => F
						| Z => F
						| _ => (GTZ nt)
					)
				end
			| normalize (APP (t1, t2)) = APP(normalize(t1), normalize(t2) )
			| normalize (LAMBDA(t1, t2) ) = LAMBDA(normalize(t1), normalize(t2) )
			| normalize n = n
			

		fun betanf(e) = 
			if(isWellTyped e) then
				let
				 	val e_r = #1 (rename(e, 0));
				 	val bnf_e = betanfHelper(e_r);
				 	val norm_e = normalize(bnf_e)
				 in
				 	norm_e
				 end 
			else 
				raise Not_welltyped
	end
