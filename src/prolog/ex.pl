
% provides the name of the next variable. All variable names are
% unique
% -Varname
getNextVariable(Z) :-
	gensym(i,Z).

% replace all the variables X with the variables Y
% +X, +Y, +ExpIn, -ExpOut
substitute( X, Y, X, Y) :- !.

substitute( X, Y, Z, Z) :-
	atom(Z),
	!.

substitute( X, Y, E1, Es1 ) :-
	E1 =.. [V|L],
	V \= X,
	maplist( substitute(X,Y), L, L2),
	Es1 =.. [V|L2].

% rewrites the sum by replacing all the variables with unique variables
% +ExpIn, +ListRangesIn, -ExpOut, -ListRangesOut
rewriteSum( Exp, [], Exp, [] ).

rewriteSum( Exp, [r(X,S)|T] , ExpR, [r(Y,S)|U]  ) :-
	getNextVariable(Y),
	substitute(X, Y, Exp, ExpI),
	rewriteSum(ExpI, T, ExpR, U).


makeVariablesUnique( X, X) :-
	atom(X),
	!.

makeVariablesUnique( sum( Exp, L ), sum(Exp2, L2) ) :-
	!,
	makeVariablesUnique(Exp, ExpI),
	rewriteSum(ExpI, L, Exp2, L2).

makeVariablesUnique( Exp, Exp2 ) :-
	Exp =.. [V|L],
	maplist( makeVariablesUnique, L, L2 ),
	Exp2 =.. [V|L2].

% pushes expectation inside sums as deep as possible
% +ExpIn -ExpOut
linearityExpectation(Ein, Eout) :-
	expandPowers(Ein, Eaux1),
	makeVariablesUnique(Eaux1, Eaux2),
	combineSums(Eaux2, Eaux3),
	pushExpectationIn(Eaux3, Eout).

% replaces X**5 by X*X*X*X*X
% +ExpIn -ExpOut
expandPowers( X**1, X) :- !.

expandPowers( X**N, Y*X) :-
	Nm1 is N-1,
	expandPowers( X**Nm1, Y),
	!.

expandPowers( E1, Es1 ) :-
	E1 =.. [V|L],
	maplist( expandPowers, L, L2),
	Es1 =.. [V|L2].


% combineSums assumes that all the variables are unique
% +ExpIn -ExpIn

combineSums( sum( X1, L1)*sum(X2, L2), sum( Z1*Z2, L3) ) :-
	combineSums( X1, C1),
	C1 = sum(Y1, La1) ->
	(append(L1, La1, Lo1), Z1=Y1);
	(Lo1 = L1,Z1=C1),
	combineSums( X2, C2),
	C2 = sum(Y2, La2) ->
	(append(L2, La2, Lo2), Z2=Y2);
	(Lo2 = L2, Z2=C2),
	append(Lo1, Lo2, L3),
	!.

combineSums( X*sum( Y, L), sum(X*Y, L) ) :- !.


	
