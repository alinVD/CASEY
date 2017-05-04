av(F,L, sum( x(I, L)*f(I), I,1,n)/j(L)) :- gensym(i,I).
m(sum(AVFL*AVGL*j(l),L,1,n)) :- gensym(l,L),av(f,l,AVFL),av(g,l,AVGL).

% provides the name of the next variable. All variable names are
% unique
% -Varname
getNextVariable(Z) :- gensym(i,Z).

% replace all the variables X with the variables Y
% +X, +Y, +ExpIn, -ExpOut
substitute( X, Y, I, I) :- var(I). % don't restrict free variables
substitute( X, Y, X, Y) :- !.
substitute( X, Y, Z, Z) :- atom(Z),!.
substitute( X, Y, E1, Es1 ) :- E1 =.. [V|L], V \= X, maplist( substitute(X,Y), L, L2), Es1 =.. [V|L2].
substitute( X, Y, E1, Es1 ) :- E1 =.. [V|L], V=X,maplist( substitute(X,Y), L, L2), Es1 =.. [Y|L2].

swap( X, Y, X, Y).
swap( X, Y, Y, X).
swap( X, Y, Z, Z) :- atom(Z),!.
swap( X, Y, E1, Es1) :- E1 =.. [V|L],V\=X,maplist( swap(X,Y), L, L2),Es1 =.. [V|L2].
swap( X, Y, E1, Es1) :- E1 =.. [V|L],V=X,maplist( swap(X,Y), L, L2),Es1 =.. [Y|L2].

member(A,A).
member(A,X) :- \+free(A,X).
%member(A,[H|T]) :- member(A,H).
%member(A,[H|T]) :- member(A,T).
%member(A,X) :- X =.. [V|L], V == A.
%member(A,X) :- X =.. [V,W|L], W==A.
%member(A,X) :- X =.. [V,W|L], member(A,[V|L]).
% free(+A,+X) is true if A is not in the expression X
free(A,X) :- atomic(X),A \= X.
free(A,X) :- X =.. [V|L], V \= A, maplist( free(A),L).

eqSwap([X-Y|L],EsIn,EsOut) :- swap(X,Y,EsIn,EsRecur),eqSwap(L,EsRecur,EsOut).
eqSwap([],Es,Es).
eqReplace([X-Y|L],EsIn,EsOut) :- substitute(X,Y,EsIn,EsRecur),eqReplace(L,EsRecur,EsOut).
eqReplace([],Es,Es).

% rewrites the sum by replacing all the variables with unique variables
% +ExpIn, +ListRangesIn, -ExpOut, -ListRangesOut
rewriteSum( Exp, [], Exp, [] ).

rewriteSum( Exp, [r(X,S)|T] , ExpR, [r(Y,S)|U]  ) :-
	getNextVariable(Y), substitute(X, Y, Exp, ExpI), rewriteSum(ExpI, T, ExpR, U).


makeVariablesUnique( X, X) :- atom(X), !.

makeVariablesUnique( sum( Exp, L ), sum(Exp2, L2) ) :-
	!, makeVariablesUnique(Exp, ExpI), rewriteSum(ExpI, L, Exp2, L2).

makeVariablesUnique( Exp, Exp2 ) :-
	Exp =.. [V|L], maplist( makeVariablesUnique, L, L2 ), Exp2 =.. [V|L2].

% replaces X**5 by X*X*X*X*X
% +ExpIn -ExpOut
expandPowers( X**1, X) :- !.

expandPowers( X**N, Y*X) :- Nm1 is N-1, expandPowers( X**Nm1, Y), !.

expandPowers( E1, Es1 ) :- E1 =.. [V|L], maplist( expandPowers, L, L2), Es1 =.. [V|L2].


% dRewrite(+expr, -nicer expr)
dRewrite(sum(F,A,1,N),s(f)) :- member(A,F).
dRewrite(sum(F^2,A,1,N),sj(f)) :- member(A,F).
dRewrite(sum(F*G,A,1,N),p(f*g)) :- member(A,F),member(A,G).
dRewrite(sum(F^POW*G,A,1,N),p(f^POW*g)) :- member(A,F),member(A,G).
dRewrite(sum(F*G^POW,A,1,N),p(f*g^POW)) :- member(A,F),member(A,G).
dRewrite(sum(F^POW*G^POW2,A,1,N),p(f^POW*g^POW2)) :- member(A,F),member(A,G).

dRewrite(sum(F,A,1,N),sum(FD,A,1,N)) :- dRewrite(F,FD).
dRewrite(X*Y,XD*YD) :- dRewrite(X,XD),dRewrite(Y,YD).
dRewrite(X+Y,XD+YD) :- dRewrite(X,XD),dRewrite(Y,YD).
dRewrite(X-Y,XD-YD) :- dRewrite(X,XD),dRewrite(Y,YD).
dRewrite(X^N,XD^N) :- dRewrite(X,XD).
dRewrite(X,X).

%splitProduct(+variable,+expression,-part of expr dependent on var, -part independent)
splitProduct(X,B*A,DEPRECUR*A,INDEPRECUR) :- A\= C*D,member(X,A),!,splitProduct(X,B,DEPRECUR,INDEPRECUR).
splitProduct(X,B*A,DEPRECUR,INDEPRECUR*A) :- A\= C*D,!,splitProduct(X,B,DEPRECUR,INDEPRECUR).
splitProduct(X,A,A,1) :- A\=C*D,!,member(X,A).
splitProduct(X,A,1,A) :- A\=C*D,!.

%rvSeparate(+expr,-separated expression)
rvSeparate(EXPR,RESULT) :- nb_getval(rvlist,RVLIST),rvSeparate(EXPR,RVLIST,RESULT).
rvSeparate(A+B,LIST,AS+BS) :- rvSeparate(A,LIST,AS),rvSeparate(B,LIST,BS).
rvSeparate(EXPR,[X,NAME|TAIL],DEP*RECUR) :- splitProduct(X,EXPR,DEP,INDEP),rvSeparate(INDEP,TAIL,RECUR).
rvSeparate(EXPR,[],EXPR) :- !.

%ex(+expression, -expected value)
ex(sum(X,A,1,N),sum(XDS,A,1,N)) :- ex(X,XD),simplify(XD,XDS).
ex(Y*sum(X,A,1,N),LIST,sum(YXDS,A,1,N)) :- ex(X*Y,YXD),simplify(YXD,YXDS).
ex(sum(X,A,1,N)*Y,LIST,sum(YXDS,A,1,N)) :- ex(X*Y,YXD),simplify(YXD,YXDS).
ex(sum(X,A,1,N)^2,LIST,sum(sum(X*X2,A,1,N),A2,1,N)) :- gensym(A,A2),substitute(A,A2,X,X2).

ex(A*B,RESULT) :- nb_getval(rvlist,LIST),ex(A*B,LIST,RESULT).
ex(A*B,LIST,EXA*EXB) :- exIndependent(A,B,LIST),ex(A,EXA),ex(B,EXB).
ex(A+B,LIST,EXA+EXB) :- ex(A,EXA),ex(B,EXB).
ex(C,RESULT) :- nb_getval(rvlist,LIST),ex(C,LIST,RESULT).
ex(C*A,LIST,C*EXA) :- exFreeAll(C,LIST),ex(A,EXA).
ex(A*C,LIST,C*EXA) :- exFreeAll(C,LIST),ex(A,EXA).
ex(C,LIST,C) :- exFreeAll(C,LIST).
ex(A,LIST,EXA2) :- expand(A,A2),A\==A2,ex(A2,EXA2).
ex(A,LIST,EXA2) :- simplify(A,A2),A\==A2,ex(A2,EXA2).
ex(A,LIST,EXA2) :- rvSeparate(A,A2),A\==A2,A*1\==A2,1*A\==A2,ex(A2,EXA2).
ex(A,LIST,RESULT) :- exBase(A,RESULT).

var(X,EXX-EX^2) :- ex(X*X,EXX),ex(X,EX).
cov(X,Y,EXY-EX*EY) :- ex(X*Y,EXY),ex(x,EX),ex(y,EY).

exIndependent(A,B,[X,NAME|TAIL]) :- member(X,A),free(X,B).
exIndependent(A,B,[X,NAME|TAIL]) :- exIndependent(A,B,TAIL).

exFreeAll(C,[X,NAME|TAIL]) :- free(X,C),exFreeAll(C,TAIL).
exFreeAll(C,[]).

expand(F,RESULT) :- expand2(F,FD),F\=FD,expand(FD,RESULT).
expand(F,F).

expand2(A+B*(C+D)*E+F,A+B*E*C+B*E*D+F).
expand2(A+B*(C+D)+F,A+B*C+B*D+F).
expand2(A+(C+D)*E+F,A+E*C+E*D+F).
expand2(X,X).

% simplify(+expr, -simplified expr)
simplify(F,RESULT) :- simplify2(F,FD),F\=FD,simplify(FD,RESULT).
simplify(F,F).

simplify2(A*1,A).
simplify2(1*A,A).
simplify2(A*1*B,A*B).
simplify2(A*0,0).
simplify2(0*A,0).
simplify2(A*0*B,0).

simplify2(A*(B*C),A*B*C).
simplify2((A*B)*C,A*B*C).
simplify2(A+(B+C),A+B+C).
simplify2((A+B)+C,A+B+C).
simplify2(A-(B+C),A-B-C).
simplify2((A-B)+C,A-B+C).
simplify2(A+(B-C),A+B-C).
simplify2((A+B)-C,A+B-C).
simplify2(A-(B-C),A-B+C).
simplify2((A-B)-C,A-B-C).

simplify2(A*B,AD*BD) :- simplify2(A,AD),simplify2(B,BD).
simplify2(A+B,AD+BD) :- simplify2(A,AD),simplify2(B,BD).
simplify2(A-B,AD-BD) :- simplify2(A,AD),simplify2(B,BD).

% simplify2(sum(F,A,1,N),sum(FD,A,1,N)) :- simplify2(F,FD).

simplify2(F,F).

%dsmpf(+equation, -simplified result).

% Simplifications
dsmpf(d(A,B),1) :- \+var(A),\+var(B),A==B.
dsmpf(1-d(A,B),0) :- \+var(A),\+var(B),A==B.
dsmpf(d(A,B)^N,d(A,B)).

dsmpf(sum(1,A,1,N),N).

dsmpf(sum(d(A,B),A,1,N),1).
dsmpf(sum(d(A,B),B,1,N),1).

dsmpf(sum(X*d(A,B),A,1,N),X2) :- substitute(A,B,X,X2).
dsmpf(sum(X*d(A,B),B,1,N),X2) :- substitute(B,A,X,X2).
dsmpf(sum(d(A,B)*Y,A,1,N),X2) :- substitute(A,B,Y,X2).
dsmpf(sum(d(A,B)*Y,B,1,N),X2) :- substitute(B,A,Y,X2).
dsmpf(sum(X*d(A,B)*Y,A,1,N),X2) :- substitute(A,B,X*Y,X2).
dsmpf(sum(X*d(A,B)*Y,B,1,N),X2) :- substitute(B,A,X*Y,X2).

% pull products out of sums
dsmpf(sum(F,A,1,N),F*N) :- free(A,F).
%dsmpf(sum(F*X,A,1,N),F*sum(X,A,1,N)) :- free(A,F).
dsmpf(sum(EXPR,A,1,N),INDEP*sum(DEPS,A,1,N)) :- splitProduct(A,EXPR,DEP,INDEP),INDEP\==1,simplify(DEP,DEPS).

% Recursive Cases
% summations inside sums
dsmpf(sum(X+Y,A,1,N),DS1+DS2) :- simplify(X,XS),simplify(Y,YS),dsmpf(sum(XS,A,1,N),DS1),dsmpf(sum(YS,A,1,N),DS2).
dsmpf(sum(C*(X+Y),A,1,N),DS1+DS2) :- simplify(C*X,XS),simplify(C*Y,YS),dsmpf(sum(XS,A,1,N),DS1),dsmpf(sum(YS,A,1,N),DS2).
dsmpf(sum(C*(X+Y)*D,A,1,N),DS1+DS2) :- simplify(C*X*D,XS),simplify(C*Y*D,YS),dsmpf(sum(XS,A,1,N),DS1),dsmpf(sum(YS,A,1,N),DS2).
dsmpf(sum((X+Y)*D,A,1,N),DS1+DS2) :- simplify(X*D,XS),simplify(Y*D,YS),dsmpf(sum(XS,A,1,N),DS1),dsmpf(sum(YS,A,1,N),DS2).
dsmpf(sum(X-Y,A,1,N),DS1-DS2) :- simplify(X,XS),simplify(Y,YS),dsmpf(sum(XS,A,1,N),DS1),dsmpf(sum(YS,A,1,N),DS2).
dsmpf(sum(C*(X-Y),A,1,N),DS1-DS2) :- simplify(C*X,XS),simplify(C*Y,YS),dsmpf(sum(XS,A,1,N),DS1),dsmpf(sum(YS,A,1,N),DS2).
dsmpf(sum(C*(X-Y)*D,A,1,N),DS1-DS2) :- simplify(C*X*D,XS),simplify(C*Y*D,YS),dsmpf(sum(XS,A,1,N),DS1),dsmpf(sum(YS,A,1,N),DS2).
dsmpf(sum((X-Y)*D,A,1,N),DS1-DS2) :- simplify(X*D,XS),simplify(Y*D,YS),dsmpf(sum(XS,A,1,N),DS1),dsmpf(sum(YS,A,1,N),DS2).

% give up and dsmpf inside sum
dsmpf(sum(X,A,1,N),sum(XD,A,1,N)) :- dsmpf(X,XD).

dsmpf(X*Y,XD*YD) :- dsmpf(X,XD),dsmpf(Y,YD).
dsmpf(X+Y,XD+YD) :- dsmpf(X,XD),dsmpf(Y,YD).
dsmpf(X-Y,XD-YD) :- dsmpf(X,XD),dsmpf(Y,YD).
dsmpf(X^N,XD^ND) :- dsmpf(X,XD),dsmpf(N,ND).
dsmpf(X,X).

dSimplify(F,RESULT) :- dsmpf(F,FD),F\==FD,dSimplify(FD,FDS),simplify(FDS,RESULT).
dSimplify(F,F).

join([H],[L],[H,L]).
join([H],[],[H]).
join([H],[L|M],[H,L|M]).
join([],[L],[H|L]).
join([H|T],R,JOIN) :- join(T,R,RECUR),join([H],RECUR,JOIN).
join([H|T],[],[H|T]).
join([],[L|M],[L|M]).

% eqRed(+eqn, +orig eqSet, +list of eqSets, -eqn of deltas)
% Symmetric cases- match sets and make swaps
eqRed(F,EQSET,[EQSET2|R],F2*EQN+RECUR) :- eqMatch(EQSET,EQSET2,SWAPS),eqSwap(SWAPS,F,F2),eqRed(EQSET2,EQN),eqRed(F,EQSET,R,RECUR).
eqRed(F,EQSET,[],F*EQN) :- eqRed(EQSET,EQN).

% eqRed(+eqSet, -eqn. of delta's)
eqRed([eq([A,B|C])|D],d(A,B)*R1) :- eqRed([eq([B|C])|D],R1).
eqRed([eq([A]),eq([B|C])|D],(1-d(A,B))*R1*R2):-eqRed([eq([B|C])|D],R1),eqRed2([eq([A])|D],R2).
eqRed2([eq([A]),eq([B|C])|D],(1-d(A,B))*R1):-eqRed2([eq([A])|D],R1).
eqRed([eq([A])],1).
eqRed2([eq([A])],1).

% eqForm(+eqSet, -form)
eqForm(R,REVERSEDSORTEDFORM) :- eqForm2([0],R,FORM),msort(FORM,SORTEDFORM),reverse(SORTEDFORM,REVERSEDSORTEDFORM).
eqForm2([I],[eq([A])],[I2]) :- plus(I,1,I2).
eqForm2([I],[eq([A])|R],MERGING) :- plus(I,1,I2),eqForm2([0],R,RECUR),merge([I2],RECUR,MERGING).
eqForm2([I],[eq([A|B])|R],RECUR) :- plus(I,1,I2),eqForm2([I2],[eq(B)|R],RECUR).

% eqFormAllows(+main form, +form to check).
eqFormAllows([],[]).
eqFormAllows([A],[]).
eqFormAllows([A|B],[C|D]):- A>=C,eqFormAllows(B,D).

% eqCheckForm(+main eqSet, +list of eqSets to check, -list matching)
%eqCheckForm([F|G],[[L|M]|R],RESULT) :- eqForm([F|G],FORM),eqCheckForm2(FORM,[[L|M]|R],RESULT).
eqCheckForm(FORM,[[L|M]|R],RESULT) :- eqForm([L|M],LFORM),eqFormAllows(FORM, LFORM),eqCheckForm(FORM,R,RECUR),merge([[L|M]],RECUR,RESULT).
eqCheckForm(FORM,[[L|M]|R],RECUR) :- eqCheckForm(FORM, R, RECUR).
eqCheckForm(FORM,[],[]).

% eqCheckUniqueForm(+list of eqSets to compare, -unique list)
eqCheckUniqueForm([[L|M],[O|P]|R],RESULT) :- eqCheckUniqueForm([[O|P]|R],RECUR),eqForm([L|M],FORM),eqCheckUniqueForm2(FORM,RECUR,RECUR2),merge([[L|M]],RECUR2,RESULT).
eqCheckUniqueForm([[L|M]],[[L|M]]).
eqCheckUniqueForm2(FORM,[[L|M]|R],RESULT) :- eqForm([L|M],FORML),FORM\==FORML,eqCheckUniqueForm2(FORM,R,RECUR),merge([[L|M]],RECUR,RESULT).
eqCheckUniqueForm2(FORM,[[L|M]|R],RESULT) :- eqCheckUniqueForm2(FORM,R,RESULT).
eqCheckUniqueForm2(FORM,[],[]).

% eqDot (+eq(), +list of eqsets, -eq() added to all eqsets)
eqDot(eq([H|T]),[[L|M]|N],RESULT) :- eqDot(eq([H|T]),N,RECUR),merge([[eq([H|T]),L|M]],RECUR,RESULT).
eqDot(eq([H|T]),[],[]).

% eqCross(+element, +list of eqsets, -list of all possible new eqsets with element)
eqCross(A,[],[]).
eqCross(A,[[eq([H|T])|U]|R],RESULT) :- eqCross2(A,U,CROSS2RECUR),eqDot(eq([H]),CROSS2RECUR,DOTRECUR),eqCross(A,R,CROSSRECUR),merge([[eq([A]),eq([H|T])|U],[eq([A,H|T])|U]],DOTRECUR,MERGE1),merge(MERGE1,CROSSRECUR,RESULT).
eqCross2(A,[],[]).
eqCross2(A,[eq([H|T])|U],RESULT) :- eqCross2(A,U,CROSS2RECUR),eqDot(eq([H]),CROSS2RECUR,DOTRECUR),merge([[eq([A,H|T])|U]],DOTRECUR,RESULT).

% eqGen(+[list of variables], -list of all eqSets using variables)
eqGen([H|T],RESULT) :- eqGen2([[eq([H])]],T,RESULT).
eqGen2(L,[A|B],RESULT) :- eqCross(A,L,CROSSRECUR),eqGen2(CROSSRECUR,B,RESULT).
eqGen2(L,[],L).

% eqMakeList(+eqSet, -list of all variables in eqSet)
eqMakeList([eq([H|T])|L],RESULT) :- eqMakeList(L,RECUR),join([H|T],RECUR,RESULT).
eqMakeList([],[]).

%eqSymGen(+eqSet, -list of all eqSets of same form using same variables)
eqSymGen([eq([H|T])|L],RESULT) :- eqForm([eq([H|T])|L],FORM),eqMakeList([eq([H|T])|L],LIST),eqSymGen2(FORM,LIST,RESULT).
eqSymGen2(FORM,[A|B],RESULT) :- eqSymGen3(FORM,[[eq([A])]],B,RESULT).
eqSymGen3(FORM,LIST,[A|B],RESULT) :- eqCross(A,LIST,CROSS),eqCheckForm(FORM,CROSS,CHECKED),eqSymGen3(FORM,CHECKED,B,RESULT).
eqSymGen3(FORM,LIST,[],LIST).

% eqUniqueGen(+list of vars, -list of unique eqSets from vars)
eqUniqueGen([A|B],RESULT) :- eqUniqueGen2([[eq([A])]],B,RESULT).
eqUniqueGen2(LIST,[A|B],RESULT) :- eqCross(A,LIST,CROSS),eqCheckUniqueForm(CROSS,UNIQUE),eqUniqueGen2(UNIQUE,B,RESULT).
eqUniqueGen2(LIST,[],LIST).

% eqStandard(+list of eqSets, -eqSets with eq classes in decreasing size)
eqStandard([H|T],RESULT) :- eqStandard2(H,RECUR2),eqStandard(T,RECUR),merge([RECUR2],RECUR,RESULT).
eqStandard([],[]).
eqStandard2([H|T],RESULT) :- eqKey([H|T],KEYED),keysort(KEYED,SORTED),reverse(SORTED,INVERTED),eqRemoveKey(INVERTED,RESULT).
eqStandard2([],[]).
eqKey([eq([H|T])|R],RESULT) :- eqKey(R,RECUR),length([H|T],SIZE),merge([SIZE-eq([H|T])],RECUR,RESULT).
eqKey([],[]).
eqRemoveKey([SIZE-eq([H|T])|R],RESULT) :- eqRemoveKey(R,RECUR),join([eq([H|T])],RECUR,RESULT).
eqRemoveKey([],[]).

% eqDif(+eqSet1, +eqSet2, -number of different elements)
eqDif(L,R,RESULT) :- eqMakeList(L,L2),eqMakeList(R,R2),eqDif2(L2,R2,RESULT).
eqDif2([A],[A],0).
eqDif2([A],[B],1).
eqDif2([A|B],[A|D],RESULT) :- eqDif2(B,D,RESULT).
eqDif2([A|B],[C|D],RESULT) :- eqDif2(B,D,RECUR),plus(RECUR,1,RESULT).

% eqMatch(eqSet,+eqSet,-list of transforms)
eqMatch(H,T,RESULT) :- eqMakeList(H,L1),eqMakeList(T,L2),eqMatch2(L1,L2,RESULT).
eqMatch2([H|J],[L|M],RESULT) :- H\==L,eqSwap([H-L],J,J2),eqSwap([H-L],M,M2),eqMatch2(J2,M2,RECUR),join([H-L],RECUR,RESULT).
eqMatch2([H|J],[L|M],RESULT) :- eqMatch2(J,M,RESULT).

initRV(X) :- nb_setval(rvflist,[]),nb_setval(rvlist,[]).

makeRVFamily(X,NAME,VARS,RULES) :- nb_getval(rvflist,LIST),makeRVFamily2(X,NAME,VARS,[],LIST,RULES).
% add rule for existing var
makeRVFamily2(X,NAME,VARS,USEDLIST,[[X,NAME,VARS2,RULES2]|TAIL],RULES) :- union(VARS,VARS2,NEWVARS),union(RULES,RULES2,NEWRULES),append(USEDLIST,[[X,NAME,NEWVARS,NEWRULES]|TAIL],NEWLIST),nb_setval(rvflist,NEWLIST).
% recur
makeRVFamily2(X,NAME,VARS,USEDLIST,[[X2,NAME2,VARS2,RULES2]|TAIL],RULES) :- append(USEDLIST,[[X2,NAME2,VARS2,RULES2]],NEWUSEDLIST),makeRVFamily2(X,NAME,VARS,NEWUSEDLIST,TAIL,RULES).
% add new variable
makeRVFamily2(X,NAME,VARS,USEDLIST,[],RULES) :- nb_getval(rvflist,LIST),append(LIST,[[X,NAME,VARS,RULES]],NEWLIST),nb_setval(rvflist,NEWLIST).

deleteRVFamily(NAME) :- nb_getval(rvflist,LIST),deleteRVFamily2(NAME,[],LIST).
deleteRVFamily2(NAME,USEDLIST,[[X,NAME,VARS2,RULES2]|TAIL]) :- append(USEDLIST,TAIL,NEWLIST),nb_setval(rvflist,NEWLIST).
deleteRVFamily2(NAME,USEDLIST,[[X,NAME2,VARS2,RULES2]|TAIL]) :- append(USEDLIST,[[X,NAME2,VARS2,RULES2]],NEWUSEDLIST),deleteRVFamily2(NAME,NEWUSEDLIST,TAIL).

makeRV(X,NAME,VARS) :- nb_getval(rvlist,LIST),makeRV2(X,NAME,VARS,LIST).
% ensure not already defined
makeRV2(X,NAME,VARS,[X|TAIL]).
makeRV2(X,NAME,VARS,[X|TAIL]) :- makeRV2(X,NAME,VARS,TAIL).
% make new variable
makeRV2(X,NAME,VARS,[]) :- nb_getval(rvlist,LIST),append([X,NAME],LIST,NEWLIST),nb_setval(rvlist,NEWLIST),nb_getval(rvflist,RVFLIST),executeRules(X,NAME,VARS,RVFLIST).

deleteRV(X,NAME) :- nb_getval(rvlist,LIST),deleteRV2(X,NAME,[],LIST).
deleteRV2(X,NAME,USEDLIST,[X,NAME|TAIL]) :- append(USEDLIST,TAIL,NEWLIST),nb_setval(rvlist,NEWLIST),nb_getval(rvflist,RVFLIST),deleteRules(X,NAME,RVFLIST).
%recur
deleteRV2(X,NAME,USEDLIST,[X2,NAME2|TAIL]) :- append(USEDLIST,[X2,NAME2],NEWUSEDLIST),deleteRV2(X,NAME,NEWUSEDLIST,TAIL).

% find right variable family
executeRules(X,NAME,VARS,[[X2,NAME,VARS2,RULES]|TAIL]) :- listRules(VARS,VARS2,LISTRULES),append([X2-X],LISTRULES,REPLACELIST),executeRules2(X,NAME,VARS,[X2,NAME,VARS2,RULES],REPLACELIST).
executeRules(X,NAME,VARS,[[X2,NAME2,VARS2,RULES]|TAIL]) :- executeRules(X,NAME,VARS,TAIL).
% execute
executeRules2(X,NAME,VARS,[X2,NAME,VARS2,[expectation(A)==B|TAIL]],REPLACELIST) :- executeRules2(X,NAME,VARS,[X2,NAME,VARS2,TAIL],REPLACELIST),eqReplace(REPLACELIST,A,A2),eqReplace(REPLACELIST,B,B2),assert(exBase(A2,B2)).
executeRules2(X,NAME,VARS,[X2,NAME,VARS2,[]],REPLACELIST).

% find right variable family
deleteRules(X,NAME,[[X2,NAME,VARS2,RULES]|TAIL]) :- deleteRules2(X,NAME,[X2,NAME,VARS2,RULES]).
deleteRules(X,NAME,[[X2,NAME2,VARS2,RULES]|TAIL]) :- deleteRules(X,NAME,TAIL).
% execute
deleteRules2(X,NAME,[X2,NAME,VARS2,[expectation(A)==B|TAIL]]) :- deleteRules2(X,NAME,[X2,NAME,VARS2,TAIL]),substitute(X2,X,A,A2),retract(exBase(A2,B2)).
deleteRules2(X,NAME,[X2,NAME,VARS2,[]]).

listRules([A|B],[C|D],RESULT) :- listRules(B,D,RECUR),append([C-A],RECUR,RESULT).
listRules([],[],[]).

case(symmetric(EQSET),F,RESULT) :- eqStandard(EQSET,STDEQSET),eqSymGen(EQSET,SYMSETS),eqStandard(SYMSETS,STDSYMSETS),eqRed(F,STDEQSET,STDSYMSETS).
case(EQSET,F,RESULT) :- eqRed(F,EQSET,RESULT).
dSwitch([case(H|T)|TAIL],CASE+SWITCH) :- case(H|T,CASE),dSwitch(TAIL,SWITCH).
dSwitch([A|B],A+SWITCH) :- dSwitch(B,SWITCH).
dSwitch([A],A).
