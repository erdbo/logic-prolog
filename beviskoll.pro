verify(InputFileName) :-
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof, []).

% Support functions
getTerm(Row, [[Row, Term, _] | _], Term).
getTerm(Row, [_ | T], Output) :-
    getTerm(Row, T, Output).

getAssTerm(Row, [[Row, Term, _] | _], Term).
getAssTerm(Row, [[[H | T] | Z] | _], Term) :-
    getAssTerm(Row, [[H | T] | Z], Term).
getAssTerm(Row , [_ | T], Term) :-
    getAssTerm(Row , T, Term).

% Rules
premise([H|_], H).
premise([_|T], H) :-
    premise(T,H).
premise([H|T], G, 1) :-
    premise([H|T], G).

assumption([[Row, Term, assumption] | T], Prems, List) :-
    assumption(T, Prems, List, [Row,Term,assumption]).
assumption([[[Row, Term, assumption] | T] | Z], Prems, List, AssList) :-
    assumption([[Row, Term, assumption] | T], Prems, [AssList|  List]),
    assumption(Z, Prems, List, [[[Row, Term, assumption] | T] | [AssList]]).
assumption([[Row,Term,premise] | T], Prems, List, AssList) :-
    premise(Prems, Term),
    assumption(T, Prems, List, [[Row,Term,premise]|[AssList]]).
assumption([[Row, Term, Fun] | T], Prems, List, AssList) :-
    call(Fun, Term, [AssList | List], 1), !,
    assumption(T, Prems, List, [[Row, Term, Fun] | [AssList]]).
assumption([], _, _, _).
assumption(X, X).

copy(Row, Term, List) :-
    getTerm(Row, List, Output),
    copy(Term, Output).
copy(Row, Term, List, 1) :-
    getAssTerm(Row, List, Output),
    copy(Term, Output).
copy(X, X).

andint(Row1, Row2, Term, List) :-
    getTerm(Row1, List, Output1),
    getTerm(Row2, List, Output2),
    andint(Term, Output1, Output2).
andint(Row1, Row2, Term, List, 1) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    andint(Term, Output1, Output2), !.
andint(and(X, Y), X, Y).

andel1(Row, Term, List) :-
    getTerm(Row, List, Output),
    andel1(Term, Output).
andel1(Row, Term, List, 1) :-
    getTerm(Row, List, Output),
    andel1(Term, Output).
andel1(X, and(X,_)).

andel2(Row, Term, List) :-
    getTerm(Row, List, Output),
    andel2(Term, Output).
andel2(Row, Term, List, 1) :-
    getAssTerm(Row, List, Output),
    andel2(Term, Output).
andel2(X, and(_,X)).

orint1(Row, Term, List) :-
    getTerm(Row, List, Output),
    orint1(Term, Output).
orint1(Row, Term, List, 1) :-
    getAssTerm(Row, List, Output),
    orint1(Term, Output).
orint1(or(X, _), X) :- !.

orint2(Row, Term, List) :-
    getTerm(Row, List, Output),
    orint2(Term, Output).
orint2(Row, Term, List, 1) :-
    getAssTerm(Row, List, Output),
    orint2(Term, Output).
orint2(or(X, _), X) :- !.

orel(Row1, Row2, Row3, Row4, Row5, Term, List) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    getAssTerm(Row3, List, Output3),
    getAssTerm(Row4, List, Output4),
    getAssTerm(Row5, List, Output5),
    orel(Term, Output1, Output2, Output3, Output4, Output5).
orel(Row1, Row2, Row3, Row4, Row5, Term, List, 1) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    getAssTerm(Row3, List, Output3),
    getAssTerm(Row4, List, Output4),
    getAssTerm(Row5, List, Output5),
    orel(Term, Output1, Output2, Output3, Output4, Output5).
orel(Term,or(X, Y), X, Term, Y, Term).

impint(Row1, Row2, Term, List) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    impint(Term,Output1,Output2).
impint(Row1, Row2, Term, List, 1) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    impint(Term,Output1,Output2).
    impint(imp(X,Y), X, Y).

impel(Row1, Row2, Term, List) :-
    getTerm(Row1, List, Output1),
    getTerm(Row2, List, Output2),
    impel(Term,Output1,Output2).
impel(Row1, Row2, Term, List, 1) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    impel(Term,Output1,Output2).
impel(Term,X,imp(X,Term)).

negint(Row1, Row2, Term, List) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    negint(Term, Output1, Output2).
negint(Row1, Row2, Term, List, 1) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    negint(Term, Output1, Output2).
negint(neg(X), X, cont).

negel(Row1, Row2, Term, List) :-
    getTerm(Row1, List, Output1),
    getTerm(Row2, List, Output2),
    negel(Term, Output1,Output2).
negel(Row1, Row2, Term, List, 1) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    negel(Term, Output1,Output2).
negel(cont, X, neg(X)).

contel(Row, Term, List) :-
    getTerm(Row, List, Output),
    contel(Output).
contel(Row, Term, List, 1) :-
    getAssTerm(Row, List, Output),
    contel(Output).
contel(cont).

negnegint(Row, Term, List) :-
    getTerm(Row, List, Output),
    negnegint(Term, Output).
negnegint(Row, Term, List, 1) :-
    getAssTerm(Row, List, Output),
    negnegint(Term, Output).
negnegint(neg(neg(X)), X).

negnegel(Row, Term, List) :-
    getTerm(Row, List, Output),
    negnegel(Term, Output).
negnegel(Row, Term, List, 1) :-
    getAssTerm(Row, List, Output),
    negnegel(Term, Output).
negnegel(X, neg(neg(X))).

mt(Row1, Row2, Term, List) :-
    getTerm(Row1, List, Output1),
    getTerm(Row2, List, Output2),
    mt(Term, Output1, Output2).
mt(Row1, Row2, Term, List, 1) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    mt(Term, Output1, Output2).
mt(neg(X), imp(X, Y), neg(Y)).

pbc(Row1, Row2, Term, List) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    pbc(Term, Output1, Output2).
pbc(Row1, Row2, Term, List, 1) :-
    getAssTerm(Row1, List, Output1),
    getAssTerm(Row2, List, Output2),
    pbc(Term, Output1, Output2).
pbc(X, neg(X), cont).

lem(or(X,neg(X)), _).


% Main
valid_proof(Prems, Goal, [[_, Goal, premise]], List) :-
    premise(Prems, Goal).
valid_proof(Prems, Goal, [[_, Goal, Fun]], List) :-
    catch(call(Fun, Goal, List),_, fail).

valid_proof(Prems, Goal, [[Row, Term, premise] | T], List) :-
    premise(Prems, Term),
    valid_proof(Prems, Goal, T, [[Row, Term, premise] | List]).

valid_proof(Prems, Goal, [[[Row, Term, assumption] | T] | Z], List) :-
    assumption([[Row, Term, assumption] | T], Prems, List),
    !,
    valid_proof(Prems, Goal, Z, [[[Row, Term, assumption] | T] | List]).

valid_proof(Prems, Goal, [[Row, Term, Fun] | T], List) :-
    catch(call(Fun, Term, List), _, fail),
    valid_proof(Prems, Goal, T, [[Row, Term, Fun] | List]).
