% For SICStus, uncomment line below: (needed for member/2)
:- use_module(library(lists)).

% Load model, initial state and formula from file.
verify(Input) :-
    see(Input),
    read(T),
    read(L),
    read(S),
    read(F),
    seen,
    check(T, L, S, [], F).

%check(T, L, S, U, F)
%   T - The transitions in form of adjacency lists
%   L - The labeling
%   S - Current state
%   U - Currently recorded states
%   F - CTL Formula to check.
%
% Should evaluate to true if the sequent below is valid.
%
%(T,L),S|- F
%   U

% To execute: consult(’your_file.pl’). verify(’input.txt’).

% And
% sann om A och B är korrekta för modellen
check(T, L, S, [], and(A, B)) :-
    check(T, L, S, [], A),
    check(T, L, S, [], B).

% Or
% sann om A eller B är korrekta för modellen
check(T, L, S, [], or(A, B)) :-
    check(T, L, S, [], A);

    check(T, L, S, [], B).

% AX
% sann om F existerar i alla efterföljande tillstånd
check(T, L, S, U, ax(F)) :-
    member([S, V], T),
    checkAX(T, L, V, U, F).

% Support function for AX
checkAX(_, _, [], _, _).
checkAX(T, L, [Path|Rest], U, F) :-
    check(T, L, Path, U, F), !,
    checkAX(T, L, Rest, U, F).

% EX
% sann om F existerar i åtminstonde ett efterföljande tillstånd
check(T, L, S, U, ex(F)) :-
    member([S, Paths], T),
    member(Next, Paths),
    check(T, L, Next, U, F).

% AG
% sann om F existerar i alla nåbara tillstånd
check(T, L, S, U, ag(F)) :-
    member(S, U);

    check(T, L, S, [], F),
    append(U, [S], Output),
    check(T, L, S, Output, ax(ag(F))).

% EG
% sann om F existerar i alla tillstånd i en länk av efterföljande tillstånd
check(T, L, S, U, eg(F)) :-
    member(S, U);

    check(T, L, S, [], F),
    append(U, [S], Output),
    check(T, L, S, Output, ex(eg(F))), !.

% EF
% sann om F existerar i något av alla nåbara efterföljande tillstånd
check(T, L, S, U, ef(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F);

    \+ member(S, U),
    append(U, [S], Output),
    check(T, L, S, Output, ex(ef(F))), !.

% AF
% sann om F existerar i något av alla nåbara tillstånd i alla efterföljande tillstånd
check(T, L, S, U, af(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F);

    \+ member(S, U),
    append(U, [S], Output),
    check(T, L, S, Output, ax(af(F))).

% Literals
% sann om F inte existerar i nuvarande tillståndet
check(_, L, S, [], neg(X)) :-
    member([S, V], L),
    \+ member(X, V).

% sann om F existerar i nuvarande tillståndet
check(_, L, S, [], X)   :-
    member([S, V], L),
    member(X, V).
