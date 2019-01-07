:- set_prolog_flag(toplevel_print_options, [quoted(true),numbervars(true),portrayed(true),max_depth(100)]).

%% crossing refactoring
%% allow to use: append/3, member/2, nonmember/2, memberchk/2, length/2
% start: [f,w,g,c,b]-[]
/* member VS memberchk
| ?- member(X, [1,2,3]).
X = 1 ? ;
X = 2 ? ;
X = 3 ? ;
no
| ?- memberchk(X, [1,2,3]).
X = 1 ? ;
no
*/

%% TASK 1
safe(L):-
  member(f, L),!.
safe(L):-
  \+ notsafe(L).
notsafe(L):-
  member(g, L), member(w, L).
notsafe(L):-
  member(g, L), member(c, L).

%% TASK 2
goal([]-S2):-
  sort(S2, L),
  length(L, 5).

%% TASK 3
equiv(X1-X2, Y1-Y2):-
  e(X1, Y1),
  e(X2, Y2).
e(X, Y):-
  length(X, K),
  length(Y, K),
  sort(X, L),
  sort(Y, L).

%% TASK 4
visited(State1, Seq):-
  member(State2, Seq),
  equiv(State1, State2), !.

%% TASK 5
choose([f], S):-
  member(f, S), 
  delete(f, S, L),
  safe(L).  
choose([f, I], S):-
  member(f, S),
  member(I, S),
  f \== I,
  delete(f, S, L),
  delete(I, L, L2),
  safe(L2).

% helping predicate, delete item I from list L and get result list R. assume I is in L.
delete(I, L, R):-
  d(I, L, [], R).
d(I, [I|T], Acc, R):-
  append(T, Acc, R).
d(I, [NoI|T], Acc, R):-
  append([NoI], Acc, Acc2),
  d(I, T, Acc2, R).

%% TASK 6
journey(X1-Y1, X2-Y2):-
  choose(L, X1),
  deletelist(L, X1, X2),
  append(L, Y1, Y2).
journey(X1-Y1, X2-Y2):-
  choose(L, Y1),
  deletelist(L, Y1, Y2),
  append(L, X1, X2).

% helping predicate, delete list L1 from L2 and get result list R.
deletelist([I], L2, R):-
  delete(I, L2, R).
deletelist([I1, I2], L2, R):-
  delete(I1, L2, R1),
  delete(I2, R1, R).

%% TASK 7
succeeds(Seq):-
  extend([[f,w,g,c,b]-[]], Seq1),
  reversal(Seq1, [], Seq).

extend([H|T], [H|T]):-
  goal(H).
extend([H|T], Final):-
  journey(H, Next),
  \+ visited(Next, T),
  extend([Next, H|T], Final).

reversal([], A, A).
reversal([H|T], A, L):-
  reversal(T, [H|A], L).

%% TASK 8
fee(X1-Y1, X2-Y2, Fee):-
  length(X1, L1),
  length(X2, L2),
  (L1-L2 =:= -1; L1-L2 =:= 1), !,
  fees(Fee, _).
fee(X1-Y1, X2-Y2, Fee):-
  length(X1, L1),
  length(X2, L2),
  (L1-L2 =:= -2; L1-L2 =:= 2),
  fees(_, Fee).
fees(5, 7).

%% TASK 9
cost(Seq, Cost):-
  succeeds(Seq),
  sumcost(Seq, 0, Cost).

sumcost([End], C, C).
sumcost([H1, H2|T], Acc, C):-
  fee(H1, H2, F),
  Acc2 is Acc + F,
  sumcost([H2|T], Acc2, C).

%% ********************** TEST **********************
:- use_module(library(plunit)).

:- begin_tests(safe).
test('1'):-
  safe([b,c,f,g,w]).
test('2'):-
  \+ safe([g,c]).
test('3'):-
  \+ safe([g,w]).
test('-'):-
  safe([]).
test('-'):-
  safe([f]).
test('-'):-
  \+ safe([b,c,g,w]).
test('-'):-
  safe([g]).
test('-'):-
  safe([b]).
:- end_tests(safe).
?- run_tests(safe).


:- begin_tests(goal).
test('goal'):-
  goal([]-[f,w,g,c,b]).
test('not goal'):-
  \+ goal([w,f,c]-[b,g]).
test('-'):-
  \+ goal([b,c,f,g,w]).
test('-'):-
  \+ goal([b]-[b,c,f,g,w]).
test('-'):-
  \+ goal([]-[b,c,f,g]).
test('-'):-
  \+ goal([]-[b,c,f,g,w,a]).
:- end_tests(goal).
?- run_tests(goal).


:- begin_tests(equiv).
test('true1'):-
  equiv([b,c]-[f,w,g], [c,b]-[w,g,f]).
test('false1'):-
  \+ equiv([b]-[f,w,c,g], [c,b]-[g,f,w]).
test('-'):-
  \+ equiv([b,c,f,g,w],[b,c,f,g,w]).
test('-'):-
  \+ equiv([],[]).
test('-'):-
  equiv([]-[b,c,f,g,w],[]-[w,g,f,c,b]).
test('-'):-
  equiv([b,c]-[f,g,w],[c,b]-[w,g,f]).
test('-'):-
  \+ equiv([g]-[b,c,f],[g]-[w,f,c,b]).
test('-'):-
  \+ equiv([g,g]-[b,c,f,w],[g]-[w,f,c,b]).
test('-'):-
  \+ equiv([b,c]-[f,g,w],[c,g]-[w,b,f]).
:- end_tests(equiv).
?- run_tests(equiv).


:- begin_tests(visited).
test('1'):-
  visited([b,c]-[f,w,g], [[c,b]-[w,g,f], [c,b,f,w]-[g]]).
test('-'):-
  \+ visited([b,c,f,g,w],[b,c,f,g,w]).
test('-'):-
  visited([b,c]-[f,g,w],[[]-[b,c,f,g,w],[c,f]-[b,g,w],[c]-[b,f,g,w],[c,b]-[f,g,w
],[c,f]-[b,g,w]]).
test('-'):-
  \+ visited([g,c]-[f,b,w],[[]-[b,c,f,g,w],[c,f]-[b,g,w],[c]-[b,f,g,w],[c,b]-[f,g,w
],[c,f]-[b,g,w]]).
:- end_tests(visited).
?- run_tests(visited).


:- begin_tests(choose).
test('1'):-
  choose([f], [g,f,b]).
test('2'):-
  choose([f,g], [g,f,b]).
test('3'):-
  choose([f,b], [g,f,b]).
test('4'):-
  \+ choose([f,b], [f,b,w,g]).
test('all', all(I == [[f], [f,g], [f,b]])):-
  choose(I, [g,f,b]).
test('-', all(I == [[f], [f,b], [f,c], [f,w]])):-
  choose(I, [b,c,f,w]).
test('-', all(I == [[f]])):-
  choose(I, [f]).
test('-'):-
  \+ choose(_, [w,c,b]).
:- end_tests(choose).
?- run_tests(choose).


:- begin_tests(reversal).
test('reverse', true(L == [1,2,3])):-
  reversal([3,2,1], [], L).
:- end_tests(reversal).
?- run_tests(reversal).

:- begin_tests(fee).
test('5', true(Fee == 5)):-
  fee([f,g]-[b,c,w],[g]-[f,b,c,w],Fee).
test('7', true(Fee == 7)):-
   fee([f,g]-[b,c,w],[]-[f,g,b,c,w],Fee).
:- end_tests(fee).
?- run_tests(fee).

% task six (journey/2) passed all tests.

