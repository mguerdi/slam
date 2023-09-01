min_size(20).
max_size(150).
max_steps(10000000).

boltzmann_index(R):-R<0.35700035696434995.
boltzmann_lambda(R):-R<0.6525813160382378.
boltzmann_leaf(R):-R<0.7044190409261122.

pickIndex(_,R,0,[V|_],V0,N,N):-boltzmann_leaf(R),!,
  unify_with_occurs_check(V0,V).
pickIndex(Max,_,s(X),[_|Vs],V,N1,N3):-
  next(Max,NewR,N1,N2),
  pickIndex(Max,NewR,X,Vs,V,N2,N3).

next(Max,R,N1,N2):-N1<Max,N2 is N1+1,random(R).

ranTypable(Max,R,X,V,Vs,N1,N2):-boltzmann_index(R),!,
  random(NewR),
  pickIndex(Max,NewR,X,Vs,V,N1,N2).
ranTypable(Max,R,l(A),(X->Xs),Vs,N1,N3):-boltzmann_lambda(R),!,
  next(Max,NewR,N1,N2),
  ranTypable(Max,NewR,A,Xs,[X|Vs],N2,N3).
ranTypable(Max,_R,a(A,B),Xs,Vs,N1,N5):-
  next(Max,R1,N1,N2),
  ranTypable(Max,R1,A,(X->Xs),Vs,N2,N3),
  next(Max,R2,N3,N4),
  ranTypable(Max,R2,B,X,Vs,N4,N5).

ranTypable(X,T,Size,Steps):-
  max_size(Max),
  min_size(Min),
  max_steps(MaxSteps),
  between(1,MaxSteps,Steps),
    random(R),
    ranTypable(Max,R,X,T,[],0,Size0),
  Size0>=Min,
  !,
  Size is Size0+1.


suc_to_n(0, 0).
suc_to_n(s(N), M) :- suc_to_n(N, N_as_int), M is N_as_int + 1.

lam_to_string(0, PP) :- atom_string(0, PP).
lam_to_string(s(N), PP) :- suc_to_n(s(N), N_plus_one), atom_string(N_plus_one, PP).
lam_to_string(l(A), PP) :-
  lam_to_string(A, Body),
  string_concat("λ(", Body, PP_tmp),
  string_concat(PP_tmp, ")", PP).
lam_to_string(a(A, B), PP) :-
  lam_to_string(A, PP_A),
  lam_to_string(B, PP_B),
  string_concat(PP_A, " ", PP_tmp),
  string_concat(PP_tmp, PP_B, PP).

example_term(T) :- T = l(l(a(a(a(l(a(a(l(0), 0), l(l(0)))), l(a(l(0), 0))), a(l(l(l(l(a(0, l(a(l(l(a(s(0), a(l(l(0)), a(l(l(a(0, l(0)))), l(a(l(l(a(a(s(0), l(l(a(l(l(a(a(a(l(a(l(a(s(0), 0)), l(l(a(a(s(0), a(s(0), l(l(l(l(l(0))))))), 0))))), s(0)), l(l(a(l(l(0)), a(l(l(a(l(a(a(0, s(0)), l(0))), l(a(l(s(s(0))), 0))))), 0))))), 0))), s(0))))), 0))), s(0)))))))), l(0)))))))), s(0))), 0))).

n_terms(0, []).
n_terms(N, [Steps|Ts]) :-
  ranTypable(X,T,Size,Steps),
  M is N - 1,
  n_terms(M, Ts).

%
% These never backtrack. Use set_random(seed(42)) to observe no differences!
%

next_never(Max,R,N1,N2):-N1<Max, !, N2 is N1+1, ! ,random(R).

ranTypableNever(Max,R,X,V,Vs,N1,N2):-boltzmann_index(R),!,
  random(NewR), !,
  pickIndex(Max,NewR,X,Vs,V,N1,N2).
ranTypableNever(Max,R,l(A),(X->Xs),Vs,N1,N3):-boltzmann_lambda(R),!,
  next_never(Max,NewR,N1,N2), !,
  ranTypableNever(Max,NewR,A,Xs,[X|Vs],N2,N3).
ranTypableNever(Max,_R,a(A,B),Xs,Vs,N1,N5):-
  next_never(Max,R1,N1,N2), !,
  ranTypableNever(Max,R1,A,(X->Xs),Vs,N2,N3), !,
  next_never(Max,R2,N3,N4), !,
  ranTypableNever(Max,R2,B,X,Vs,N4,N5).

ranTypableNever(X,T,Size,Steps):-
  max_size(Max),
  min_size(Min),
  max_steps(MaxSteps),
  between(1,MaxSteps,Steps),
    random(R),
    ranTypableNever(Max,R,X,T,[],0,Size0),
  Size0>=Min,
  !,
  Size is Size0+1.


n_terms_never(0, []).
n_terms_never(N, [Steps|Ts]) :-
  ranTypableNever(X,T,Size,Steps),
  M is N - 1,
  n_terms(M, Ts).
