% Trabalho Individual - 2020/2021 
% Daniela Fernandes (a73768)
%--------------------------------------------------------------------
% SICStus PROLOG : Declarações iniciais 
use_module(library(statistics)).
:- discontiguous call_time/2.
:- set_prolog_flag(discontiguous_warnings, off).
:- set_prolog_flag(single_var_warnings, off).
:- set_prolog_flag(unknown, fail).

%--------------------------------------------------------------------
% SICStus PROLOG : definições iniciais 

:- op(900, xfy, '::').
:- dynamic '-'/1.


%--------------------------------------------------------------------
% Importar os dados para a base de conhecimento 
% Leitura do ficheiro com os dados dos pontos e vai inseri-los numa lista 

% Extensão do predicado readDados -> {V,F}
% readDados :- open('/Users/danielaecfernandes/Desktop/Universidade/TP2_SRCR/final.txt', read, STR), 
%            readFileAux(Str,Lines), 
%            close(Str), 
%            insere_pontos(Lines).
% readFileAux(Stream,[]) :-    at_end_of_stream(Stream).
% readFileAux(Stream,[X|L]) :- \+ at_end_of_stream(Stream),
%    					     read(Stream,X),
%    					     readFileAux(Stream,L).

%--------------------------------------------------------------------
% Insere os pontos na base de conhecimento
% Extensão do predicado insere_pontos: Lista ->{V,F}

%insere_pontos([]).
%insere_pontos([X|L]) :- insercao(X), insere_pontos(L).

%--------------------------------------------------------------------
% PREDICADOS AUXILIARES PARA A CRIAÇÃO DO GRAFO

% Lista dos ecopontos 
% ecopontos(L) :- solucoes((ecopontos(La, Lo, C, N, L1, O)), ecopontos(La, Lo, C, N, L1, O), L). 

% Lista os nodos, arestas 
% arestas(L) :- solucoes((aresta(I,F,D)), aresta(I,F,D), L). 

% Lista os pontos de recolha por id, que vão ser os vértices do grafo
% pontosRecolha(L) :- solucoes((pontoRecolha(Id, N, La, Lo)), pontoRecolha(Id, N, La, Lo), L). 



aresta('R da Boavista','Lg Conde-Barao',258.37).
aresta('Lg Conde-Barao','Bqr do Duro',89.00).
aresta('Lg Conde-Barao','Tv do Cais do Tojo',89.94).
aresta('R Cais do Tojo','Tv do Cais do Tojo',31.49).
aresta('R Cais do Tojo','Bqr do Duro',54.50).
aresta('Bqr do Duro','R Dom Luis I',333.45).

inicio('R da Boavista').
fim('R Dom Luis I').

aresta(Nodo, NodoProx):- aresta(Nodo,NodoProx,_).

adjacente(Nodo, NodoProx):- aresta(Nodo, NodoProx, _).

adjacente(Nodo, NodoProx):- aresta(NodoProx, Nodo, _).



%--------------------------------------------------------------------
% ALGORITMO DF (EM PROFUNDIDADE)
dfs(Nodo, Destino, [Nodo|Caminho]):-
    dfsAux(Nodo, Destino, [Nodo], Caminho).

dfsAux(Nodo, Destino, _, [Destino]):-
    adjacente(Nodo, Destino).

dfsAux(Nodo, Destino, Visited, [ProxNodo|Caminho]):-
    adjacente(Nodo, ProxNodo),
    \+ member(ProxNodo, Visited),
    dfsAux(ProxNodo, Destino, [Nodo|Visited], Caminho).

porCusto(Nodo,[Nodo|Caminho],Custo):-
    profundidadeCusto(Nodo,[Nodo],Caminho,Custo).

profundidadeCusto(Nodo, _, [], 0):-
    fim(Nodo).

profundidadeCusto(Nodo,Historico,[NodoProx|Caminho],Custo):-
    custoAdj(Nodo,NodoProx,CustoMovimento),
    nao(membro(NodoProx, Historico)),
    profundidadeCusto(NodoProx,[NodoProx|Historico],Caminho,Custo2),
    Custo is CustoMovimento + Custo2.


custoAdj(Nodo, NodoProx, Custo):-
    nodo(Nodo,NodoProx,Custo).

custoAdj(Nodo, NodoProx, Custo):-
    nodo(NodoProx,Nodo,Custo).

todasSol(L):- findall((S),(porCusto('R da Boavista',S,C)),L).
todasSolCusto(L):- findall((S,C),(porCusto('R da Boavista',S,C)),L).

% Predicado que calcula o percurso com menos metros
melhor(Nodo,Cam,Custo):- findall((Ca,Cus), porCusto(Nodo,Ca,Cus), L),minimo(L,(Cam,Custo)).

% Predicado que calcula o percurso com mais metros
pior(Nodo,Cam,Custo):- findall((Ca,Cus), porCusto(Nodo,Ca,Cus), L),maximo(L,(Cam,Custo)).

% Predicado que calcula o percurso com mais pontos 
maisPontos(L):- todasSol(R),
                longest(R,L).

%--------------------------------------------------------------------
% ALGORITMO BF (EM LARGURA)
largura(Origem,Destino,Caminho) :- 
    bfs1([[Origem]],Destino,Caminho),
    reverse(CaminhoAux,Caminho).

bfs1([[Destino|Caminho]|_],Destino,[Destino|Caminho]).

bfs1([[Caminho1|Caminhos]|_],Destino,Caminho) :-
    extende(Caminho1, NovosCaminhos),
    append(Caminhos, NovosCaminhos, Caminhos1),
    bfs1(Caminhos1,Destino,Caminho).

extende(_,[]).

extende([Paragem|Caminho], NovosCaminhos) :-
    findall([Paragem2, Paragem|Caminho], (adjacente(Paragem,Paragem2), \+ memberchk(Paragem2,[Paragem|Caminho])),NovosCaminhos),!.

%--------------------------------------------------------------------
% ALGORITMO GULOSA

solucaoGulosa(Nodo, Caminho/Custo) :-
    estimativa(Nodo, Estimativa),
    agulosa([[Nodo]/0/Estimativa], CaminhoInverso/Custo/_),
    inverso(CaminhoInverso, Caminho).

gulosa(Caminhos, Caminho) :-
    melhorG(Caminhos, Caminho),
    Caminho = [Nodo|_]/_/_,fim(Nodo).

gulosa(Caminhos, SolucaoCaminho) :-
    melhorG(Caminhos, MelhorCaminho),
    escolhe(MelhorCaminho, Caminhos, OutrosCaminhos),
    expandeG(MelhorCaminho, ExpCaminhos),
    append(OutrosCaminhos, ExpCaminhos, NovoCaminhos),
    gulosa(NovoCaminhos, SolucaoCaminho).

melhorG([Caminho], Caminho) :- !.

melhorG([Caminho1/Custo1/Est1,_/Custo2/Est2|Caminhos], MelhorCaminho) :-
    Est1 =< Est2, !,
    melhorG([Caminho1/Custo1/Est1|Caminhos], MelhorCaminho).

melhorG([_|Caminhos], MelhorCaminho) :- 
    melhorG(Caminhos, MelhorCaminho).

expandeG(Caminho, ExpCaminhos) :-
    findall(NovoCaminho, gulosaAdj(Caminho,NovoCaminho), ExpCaminhos).

gulosaAdj([Nodo|Caminho]/Custo/_, [ProxNodo,Nodo|Caminho]/NovoCusto/Est) :-
    nodo(Nodo, ProxNodo, PassoCusto),\+ member(ProxNodo, Caminho),
    NovoCusto is Custo + PassoCusto,
    estimativa(ProxNodo, Est).

%--------------------------------------------------------------------
% ALGORITMO A Estrela

solucaoEstrela(Nodo, Caminho/Custo) :-
    nodo(Nodo,_,Estimativa),
    estrela([[Nodo]/0/Estima], CaminhoInverso/Custo/_),
    inverso(CaminhoInverso, Caminho).

estrela(Caminhos, Caminho) :-
    melhorE(Caminhos, Caminho),
    Caminho = [Nodo|_]/_/_,fim(Nodo).

estrela(Caminhos, SolucaoCaminho) :-
    melhorE(Caminhos, MelhorCaminho),
    escolhe(MelhorCaminho, Caminhos, OutrosCaminhos),
    expandeEstrela(MelhorCaminho, ExpCaminhos),
    append(OutrosCaminhos, ExpCaminhos, NovoCaminhos),
    estrela(NovoCaminhos, SolucaoCaminho).

melhorE([Caminho], Caminho) :- !.

melhorE([Caminho1/Custo1/Est1,_/Custo2/Est2|Caminhos], MelhorCaminho) :-
    Custo1 + Est1 =< Custo2 + Est2, !,
    melhorE([Caminho1/Custo1/Est1|Caminhos], MelhorCaminho).
    
melhorE([_|Caminhos], MelhorCaminho) :- 
    melhorE(Caminhos, MelhorCaminho).
    
expandeE(Caminho, ExpCaminhos) :-
findall(NovoCaminho, gulosaAdj(Caminho,NovoCaminho), ExpCaminhos). 


%--------------------------------------------------------------------
% QUERIES 
caminhoDepthFirst(Origem, Destino) :- 
    statistics(walltime, [_|T1]),
    dfs(Origem,Destino,R), 
    statistics(walltime, [_|T2]),
    pathCost(R, Custo), 
    printCost(Custo),
    printTime(T2).


custoTodasSolucoesDF(L) :- 
    statistics(walltime, [_|T1]),
    todasSolCusto(R),
    statistics(walltime, [_|T2]), 
    write(R),
    printTime(T2).


caminhoMaisCurtoDF(Origem) :-  
    statistics(walltime, [_|T1]),
    melhor(Origem,Cam,Custo),
    statistics(walltime, [_|T2]),
    write(Cam),
    write(Custo), 
    printTime(T2).

caminhoMaisLongoDF(Origem) :- 
    statistics(walltime, [_|T1]), 
    pior(Origem,Cam,Custo),
    statistics(walltime, [_|T2]), 
    write(Cam),
    write(Custo), 
    printTime(T2).

caminhoComMaisPontosRecolhaDF(R) :-  
    statistics(walltime, [_|T1]), 
    maisPontos(L),
    statistics(walltime, [_|T2]),
    write(L), 
    printTime(T2).

gulosaa(Origem) :- 
    statistics(walltime, [_|T1]), 
    solucaoGulosa(Origem,Caminho/Custo),
    statistics(walltime, [_|T2]),
    write(Caminho),
    write(Custo), 
    printTime(T2).


aEstrela(Origem) :-  
    statistics(walltime, [_|T1]), 
    solucaoEstrela(Origem,Caminho/Custo),
    statistics(walltime, [_|T2]), 
    write(Caminho),
    write(Custo), 
    printTime(T2).



printTime(Time) :- write(Time), write(' milliseconds.\n\n').

printCost(Cost) :- write(Cost), write(' metros.\n\n').


list_sum([Item], Item).
list_sum([Item1,Item2 | Tail], Total) :-
    NewValue is (Item1 + Item2),
    list_sum([NewValue|Tail], Total).

auxPathCost([Elem], Result) :-
    Result = [].
auxPathCost([First, Second|Path], Result) :-
    nodo(First, Second, Cost),
    auxPathCost([Second|Path], NewResult),
    Result = [Cost|NewResult].

pathCost(Path, Custo) :-
    auxPathCost(Path, SumList),
    list_sum(SumList, Custo).

%--------------------------------------------------------------------
% PREDICADOS AUXILIARES 

% Extensão do meta-predicado nao : Questao -> {V,F}
nao(Questao) :- Questao, !, fail.
nao(Questao).

% Extensão do predicado solucoes: Termo, Questao, Resultado -> {V,F}
solucoes(X,Y,R) :- findall(X,Y,R).

% Extensão do predicado solucoesSemRepeticao : Termo, Questao, Resultado -> {V,F}
solucoesSemRepeticao(X,Y,Z) :- setof(X,Y,Z).

% Extensão do predicado insercao : Termo -> {V,F}
insercao(Termo) :- assert(Termo).

% Extenstão do predico inicio_lista : Lista, Resultado -> {V,F}.
inicio_lista([], 0).
inicio_lista([X], X).
inicio_lista([X|T], X).

% Extensao do predicado comprimento : Lista, Resultado -> {V,F}
comprimento(S,N) :- length(S,N).

%Extensao do predicado minimo : Lista, Ponto -> {V,F}
minimo([(P,X)],(P,X)).
minimo([(P,X)|L],(Py,Y)):- minimo(L,(Py,Y)), X>Y.
minimo([(Px,X)|L],(Px,X)):- minimo(L,(Py,Y)), X=<Y.

%Extensao do predicado maximo : Lista, Ponto -> {V,F}
maximo([(P,X)],(P,X)).
maximo([(P,X)|L],(Py,Y)):- maximo(L,(Py,Y)), X<Y.
maximo([(Px,X)|L],(Px,X)):- maximo(L,(Py,Y)), Y=<X.

% Extensao do predicado ultimo : Lista, Real -> {V,F}
ultimo([X],X).
ultimo([H|T], R) :- ultimo(T,R).

% Extensao do predicado inverso : Lista, Resultado -> {V,F}
inverso(Lista,Nova) :- inversoA(Lista, [], Nova).
inversoA([],Lista,Lista).
inversoA([X|Lista], Aux, Nova) :- inversoA(Lista, [X|Aux], Nova).

% Extensão do predicado escolhe : Elemento, Lista, Resultado -> {V,F}
escolhe(Elemento, [Elemento|Xs], Xs).
escolhe(Elemento, [X|Xs], [X|Ys]) :- escolhe(Elemento, Xs, Ys).

% Extensão do predicado tem_elementos : Lista, Lista -> {V,F}
tem_elementos([H], LL) :- member(H, LL).
tem_elementos([H|T], LL) :- member(H,LL), tem_elementos(T,LL).

% Extensão do predicado write_aux : Lista -> {V,F}
write_aux([H]) :- write(H), nl.
write_aux([H|T]) :- write(H), nl, write_aux(T).

 
% Extensão para o predicado longest 
longest([L], L) :- !.
longest([H|T], H) :- 
   length(H, N),
   longest(T, X),
   length(X, M),
   N > M,
   !.
longest([H|T], X) :-
   longest(T, X),
   !.



