//Ponemos as Rio para referimos a las utilidades de la lib, ejemplo Rio/first, Rio/next,
//Cuando usamos multiples estados deberiamos usar varias 
open util/ordering[Estado] as Rio

//Granjero y sus poseciones son objetos
abstract sig Objeto {come:set Objeto}
one sig Granjero, Zorro, Gallina, Grano extends Objeto{}

/*define que comen las poseciones del granjero */
fact { come = Zorro -> Gallina + Gallina -> Grano}

/* define el estad como el conjunto de objeto a cada orilla*/
sig Estado {
	orillaDerecha:set Objeto, 
	orillaIzquierda: set Objeto
}

/*En el estado inicial, todo esta en la orilla derecha*/
fact { Rio/first.orillaDerecha = Objeto && no Rio/first.orillaIzquierda}

//Estado valido: que cosas deben satisfacer los estados validos, sino son invalidos XD
pred EsValido[e:Estado]{
	e.orillaDerecha + e.orillaIzquierda = Objeto and //entre las dos orilla estan todos los objetos
	e.orillaDerecha & e.orillaIzquierda = none // no hay un objeto simultaneamente en ambas orillas
	
}
//No importa donde hagas el chequeo que todos los estados son validos, indicar donde lo haces. 
fact{ all e:Estado | EsValido[e]}//Para decir que todos los estados sean validos, es 1 forma de hacerlo

//definamos las operaciones que me permiten cambiar de estado 
//ep: estado partida, el: estado llegada
//Forma 1
pred cruzarRio[ep,el: Estado ]{
	//No hay que preguntar por algun atomo granjero por es unico 
	Granjero in ep.orillaIzquierda implies  --Cruzar de izquierda a derecha
		CruzarIzquierdaDerecha[ep,el] 

	and
	
	Granjero in ep.orillaDerecha implies  --Cruzar de derecha a izquierda 
		CruzarDerechaIzquierda[ep,el] 
	
}

pred CruzarIzquierdaDerecha[ep,el:Estado]{
	//El granjero esta en la orilla izquierda
	some item: ep.orillaIzquierda | //Elijo un objeto cualquiera(incluido el granjero para el caso que quiera cruzar solo)
		el.orillaIzquierda= ep.orillaIzquierda- Granjero-item - el.orillaIzquierda.come and // si saco el ultimo no se respeta el problema
		el.orillaDerecha = ep.orillaDerecha +Granjero+ item // actualizo la otra orilla 
}
pred CruzarDerechaIzquierda[ep,el:Estado]{
	//El granjero esta en la orilla izquierda
	some item: ep.orillaDerecha| //Elijo un objeto cualquiera(incluido el granjero para el caso que quiera cruzar solo)
		el.orillaDerecha = ep.orillaDerecha- Granjero-item - el.orillaDerecha.come and // si saco el ultimo no se respeta el problema
		el.orillaIzquierda = ep.orillaIzquierda+Granjero+item // actualizo la otra orilla
}

//Forma 2
//pred cruzarRioCon[OrIzP, OrDeP, OrIzL, OrDeL: set Objeto]


//
fact traces{
	all e:Estado - Rio/last |
		CruzarIzquierdaDerecha[e,e.next] or CruzarDerechaIzquierda[e,e.next]//Para no poner e.next varias veces -> let estFin = e.next
}

//comandos para mover elementos
run zorro {some e:Estado | Zorro in e.orillaIzquierda} 

run gallina {some e:Estado | Gallina in e.orillaIzquierda}

run gallinaUltimoEstado {Gallina in last.orillaIzquierda}

run cruzaronTodos {Objeto in last.orillaIzquierda} for 9 

run cruzaronTodosPosibilidades{some e:Estado | }
