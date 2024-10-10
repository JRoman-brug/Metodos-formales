open util/ordering[Estado] as Rio

/* granjero y sus poseciones son objetos */
abstract sig Objeto { come: set Objeto }
one sig Granjero, Zorro, Gallina, Grano extends Objeto {}

/* define que comen las poseciones del granjero */
fact { come = Zorro->Gallina + Gallina->Grano}

/* define el estado como el conjunto de objetos a cada orilla */
sig Estado { orillaDerecha: set Objeto,
                       orillaIzquierda: set Objeto
 }

/* En el estado inicial, todo esta en la orilla derecha */
fact { Rio/first.orillaDerecha = Objeto && no first.orillaIzquierda }

/* Estado valido */
pred EsValido[e:Estado] {
	e.orillaDerecha + e.orillaIzquierda = Objeto and -- entre las dos orillas estan todos los objetos
	e.orillaDerecha & e.orillaIzquierda = none    --- no hay un objeto simultaneamente en ambas orillas
}

fact{ all e:Estado | EsValido[e]}

/* definamos las operaciones que me permiten cambiar de estado */

/*pred cruzarRio[ep,el:Estado]{
       (Granjero in ep.OrillaIzquierda implies -- cruzar de izquierda a  derecha
		CruzarIzquierdaDerecha[ep,el]) 

	and

       (Granjero in ep.OrillaDerecha implies -- cruzar de derecha a izquierda
		CruzarDerechaIzquierda[ep,el]) 

}*/

pred CruzarIzquierdaDerecha[e1,e2:Estado]{
   -- el granjero esta en la orilla izquierda
	Granjero in e1.orillaIzquierda and
	some item: e1.orillaIzquierda |
		e2.orillaIzquierda = e1.orillaIzquierda - Granjero - item - (e2.orillaIzquierda).come and
		e2.orillaDerecha = e1.orillaDerecha + Granjero + item
}



pred CruzarDerechaIzquierda[e1,e2:Estado]{
   -- el granjero esta en la orilla derecha
         Granjero in e1.orillaDerecha and
	some item: e1.orillaDerecha |
		e2.orillaDerecha = e1.orillaDerecha - Granjero - item - (e2.orillaDerecha).come and
		e2.orillaIzquierda = e1.orillaIzquierda + Granjero + item
}


fact traces {
	all e:Estado - Rio/last | let ef=e.next |
		CruzarIzquierdaDerecha[e,ef] or CruzarDerechaIzquierda[e,e.next]
}


/*  comandos para mover elementos */

run zorroCruzo { some e:Estado | Zorro in e.orillaIzquierda} for 5
run gallinaCruzo{ some e:Estado | Gallina in e.orillaIzquierda}

run gallinaUltimoEstado{  Gallina in last.orillaIzquierda}

run cruzaronTodos {Objeto in last.orillaIzquierda} for exactly 8 Estado

run cruzaronTodosPosibilidad {some e:Estado | Objeto in e.orillaIzquierda} for 9









