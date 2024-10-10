open util/ordering[Estado] as State

//tiene que ser unico
one sig Libro { 
	paginas: some Pagina,
	//Los marcadores del libro estaran controlados por el estado
	//marcadores: set Marcador 
}
sig Marcador { 
	//Ya el marcador no tiene que tener el control la pagina, se lo pasa al estado
	//pag: Pagina 
}
sig Pagina { }
fact {
	//Modificando para utilizar la dinamica
	//all l: Libro | 
	//#Marcador >= 0
	all e:Estado | 
	#Libro.(e.estadoLibro) >=0
}
fact {
	//Modificado para utilizar la dinamica
	//all l: Libro | 
	//#l.marcadores < 4
	all e:Estado | 
	#Libro.(e.estadoLibro) < 4
}
fact {
	//Modificado para utilizar la dinamica
	//no m: Marcador, l: Libro | 
	//(m in l.marcadores) and 
	//(m.pag !in l.paginas) 
	no m: Marcador, l: Libro, e:Estado| 
	m in l.(e.estadoLibro) and
	m.(e.estadoMarcadores) ! in l.paginas
}
fact{
	no m:Marcador, l:Libro , e:Estado |
	m not in l.(e.estadoLibro) and
	m in (e.estadoMarcadores).Pagina
	
}

//creacion de estados
sig Estado{
	estadoLibro: Libro ->  set Marcador,
	estadoMarcadores: Marcador -> one Pagina
}
//Estado inicial
//Sin marcadores
//Problema aca
fact{

}
//Estado valido
pred esValido[e:Estado]{
	Libro.(e.estadoLibro) in Marcador and
	(e.estadoMarcadores).Pagina in Marcador  
}

fact{
	all e:Estado | esValido[e]
}

//operaciones para cambiar los marcadores
pred agregarMarcador[m:Marcador, p:Pagina, l:Libro,e1,e2:Estado]{
	e2.estadoMarcadores = e1.estadoMarcadores + (m -> p) and
	e2.estadoLibro = e1.estadoLibro + (l -> m) 
}
pred eliminarMarcador[m:Marcador, l:Libro,e1,e2:Estado]{
	e2.estadoMarcadores = e1.estadoMarcadores - (m -> (m.(e1.estadoMarcadores)))and
	e2.estadoLibro = e1.estadoLibro - (l -> m) 
}

//Preguntar si se puede reutilizar predicados
/*
pred modificarMarcador[m:Marcador, p1,p2:Pagina,l:Libro,e1,e2:Estado]{
	some e3:Estado |
	eliminarMarcador[m,p2,l,e1,e3] and
	agregarMarcador[m,p2,l,e3,e2]
}
*/
pred modificarMarcador[m:Marcador, p1,p2:Pagina,l:Libro,e1,e2:Estado]{
	e2.estadoMarcadores = e1.estadoMarcadores - (m -> p1) + (m -> p2)
}


//Traces, forma que se de la dinamica
fact {
	all e:Estado - State/last | some l:Libro, p1,p2:Pagina, m:Marcador| let ef=e.next |
		agregarMarcador[m,p1,l,e,ef] or 
		eliminarMarcador[m,l,e,e.next] or 
		modificarMarcador[m,p1,p2,l,e,ef]
}

//testing
run test{
}







