sig Colegio { 
	miembros: some Persona,
	titulares: some Persona,
	suplentes: set Persona,
	id: one ID
}
sig Provincial, Nacional extends Colegio {}
sig ID {}
sig Persona {
	dni: one DNI,
	matricula: lone Matricula
}
sig Contador, Abogado, Farmaceutico extends Persona {}
sig DNI {}
abstract sig Matricula {}

sig MatriculaC, MatriculaA, MatriculaF extends Matricula {}
fact {all disj p1, p2: Persona | p1.dni != p2.dni}
fact {no disj p1, p2: Persona | (some p1.matricula) and (some p2.matricula) and
	(p1.matricula = p2.matricula)
}

fact {all disj c1, c2: Colegio | c1.id != c2.id}
fact {Colegio = (Provincial+Nacional)}
fact {all c: Colegio | no (c.titulares & c.suplentes)}
fact {all c: Colegio | (c.titulares + c.suplentes) in c.miembros}
fact {all p: Persona | (some (MatriculaC & p.matricula)) implies (p in Contador)}
fact {all p: Persona | (some (MatriculaA & p.matricula)) implies (p in Abogado)}
fact {all p: Persona | (some (MatriculaF & p.matricula)) implies (p in Farmaceutico)}

fact {all p1, p2: Persona, c: Colegio | ((p1 in c.miembros) and (p2 in c.miembros))
	implies (mismaProfesion[p1,p2] and matriculadosParaMismaProfesion[p1,p2])
}

fact {all c: Provincial | (#c.titulares =< 3) and (#c.suplentes =< #c.titulares)}
fact {all c: Nacional | (#c.titulares < 5) and (#c.suplentes =< 2)}

pred mismaProfesion[p1, p2: Persona]{ 
	(p1+p2 in Contador) or (p1+p2 in Abogado) or (p1+p2 in Farmaceutico) 
}

pred matriculadosParaMismaProfesion[p1, p2: Persona] {
	((some (p1.matricula & MatriculaC)) and (some (p2.matricula & MatriculaC))) or
	((some (p1.matricula & MatriculaA)) and (some (p2.matricula & MatriculaA))) or
	((some (p1.matricula & MatriculaF)) and (some (p2.matricula & MatriculaF)))
}

/* 
Incorpore al modelo el siguiente predicado, el cual modela el comportamiento de
añadir una persona al conjunto de miembros de un colegio provincial de contadores. 
Esta acción es posible siempre y cuando la persona pertenezca al consejo directivo 
de un colegio nacional para esa profesi´on:
*/

pred agregarMiembro[c1, c2: Colegio, p: Persona] {
	//Precondicion
	(no c3: Nacional | (p in c3.(titulares+suplentes))) and //No existe un colegio nacional que tenga en los directivos a la persona
	(p in c2.miembros) and
	//Frame
	(c1.titulares in c2.titulares) and
	(c1.suplentes in c2.suplentes)
}

//Exito -> dar instancias
//No-exito -> no da instancias
//6 de cada uno generalmente

//Exito
//Verificamos si el predicado cumple la condicion de que para agregar una persona
//a un colegio provincial, este tiene que pertencer al consejo directivo de un colegio
//nacional
run verificarPertenceColegioNacional{some p:Persona, c:Nacional, disj c1,c2 : Provincial| 
	p in c.(titulares+suplentes) and agregarMiembro[c1,c2,p]
} for 5
//No se genero la instacia porque al querer agregar una persona que este en el consejo directivo a un colegio provincial


//Preguntar por los casos de exito


//No exito 
//Verificamos si puede agregar una persona no-contador
run verificarPersonaContador{
	some p:  Persona-Contador, disj c1,c2: Provincial | 
	agregarMiembro[c1,c2,p]
}
//Genero una instancia donde se pudo agregar una persona no-contador a un colegio de contadores

//No exito 
//Verificamos si cumple que los colegios son el mismo (Tienen el mismo ID)
run verificarMismoColegio{
	some p:Persona, disj c1,c2:Provincial | 
	c1.id != c2.id and agregarMiembro[c1,c2,p]
}
//Se generaron 2 colegios con diferentes ID's

//No exito 
//Verificamos si no se puede agrega un miembro a un colegio Nacional
run verificarColegioNac{
	some p:Persona, cN: Nacional, cP: Provincial |
	agregarMiembro[cN,cP,p]
}
//Genero una instancia donde tenian no agregaba a la persona a lo miembro


//No exito 
//Agregar una persona que ya exista en el colegio
run verificarPersonaPertenece{
	some p:Persona, disj c1,c2:Provincial | 
	p in c1.miembros and
	p not in c2.miembros and 
	agregarMiembro[c1,c2,p]
}

//No genero 


