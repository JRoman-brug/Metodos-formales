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

//fact {all disj c1, c2: Colegio | c1.id != c2.id}
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
//Precondiciones: condiciones antes del cambio
//Frame: propiedades que se mantienen en el cambio
//Postcondiciones: condiciones dps del cambio
pred agregarMiembro[c1, c2: Colegio, p: Persona] {
	//Precondicion
	(some c3: Nacional | c3.id != c1.id and  (p in c3.(titulares+suplentes))) and
	(c1.id = c2.id)  and // Mismo colegio
	(c1 in Provincial) and // Que sean provinciales
	(c2 in Provincial) and
	(p in Contador) and  // La persona tiene que ser contadora	

	//agrego a la persona
	(c2.(miembros-(titulares+suplentes)) = c1.(miembros-(titulares+suplentes))+ p) and // son postcondiciones??
	
	//Frame
	(c2.titulares = c1.titulares) and
	(c2.suplentes = c1.suplentes) 
	
	//Postcondiciones ???
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
} for 4
//Genero una instacia donde efectivamente se agrego una persona que esta en el consejo directivo de un colegio nacional

//Exito
//Verificar si cumple la condiciones que sean el mismo colegio
run verificarMismoColegioExito{
	some p:Persona, disj c1,c2:Provincial | 
	c1.id = c2.id and agregarMiembro[c1,c2,p]
}
//Genero una instancia que efectivamente si son el "mismo" colegio

//Preguntar por los casos de exito


//No exito 
//Verificamos si puede agregar una persona no-contador
run verificarPersonaContador{
	some p:  Persona-Contador, disj c1,c2: Provincial | 
	agregarMiembro[c1,c2,p]
}
//No genero una instacia, ya que solo se puede agregar persona contadores

//No exito 
//Verificamos si cumple que los colegios son el mismo (Tienen el mismo ID)
run verificarMismoColegio{
	some p:Persona, disj c1,c2:Provincial | 
	c1.id != c2.id and agregarMiembro[c1,c2,p]
}
//No genero una instancia, ya que al no tener el mismo id, no se estan agregando una persona a un "mismo" colegio

//No exito 
//Verificamos si no se puede agrega un miembro a un colegio Nacional
run verificarColegioNac{
	some p:Persona, cN: Nacional, cP: Provincial |
	agregarMiembro[cN,cP,p]
}
//No se genero uns instancia, ya que solo se puede agregar una persona a los colegios provinciales

//------------------------------------------------------------------------------------------------------------------------------------------------
//punto d

/*
Defina una función que permita obtener el conjunto de abogados o farmac´euticos que son
consejeros titulares del consejo directivo de al menos un colegio y son consejeros suplentes de
a lo sumo un colegio.

Brinde comandos para validar la función definida, y en caso de utilizar el evaluador almacene
capturas de pantalla de las pruebas realizadas.
*/

//1) Titulares al menos 1 colegio
//2) suplente a lo sume 1 colegio
/*fun abogadoFarmaceuticosTit[]: set Persona{
	{p: (Abogado+Farmaceutico) | #(titulares.p) >= 1 and #(suplentes.p)<=1}
}*/
//Preguntar como validar

//Exito
//Ejemplo aleatorio
//p1, p4 y p7 van a cumplir con lo minimo
//p2, p5 con 1 pero no con 2
//p3, p6 con 2 pero no con 1
run prueba{
	some p1:Abogado| 
	(#Abogado = 1) and
	(#(titulares.p1) = 2) and
	(#(suplentes.p1) = 1)

}for 3

//------------------------------------------------------------------------------------------------------------------------------------------------
//punto e

/*
realizar el traspaso de un consejero
suplente del consejo directivo de un colegio a su conjunto de consejeros titulares :

Para que dicha acción pueda realizarse 
la persona no debe formar parte del consejo directivo de un colegio con distinto identificador que el
colegio para el cual se está realizando el traspaso.

Además, luego del traspaso, el colegio deber´a contar con al menos un consejero suplente.
*/

pred suplenteATitular[c1, c2: Colegio, p: Persona]{
	//precondiciones
	({some c:(Colegio-c1-c2) | (titulares.p).id not in c.id}) and
	(p not in c1.titulares) and	

	//traspaso
	(c2.suplentes = c1.suplentes - p) and
	(c2.titulares = c1.titulares + p) and

	//frame
	(c1.id = c2.id) and
	(c1.miembros = c2.miembros) and

	//postcondiciones
	(#(c2.suplentes) >=1)
}

//exito 
//Verificar funcionamiento normal
run puntoDCondNormales{
	some p:Persona, c1,c2:Colegio | 
	(p in c1.suplentes) and
	suplenteATitular[c1,c2,p]
}

//Verificar con colegio Provincial
run puntoDColProv{
	some p:Persona, c1,c2:Provincial | 
	(p in c1.suplentes) and
	suplenteATitular[c1,c2,p]
}for 4 //porque no daban los atomos para los 3 colegios

//Verificar con colegio Nacional
run puntoDColNac{
	some p:Persona, c1,c2:Nacional | 
	(p in c1.suplentes) and
	suplenteATitular[c1,c2,p]
}

//No exito
//La persona a traspasar esta ya en los titulares
run yaEnTitulares{
	some p:Persona, c1,c2:Colegio |
	(p in c1.titulares) and 
	suplenteATitular[c1,c2,p]
}
//No genero instacia, ya que no se puede realizar el traspaso de suplente a titular si ya es titular

//No quedan suplentes
run noSuplentes{
	some p:Persona, c1,c2:Colegio |
	(#(c1.suplentes) = 1) and
	(p in c1.suplentes) and
	suplenteATitular[c1,c2,p]
}
//No genero instancia, ya que si realizar el traspaso 

//No funciona si son 2 colegios diferentes
run colegiosDiferentes{
	some p:Persona, c1,c2:Colegio | 
	(c1.id != c2.id) and
	suplenteATitular[c1,c2,p]
}
//No genero instacia, ya que tienen que ser el mismo colegio

