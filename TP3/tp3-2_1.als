sig Vehiculo {
	titulares: set Persona,
	autorizados: set Persona,
	placa: lone Patente
}
sig Proveeduria, Comercial, Gerencial extends Vehiculo {}
sig Patente {}
sig Persona {
	id: one DNI,
	carnet: lone LicenciaConducir
}
sig Mayoria18, Mayoria16, Menor in Persona {}
sig DNI {}
sig LicenciaConducir {}
fact {no Vehiculo - Proveeduria - Comercial - Gerencial}
fact {all v: Vehiculo | (some v.placa) implies (some v.titulares and #v.titulares < 3)} //Patentado -> Que hay un titular
fact {no v: Vehiculo | some (v.titulares & v.autorizados)} // No puede existir una persona que sea titular y autorizado
fact {no v: Vehiculo | (no v.placa) and ((some v.titulares) or (some v.autorizados))}
fact {no disj p1, p2: Persona | (p1.id = p2.id)} // Atomos persona con el mismo id
fact {no Persona - Menor - Mayoria16 - Mayoria18} 
fact {no Menor & Mayoria16}
fact {no Menor & Mayoria18}
fact {Mayoria18 in Mayoria16}
fact {all p: Persona| (some titulares.p) implies (p in Mayoria18)}
fact {all p: Persona | (some autorizados.p) implies (p in Mayoria16)}
fact {all p: Persona | (some p.carnet) implies (p in Mayoria16)}
fact {all vg: Gerencial | lone vg.titulares} // gerencial hay 0 o 1 titular
fact {all vp: Proveeduria | #(vp.autorizados) < 4} //Proveeduria hay menos de 4 autorizados

fact {no disj p1, p2: Persona | 
	(some p1.carnet) and 
	(some p2.carnet) and
	(p1.carnet = p2.carnet)
}


//Comento para poder usar la dinamica
/*fact {no disj v1, v2: Vehiculo | 
	(some v1.placa) and 
	(some v2.placa) and
	(v1.placa = v2.placa)
}
*/
/* 
añadir una persona al conjunto de personas autorizadas a manejar un vehículo de proveeduíıa (hasta 3 autorizados). 

Esta acción es posible siempre y cuando la persona posea licencia de conducir y la cantidad original de
personas autorizadas a manejar el vehículo no supere a la cantidad de titulares del mismo:
*/
pred agregarAutorizado[v1, v2: Vehiculo, p: Persona] {
	(one p.carnet) and
	(#v1.autorizados > #v1.titulares) and
	(p in v2.autorizados) and
	(v2.titulares = v1.titulares)
}



//reglas
//Patentado -> Que hay un titular
//No puede existir una persona que sea titular y autorizado
//Proveeduria hay menos de 4 autorizados

//Preguntar como pensar los run's

//Exito
//Cumple todas las condiciones
run cumpleCondiciones{
	some p:Mayoria16, disj v1,v2:Proveeduria | 
	(one p.carnet) and
	(#(v1.autorizados) < 2) and
	(#(v1.autorizados) < #(v1.titulares)) and
	agregarAutorizado[v1,v2,p]
}
//Resultado no genera instancias

//Cumple que la persona tenga licencia
run cumpleLicencia{
	some p:Persona, disj v1,v2: Proveeduria |
	(one p.carnet) and
	agregarAutorizado[v1,v2,p]
}
//Resultado: genera instancias pero hay irregularidades 
//1ra instancia: 1 titular y 2 autorizados (con el predicado no se agrego ninguno)
//2da instancia: 1 titular y 2 autorizados ()
//3ra instancia: 1 titular y 2 autorizados (lo mismo que el caso 2)

//Cumple que no puede haber mas autorizados que titulares
run  masAutorizadosTitulares{
	some p:Persona, disj v1,v2:Vehiculo |
	(#(v1.autorizados) < #(v1.titulares)) and
 	agregarAutorizado[v1,v2,p]
}
//Resultado: no genero instancias

//Preguntar como hacer los test, porque estan funcionando por los facts, no por el pred
//Preguntar como es la justificacion de los no exitos
//No exito
//Tratar de agregar a una persona sin licencia
run noLicencia{
	some p:Mayoria18, disj v1,v2: Proveeduria |
	(no p.carnet) and
	agregarAutorizado[v1,v2,p]
}
//Resultado: no genera instancias, ya que no se puede alguien sin carnet no puede ser autorizado

//Tratar de agregar un vehiculo no de proveeduria
run noProveeduria{
	some p:Persona, disj v1,v2:(Vehiculo-Proveeduria) | 
	agregarAutorizado[v1,v2,p]
}
//Resultado: 
//1ra instancia: genero v1 es gerencial y v2 es comercial
//2ra instancia: genero v1 es comercial y v2 es comercial
//3ra instancia: genero v1 es comercial y v2 es gerencial

//Tratar de agregar a alguien ya autorizado
run yaAutorizado{
	some p:Persona, disj v1,v2:Proveeduria |
	(p in v1.autorizados)and
	agregarAutorizado[v1,v2,p]
}
//Resultado: genero una instancia 
//1ra instancia: hay irregularidades, no respeta la misma cantidad de  autorizados, ademas de agregar a alguien ya autorizado

//Tratar de usar el mismo atomo
run mismoAtomo{
	some p:Persona, v1,v2:Proveeduria |
	(v1 = v2) and 
	agregarAutorizado[v1,v2,p]
}
//Resultado: pudo generar instancias

//Tratar de agregar mas de 3 autorizados
run mas3Autorizados{
	some p:Persona, disj v1,v2:Proveeduria |
	(#(v1.autorizados) = 3) and
	(v1.autorizados & p = none) and 
	agregarAutorizado[v1,v2,p]
}for 4
//Resultado: no genra instancias, ya que no un vehiculo de proveeduria no puede tener mas de 3 autorizados


//La cantidad de autorizados supera la cantidad de titulares del vehiculo
run autorizadosSuperaTitulares{
	some p:Persona, disj v1,v2:Proveeduria |
	(#(v1.titulares) = 1) and
	(v1.autorizados & p = none) and 
	(#(v1.autorizados ) = 1) and
	agregarAutorizado[v1,v2,p]
}for 4

