sig Candidato { }
one sig Alejo, Luca, Carlos, David in Candidato { }
one sig Maria {
	alto : set Candidato,
	moreno : set Candidato,
	buenmozo : set Candidato
}


//a) Existe signatures de 1 atomo, Alejo,Luca,Carlos,Davir que estan incluidas en Candidato
//y Maria que esta relacionado a Candidato mediante 3 relaciones: alto, moreno, buenmozo

//b) Genera atomos de las signatures Alejo, luca, Carlos ,David  y Maria y aveces de Candidatos aparte.
//En ocaciones las relaciones alto, moreno o buenmozo estaban relaciones con Alejo, luca, Carlos, David

//c
fact{#Candidato=4 and Candidato = (Alejo+Luca+Carlos+David)}

//d
fact{#(Maria.alto)=3 and #(Maria.moreno)=2 and #(Maria.buenmozo)=1}
fact{all c:Candidato | c in Maria.alto or c in Maria.moreno or c in Maria.buenmozo}

fact{all a:Alejo, c:Luca| (a in (Maria.moreno) and c in (Maria.moreno)) or (a not in (Maria.moreno) and c not in (Maria.moreno)) }

fact{all l:Luca, c:Carlos| (l in (Maria.alto) and c in (Maria.alto)) or (l not in (Maria.alto) and c not in (Maria.alto)) }

fact{all c:Carlos, d:David | (c in (Maria.alto) and d not in (Maria.alto)) or (c not in (Maria.alto) and d in (Maria.alto)) }

run{some c:Candidato | c in (Maria.alto) and c in (Maria.moreno) and c in (Maria.buenmozo)} for 4
