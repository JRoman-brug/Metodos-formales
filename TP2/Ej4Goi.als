sig Candidato { }
//Por el one antes de Alejo
one sig Alejo, Luca, Carlos, David in Candidato { }
one sig Maria {
	alto : set Candidato,
	moreno : set Candidato,
	buenmozo : set Candidato
}
fact {#(Maria.alto)=3 and #(Maria.moreno)=2 and #(Maria.buenmozo)=1}
fact{(all c:Candidato | c in Maria.alto or c in Maria.moreno or c in Maria.buenmozo)}
fact{all  a:Alejo,l:Luca | (a in Maria.moreno and l in Maria.moreno) or (a not in Maria.moreno and l not in Maria.moreno)}
fact{all  c:Carlos,l:Luca | (c in Maria.alto and l in Maria.alto) or (c not in Maria.alto and l not in Maria.alto)}
fact{all  c:Carlos,d:David | (c in Maria.alto and d not in Maria.alto) or (c not in Maria.alto and d in Maria.alto)}
fact{#Candidato=4 and Candidato=Alejo+Luca+Carlos+David}
run rD{some c:Candidato | c in Maria.alto and c in Maria.buenmozo and c in Maria.moreno} for 4 Candidato
