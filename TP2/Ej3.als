one sig Juan, Pedro {}
sig Culpable in univ {}
//fact { Juan not in Culpable }
fact { Juan in Culpable implies Pedro in Culpable }
assert conclusion { Pedro not in Culpable }

//a Hay 3 signatures que estan en universo, Juan, Pedro y Culpable
//b El modelo quiere representar una sentecia logica, dado 1 atomo de cada signature Juan y Pedro
//Se quiere saber si pedro es culpable o no

//c, El significado del comando run genera atomos mediante las signatures y facts declarados
//Las caracteristicas de las instancias son: Juan no es culpable y hay veces que Pedro o un atomo 
//del universo es culpable
run{}

//d, La herramienta muestra contraejemplo donde pedro pertenece a la signature
//culpable 
//Sigue pasando lo mismo, solo que Juan puede ser o no culpable
check conclusion
