sig Objeto{}
sig Llave, Valor extends Objeto{}
sig Mapeo {map:  Llave set -> lone Valor}

fact{Objeto = Llave+Valor}
fact{all l:Llave, v:Valor | l in (Mapeo.(map.Valor)) and v in (Llave. (Mapeo.map))}

run{#Valor = 3 and #Llave=3}for 6

//b 
run{some l:Llave, v:Valor | l not in (Mapeo.(map.Valor)) or v not in (Llave.(Mapeo.map))}
//Rta no se encontro ninguna instancia donde se compruebe esto

//c
assert funcionalParcial{all l:Llave | l in (Mapeo.map).Valor}
check funcionalParcial

//d
run d{some l:Llave | l not in (Mapeo.(map.Valor)) }

