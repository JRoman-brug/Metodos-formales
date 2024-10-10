sig Objeto{}
sig Llave,Valor extends Objeto{}
sig Mapeo{map: set Llave -> lone Valor}

fact{Objeto = Llave+Valor}
fact{all o:Objeto | o in (Mapeo.map).Valor or o in  Llave.(Mapeo.map) }
run a{} for 4 but  5 int

--b)
run b{some o:Objeto | o not in Llave and o not in Valor} for 10
//Rta: no puede existir un objeto que no sea llave o valor

--c)
assert funcionalParcial{all l:Llave | l in (Mapeo.map).Valor}
check funcionalParcial
--Rta: No se verifica la aserción, encuentra un contraejemplo 

--d)
run d{some l:Llave | l not in (Mapeo.(map.Valor)) }

