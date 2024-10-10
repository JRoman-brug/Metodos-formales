abstract sig Target {}
abstract sig Name extends Target { addressBook: some Target }
sig Alias extends Name {}
sig Group extends Name {}
sig Addr extends Target {}


run {#Name = 3 and #Alias = 2 and #Group = 1 and #Addr = 3 and #addressBook = 18} for 10 Target, 6 int
//preguntar bien la diferencia
run{all t:Target | addressBook.t = Name and #Alias = 2 and #Group = 1 and #Addr = 3 }for 6 but 6 int
