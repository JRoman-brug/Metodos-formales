sig T{}
sig U{}

sig Sg{r: T one -> U}

run {some s:Sg | #(s.(r.U)) >2 and #(T.(s.r)) >2} for 4
