sig T{}
sig U{}

sig Sa{r: one T}

run {some s:Sa | #(s.r)=0}
