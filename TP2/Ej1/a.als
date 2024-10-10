sig T{}
sig U{}

sig Sa{r: lone T}

run {some s:Sa | #(s.r)=2}
