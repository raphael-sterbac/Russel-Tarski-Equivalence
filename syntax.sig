lvl : Type
ty : Type
term(var_term) : Type
russ_term(r_var_term) : Type

Prod : ty -> (bind term in ty) -> ty
Decode : lvl -> term -> ty
U : lvl -> ty

Lambda : ty -> (bind term in ty) -> (bind term in term) -> term
App : ty -> (bind term in ty) -> term -> term -> term
cProd : lvl -> term -> (bind term in term) -> term
cU : lvl -> lvl -> term
cLift : lvl -> lvl -> term -> term

r_Prod : russ_term -> (bind russ_term in russ_term) -> russ_term
r_U : lvl -> russ_term
r_Lambda : russ_term -> (bind russ_term in russ_term) -> (bind russ_term in russ_term) -> russ_term
r_App : russ_term -> (bind russ_term in russ_term) -> russ_term -> russ_term -> russ_term