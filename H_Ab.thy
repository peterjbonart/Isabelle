theory H_Ab
  imports Main
         "HOL-Algebra.Group"
         pointedSet
begin


section "Abelian Groups to Gammaset"

locale GroupToGammaset =
  G: comm_group G
  for G:: "('a,'b) monoid_scheme"
begin

interpretation pointed_set.

definition HFunctor :: "gamma \<Rightarrow> 'a LC parr" where
  "HFunctor x = undefined"




end


end
