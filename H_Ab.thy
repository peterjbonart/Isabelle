theory H_Ab
  imports Main
         "~~/src/HOL/Algebra/Group"
         finitePointedSet
         pointedSet
begin








section "Abelian Groups to Gammaset"

locale GroupToGammaset =
  G: comm_group G
  for G:: "('a,'b) monoid_scheme"
begin



end


end
