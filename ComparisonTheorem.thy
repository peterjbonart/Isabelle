theory ComparisonTheorem
  imports Main
         "HOL-Algebra.Group"
         HomologySphereCoefficients
         H_Ab
begin

locale comparison_theorem =
  A : comm_group A +
  H : Homology "GroupToGammaset.HFunctor A" Y
  for A :: "('a, 'b) monoid_scheme"
  and Y :: "(nat \<times> nat list) option \<Rightarrow> ('a pointed_set.LC pointed_set.parr) option"
begin



(*TODO: Formulate that H.Homology = HFunctor (pi_n \<circ> HA \<circ> Y) 
  For that to make sense we need to explain how pi_n (HA \<circ> Y) is an abelian group.*)

lemma comparison1 :
   "H.Homology = undefined"
  oops



end
