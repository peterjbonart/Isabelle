theory HomologySModule
  imports Main
          Gamma
          SimplicialSet
          "Category3.FunctorCategory"
          FinsetEquivalence
          SmashProduct
          GammaSetAsEndofunctor
          LoopSpace
begin




locale product_functor =
  F : "functor" A B F +
  G : "functor" C D G
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"
  and C :: "'c comp"
  and D :: "'d comp"
  and G :: "'c \<Rightarrow> 'd"
begin

interpretation AxC : product_category A C
  unfolding product_category_def
  by (simp add: F.A.category_axioms G.A.category_axioms)

interpretation BxD : product_category B D
  unfolding product_category_def
  by (simp add: F.B.category_axioms G.B.category_axioms)

definition FxG where
  "FxG = MkFunctor AxC.comp BxD.comp (\<lambda>x. (F (fst x), G (snd x)))"

lemma is_functor : "functor AxC.comp BxD.comp FxG"
  unfolding functor_def
  apply (simp add: AxC.is_category BxD.is_category)
  unfolding functor_axioms_def
  apply auto
  unfolding FxG_def
        apply simp
       apply simp
      apply simp
     apply simp
    apply simp
   apply simp
  unfolding reverse_equality [OF FxG_def]
proof-
  fix f g h i
  assume seq1: "F.A.arr (fst (AxC.comp (f, g) (h, i)))"
  assume seq2: "G.A.arr (snd (AxC.comp (f, g) (h, i)))"
  then have arr_fghi : "F.A.arr f \<and> G.A.arr g \<and> F.A.arr h \<and> G.A.arr i"
    unfolding AxC.comp_def
    by (metis AxC.arr_char AxC.seq_char F.A.seqE G.A.seqE \<open>F.A.arr (fst (AxC.comp (f, g) (h, i)))\<close> \<open>G.A.arr (snd (AxC.comp (f, g) (h, i)))\<close> fst_conv snd_conv)

  from seq1 have eq: "F.A.cod h = F.A.dom f \<and> G.A.cod i = G.A.dom g"
    unfolding AxC.comp_def
    apply (simp add: arr_fghi)
    using fst_conv by fastforce

  show "FxG (AxC.comp (f, g) (h, i)) = BxD.comp (FxG (f, g)) (FxG (h, i))"
    unfolding FxG_def
    apply (simp add: arr_fghi seq1 seq2)
    unfolding AxC.comp_def BxD.comp_def
    by (simp add: arr_fghi eq)
qed

end

locale compose_with_functor =
  A_B : functor_category A B +
  F : "functor" B C F
  for A :: "'a comp"
  and B :: "'b comp"
  and C :: "'c comp"
  and F :: "'b \<Rightarrow> 'c"
begin


interpretation A_C : functor_category A C
  unfolding functor_category_def
  by (simp add: F.B.category_axioms A_B.A.category_axioms)

interpretation eval: evaluation_functor A B
  unfolding evaluation_functor_def
  unfolding functor_category_def product_category_def
  apply (simp add: A_B.A.category_axioms A_B.B.category_axioms)
  by (simp add: A_B.is_category)

interpretation F_compose: curried_functor A_B.comp A C "(F \<circ> eval.map)" 
  unfolding curried_functor_def
  unfolding binary_functor_def
  unfolding currying_def product_category_def functor_category_def
  apply (simp add: A_B.A.category_axioms A_B.B.category_axioms 
                   A_B.is_category F.B.category_axioms)
  apply (rule_tac functor_comp)
  using eval.is_functor apply simp
  using F.functor_axioms.

definition map where
  "map = F_compose.map"

lemma is_functor: "functor A_B.comp A_C.comp map"
  unfolding map_def
  using F_compose.is_functor.


end


(*
locale gamma_set =
  A: "functor" pointed_fin_set.comp pointed_set.pointed_set_comp A
  for A :: "(nat \<times> nat list) option \<Rightarrow> ('a pointed_set.LC pointed_set.parr) option" +
  assumes
  preserves_point : "category.terminal pointed_set.pointed_set_comp (A (Some (1, [0])))"
begin
end
*)











locale SphereCoeffHomology =
  Coeff: "functor" pointed_fin_set.comp pointed_set.pointed_set_comp Coeff +
  Y : pointed_simplicial_set Y
  for Coeff :: "(nat \<times> nat list) option \<Rightarrow> ('a pointed_set.LC pointed_set.parr) option"
  and Y :: "(nat \<times> nat list) option \<Rightarrow> ('a pointed_set.LC pointed_set.parr) option"
begin

interpretation Gamma : subcategory fin_set.comp pointed_fin_set.PointedArr'
  using Gamma.pointed_fin_set.is_subcategory.

interpretation Delta : simplex.

interpretation Set: category pointed_set.pointed_set_comp
  using pointed_set.is_category.

interpretation sSet : functor_category Delta.comp pointed_set.pointed_set_comp
  unfolding functor_category_def
  by (simp add: Delta.is_category pointed_set.is_category)

definition Inc where
  "Inc = FinsetEquivalence.inclusionFunctor"


definition IncxY where
  "IncxY = product_functor.FxG 
       Gamma.comp pointed_set.pointed_set_comp Inc
       Delta.comp pointed_set.pointed_set_comp Y"

lemma IncxY_functor: "functor 
       (product_category.comp Gamma.comp Delta.comp)
       (product_category.comp pointed_set.pointed_set_comp pointed_set.pointed_set_comp)
       IncxY"
  unfolding IncxY_def
  apply (rule_tac product_functor.is_functor)
  unfolding product_functor_def
  apply (simp add: Y.X.functor_axioms)
  using FinsetEquivalence.inclusion_functor
  unfolding pointed_fin_set.comp_def Inc_def.

lemma GDS_curry: "currying Gamma.comp Delta.comp pointed_set.pointed_set_comp"
  unfolding currying_def
  by (simp add: Gamma.category_axioms Delta.is_category Set.category_axioms)


interpretation smash_with_Y:
         curried_functor "Gamma.comp" "Delta.comp" "pointed_set.pointed_set_comp" "(smash_functor \<circ> IncxY)"
  unfolding curried_functor_def
  unfolding currying_def
  unfolding functor_category_def
  unfolding binary_functor_def
  unfolding product_category_def
  apply (simp add: Gamma.category_axioms Delta.is_category Set.category_axioms)
  apply (rule_tac functor_comp)
  using IncxY_functor apply simp
  using smash_functor.

definition smash_with_Y where
  "smash_with_Y = smash_with_Y.map"

lemma smash_with_Y: "functor Gamma.comp sSet.comp smash_with_Y"
  unfolding smash_with_Y_def
  using smash_with_Y.is_functor.

interpretation coeff_as_endofunctor: gammaset_as_endofunctor Coeff
  unfolding gammaset_as_endofunctor_def
  using Coeff.functor_axioms
  by simp

interpretation sSet_endofunctor: compose_with_functor 
                   simplex.comp pointed_set.pointed_set_comp pointed_set.pointed_set_comp
                   coeff_as_endofunctor.map
  unfolding compose_with_functor_def
  unfolding functor_category_def
  apply (simp add: Delta.is_category pointed_set.is_category)
  using coeff_as_endofunctor.is_functor.

definition sSet_endofunctor where
  "sSet_endofunctor = sSet_endofunctor.map"

lemma sSet_endofunctor : "functor sSet.comp sSet.comp sSet_endofunctor"
  unfolding sSet_endofunctor_def
  using sSet_endofunctor.is_functor.



definition Homology where
  "Homology n = pi0 \<circ> (\<Omega>_tothe n) \<circ> sSet_endofunctor.map \<circ> smash_with_Y"

lemma Homology_functor: "functor Gamma.comp pointed_set.pointed_set_comp (Homology n)"
  unfolding Homology_def
  apply (rule_tac functor_comp)
  using smash_with_Y apply simp
  apply (rule_tac functor_comp)
  using sSet_endofunctor.is_functor apply simp
  apply (rule_tac functor_comp)
  using \<Omega>_tothe_functor apply blast
  using pi0_functor.



end




end
