theory ComparisonTheorem
  imports Main
         "HOL-Algebra.Group"
         HomologySphereCoefficients
         ReducedHomology
         H_Ab
begin



context pointed_set
begin

section "Change of universe functors"


definition embed_functor :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a parr option \<Rightarrow> 'b parr option" where
  "embed_functor F = MkFunctor pointed_set_comp pointed_set_comp
                 (\<lambda>f. Some (MkArr 
                 (pointed_image F (Dom' (the f))) 
                 (pointed_image F (Cod' (the f)))  
                  (\<lambda>x. F (fst (the f) (SOME a'. x = F a')))))"


interpretation P : category pointed_set_comp
  using is_category.

lemma arr_MkArr :
  assumes "Obj' A" "Obj' B" "f \<in> snd A \<rightarrow> snd B" "f (fst A) = fst B"
  shows "P.arr (Some (MkArr A B f))"
  unfolding P.arr_char
  apply simp
  apply (simp add: Arr'_def MkArr_def)
  using \<open>Obj' A\<close> unfolding Obj'_def apply simp
  unfolding setcat.Arr_def
  using assms
  unfolding Obj'_def by auto


lemma embed_functor : 
  assumes F_inj : "\<And>x y. F x = F y \<Longrightarrow> x = y"
  shows "functor pointed_set_comp pointed_set_comp (embed_functor F)"
  unfolding functor_def
  apply (simp add: is_category)
  unfolding functor_axioms_def
  apply auto
      apply (simp add: embed_functor_def)
proof-
  have F_some : "\<And>x. (SOME a'. F x = F a') = x"
  proof
    show "\<And>x. F x = F x" using refl.
    show "\<And>x a'. F x = F a' \<Longrightarrow> a' = x" using F_inj by simp
  qed

  show arr: "\<And>f. P.arr f \<Longrightarrow> P.arr (embed_functor F f)"
    unfolding embed_functor_def
    apply simp
    apply (rule_tac arr_MkArr)
  proof-
    fix f :: "'a parr option"
    assume "P.arr f"
    then have arr_f: "Arr' (the f)"
      unfolding arr_char by simp
    show "Obj' (pointed_image F (fst (snd (the f))))" 
      apply (rule_tac pointed_image_obj)
      using arr_f
      unfolding Arr'_def by simp
    show "Obj' (pointed_image F (snd (snd (the f))))" 
      apply (rule_tac pointed_image_obj)
      using arr_f
      unfolding Arr'_def by simp
    show "(\<lambda>x. F (fst (the f) (SOME a'. x = F a')))
         \<in> snd (pointed_image F (fst (snd (the f)))) \<rightarrow> snd (pointed_image F (snd (snd (the f))))"
      unfolding pointed_image_simps
      apply auto
    proof-
      fix x
      assume x_in: "x \<in> snd (Dom' (the f))"
      have fx_in : "fst (the f) x \<in> snd (Cod' (the f))"
        using arr_f
        unfolding Arr'_def setcat.Arr_def
        using x_in by auto
      show "F (fst (the f) (SOME a'. F x = F a')) \<in> F ` snd (snd (snd (the f)))"
        unfolding F_some
        using fx_in by simp
    qed
    have some_fst : "(SOME a'. fst (pointed_image F (fst (snd (the f)))) = F a') =
                     fst (Dom' (the f))"
      unfolding pointed_image_simps
      apply simp
    proof
      show "F (fst (fst (snd (the f)))) = F (fst (fst (snd (the f))))" using refl.
      show "\<And>a'. F (fst (fst (snd (the f)))) = F a' \<Longrightarrow> a' = fst (fst (snd (the f)))"
        using F_inj by simp
    qed
    show "F (fst (the f) (SOME a'. fst (pointed_image F (fst (snd (the f)))) = F a')) =
         fst (pointed_image F (snd (snd (the f))))"
      unfolding pointed_image_simps
      apply simp
      unfolding F_some
      using arr_f
      unfolding Arr'_def
      by simp
  qed
  show dom : "\<And>f. P.arr f \<Longrightarrow> P.dom (embed_functor F f) = embed_functor F (P.dom f)"
    unfolding P.dom_char [OF arr]
    unfolding embed_functor_def
    apply (simp add: MkArr_def pointed_image_simps)
    unfolding P.dom_char
    apply (simp add: Id'_def)
    apply (rule_tac ext)
    apply auto
    unfolding F_some by simp_all
  show cod : "\<And>f. P.arr f \<Longrightarrow> P.cod (embed_functor F f) = embed_functor F (P.cod f)"
    unfolding P.cod_char [OF arr]
    unfolding embed_functor_def
    apply (simp add: MkArr_def pointed_image_simps)
    unfolding P.cod_char
    apply (simp add: Id'_def)
    apply (rule_tac ext)
    apply auto
    unfolding F_some by simp_all
  fix g f :: "'a parr option"
  assume arr_gf : "P.seq g f"
  have arr_egf : "P.seq (embed_functor F g) (embed_functor F f)"
    apply (rule_tac P.seqE [OF arr_gf])
    apply (rule_tac P.seqI)
    unfolding dom cod
    by (simp_all add: arr)
  show "embed_functor F (pointed_set_comp g f) =
           pointed_set_comp (embed_functor F g) (embed_functor F f)"
    apply (rule_tac P.seqE [OF arr_egf])
    apply (rule_tac P.seqE [OF arr_gf])
    using arr_egf arr_gf
    apply (rule_tac reverse_equality)
    apply (rule_tac P.comp_eq_char2)
    unfolding dom cod
        apply (simp_all add: arr)
  proof-
    fix x
    assume arr_f : "P.arr f"
    assume arr_g : "P.arr g"
    assume fx_in_g : "fst (the (embed_functor F f)) x \<in> snd (fst (snd (the (embed_functor F g))))"
    have g_eq : "snd (fst (snd (the (embed_functor F g)))) = F ` snd (fst (snd (the g)))"
      unfolding embed_functor_def
      by (simp add: MkArr_def pointed_image_simps arr_g)

    assume x_in_f : "x \<in> snd (fst (snd (the (embed_functor F f))))"
    have f_eq: "snd (fst (snd (the (embed_functor F f)))) = F ` snd (fst (snd (the f)))"
      unfolding embed_functor_def
      by (simp add: MkArr_def pointed_image_simps arr_f)
    assume x_in_gf : "x \<in> snd (fst (snd (the (embed_functor F (pointed_set_comp g f)))))"
    have gf_eq : "snd (fst (snd (the (embed_functor F (pointed_set_comp g f))))) =
                  F ` snd (fst (snd (the (pointed_set_comp g f))))"
      unfolding embed_functor_def
      by (simp add: MkArr_def pointed_image_simps arr_gf)

    show "P.arr f \<Longrightarrow> P.arr g \<Longrightarrow> 
         fst (the (embed_functor F g)) (fst (the (embed_functor F f)) x) =
         fst (the (embed_functor F (pointed_set_comp g f))) x"
      using arr_gf
      apply (subst embed_functor_def)
      using fx_in_g
      unfolding g_eq
      apply (simp add: MkArr_def pointed_image_simps)
      apply (subst embed_functor_def)
      using x_in_f
      unfolding f_eq
      apply (simp add: MkArr_def pointed_image_simps)
      unfolding F_some
      apply (subst embed_functor_def)
      using x_in_gf
      unfolding gf_eq
      apply (simp add: MkArr_def pointed_image_simps)
      apply (subst fst_comp_char)
        apply simp_all
    proof-
      assume "x \<in> F ` snd (fst (snd (the f)))"
      then obtain a where a_def: "a \<in> snd (fst (snd (the f))) \<and> x = F a"
        by auto
      show "(SOME a'. x = F a') \<in> snd (fst (snd (the f)))"
        unfolding conjunct2 [OF a_def]
        unfolding F_some
        using conjunct1 [OF a_def].
    qed
  qed
qed


definition Inl_functor :: "'a parr option \<Rightarrow> ('a + 'b) parr option" where
  "Inl_functor = embed_functor Inl"

definition Inr_functor :: "'b parr option \<Rightarrow> ('a + 'b) parr option" where
  "Inr_functor = embed_functor Inr"

lemma Inl_functor : "functor pointed_set_comp pointed_set_comp Inl_functor"
  unfolding Inl_functor_def
  apply (rule_tac embed_functor)
  by simp

lemma Inr_functor : "functor pointed_set_comp pointed_set_comp Inr_functor"
  unfolding Inr_functor_def
  apply (rule_tac embed_functor)
  by simp


end






locale comparison_theorem =
  A : comm_group A +
  Y : pointed_simplicial_set Y
  for A :: "('a, 'b) monoid_scheme"
  and Y :: "(nat \<times> nat list) option \<Rightarrow> ('a pointed_set.LC pointed_set.parr) option"
begin

interpretation P: pointed_set.

interpretation FunCat : functor_category pointed_fin_set.comp P.pointed_set_comp
  unfolding functor_category_def
  by (simp add: P.is_category pointed_fin_set.is_category)




interpretation SH : SphereCoeffHomology "GroupToGammaset.HFunctor A" Y
  unfolding SphereCoeffHomology_def
  apply (simp add: Y.pointed_simplicial_set_axioms)
  apply (rule_tac GroupToGammaset.is_functor)
  unfolding GroupToGammaset_def
  using A.comm_group_axioms.

interpretation RH : Reduced_Homology Y A
  unfolding Reduced_Homology_def
  by (simp add: Y.pointed_simplicial_set_axioms A.comm_group_axioms)


theorem "functor pointed_fin_set.comp P.pointed_set_comp 
       (SH.Homology n)"
  unfolding pointed_fin_set.comp_def
  using SH.Homology_functor.

theorem "functor pointed_fin_set.comp P.pointed_set_comp
       (GroupToGammaset.HFunctor (RH.homology_group n))"
  apply (rule_tac GroupToGammaset.is_functor)
  unfolding GroupToGammaset_def
  using RH.is_comm_group.

theorem comparison :
   "FunCat.isomorphic
   (FunCat.mkIde (P.Inr_functor \<circ> SH.Homology n))
   (FunCat.mkIde (P.Inl_functor \<circ> GroupToGammaset.HFunctor (RH.homology_group n)))"
  oops
end
