theory SubcategoryFactorization
  imports Main
         "Category3.Subcategory"
         "Category3.NaturalTransformation"
begin




locale factorization =
  A: category A +
  B: category B +
  S: subcategory B S +
  F: "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"
  and S :: "'b \<Rightarrow> bool" +
assumes lands_in_subcat: "\<And>a. A.arr a \<Longrightarrow> S (F a)"
begin

lemma is_functor : "functor A S.comp F"
  unfolding functor_def apply auto
    apply (simp add: A.category_axioms)
   apply (simp add: subcategory.is_category S.subcategory_axioms)
  unfolding functor_axioms_def apply auto
proof-
  show "\<And>f. \<not> A.arr f \<Longrightarrow> F f = B.null"
    using F.is_extensional by blast
  show arr_f : "\<And>f. A.arr f \<Longrightarrow> S.arr (F f)"
    using S.subcategory_axioms apply (simp add: subcategory.arr_char)
    by (simp add: lands_in_subcat)
  show "\<And>f. A.arr f \<Longrightarrow> S.dom (F f) = F (A.dom f)"
    using S.subcategory_axioms apply (simp add: subcategory.dom_char)
    using lands_in_subcat by auto
  show "\<And>f. A.arr f \<Longrightarrow> S.cod (F f) = F (A.cod f)"
    using S.subcategory_axioms apply (simp add: subcategory.cod_char)
    using lands_in_subcat by auto
  show "\<And>g f. A.seq g f \<Longrightarrow> B (F g) (F f) = S.comp (F g) (F f)"
    using S.subcategory_axioms apply (simp add: subcategory.comp_char)
    using lands_in_subcat by auto
qed
    
lemma fully_faithful : "fully_faithful_functor A B F \<Longrightarrow> 
                        fully_faithful_functor A S.comp F"
  unfolding fully_faithful_functor_def
            faithful_functor_def
            full_functor_def
  apply auto
  apply (simp add: is_functor)
  unfolding full_functor_axioms_def
  apply auto
proof-
  fix a b g
  assume "\<forall>a. A.ide a \<longrightarrow>
           (\<forall>b. A.ide b \<longrightarrow>
                 (\<forall>g. \<guillemotleft>g : F b \<rightarrow>\<^sub>B F a\<guillemotright> \<longrightarrow> (\<exists>f. \<guillemotleft>f : b \<rightarrow>\<^sub>A a\<guillemotright> \<and> F f = g)))"
  then have full: "\<And>a. A.ide a \<Longrightarrow> (\<And>b. A.ide b \<Longrightarrow>
             (\<And>g. \<guillemotleft>g : F b \<rightarrow>\<^sub>B F a\<guillemotright> \<Longrightarrow>  (\<exists>f. \<guillemotleft>f : b \<rightarrow>\<^sub>A a\<guillemotright> \<and> F f = g)))"
    by auto
  assume "A.ide a" "A.ide b"
  assume g_in_Shom: "S.in_hom g (F b) (F a)"
  then have "\<guillemotleft>g : F b \<rightarrow>\<^sub>B F a\<guillemotright>"
    using subcategory.in_hom_char [OF S.subcategory_axioms] by blast
  show "(\<exists>f. \<guillemotleft>f : b \<rightarrow>\<^sub>A a\<guillemotright> \<and> F f = g)"
    apply (rule_tac full)
    using \<open>A.ide a\<close> \<open>A.ide b\<close> \<open>\<guillemotleft>g : F b \<rightarrow>\<^sub>B F a\<guillemotright>\<close> by simp_all
qed


lemma comp_factorization :
  assumes "functor D A G"
  shows "factorization D B (F \<circ> G) S"
  unfolding factorization_def
  apply safe
  using \<open>functor D A G\<close>
      apply (simp add: functor_def)
     apply (rule_tac B.category_axioms)
    apply (rule_tac S.subcategory_axioms)
   apply (rule_tac functor_comp)
    apply (rule_tac \<open>functor D A G\<close>)
   apply (rule_tac F.functor_axioms)
  unfolding factorization_axioms_def
  apply safe
proof-
  fix a
  assume "partial_magma.arr D a"
  then have "A.arr (G a)"
    using functor.preserves_arr [OF \<open>functor D A G\<close>]
    by simp
  then show "S ((F \<circ> G) a)"
    apply simp
    using lands_in_subcat.
qed



end






locale nat_trafo_factorization =
  A: category A +
  B: category B +
  S: subcategory B S +
  F: "functor" A B F +
  F_factors : factorization A B F S +
  G_factors : factorization A B G S +
  G: "functor" A B G +
  \<tau>: natural_transformation A B F G \<tau>
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'a \<Rightarrow> 'b"
  and \<tau> :: "'a \<Rightarrow> 'b" 
  and S :: "'b \<Rightarrow> bool" +
assumes lands_in_subcat: "\<And>a. A.arr a \<Longrightarrow> S (\<tau> a)"
begin


lemma is_natural_transformation : "natural_transformation A S.comp F G \<tau>"
  unfolding natural_transformation_def
  apply (simp add: A.category_axioms
                   subcategory.is_category [OF S.subcategory_axioms]
                   F_factors.is_functor
                   G_factors.is_functor)
  unfolding natural_transformation_axioms_def
  apply safe
proof-
  fix f
  show "\<not> A.arr f \<Longrightarrow> \<tau> f = S.null"
    unfolding subcategory.null_char [OF S.subcategory_axioms]
    using \<tau>.is_extensional by blast
  assume "A.arr f"
  show "S.dom (\<tau> f) = F (A.dom f)"
    unfolding subcategory.dom_char [OF S.subcategory_axioms]
    using lands_in_subcat [OF \<open>A.arr f\<close>]
    unfolding subcategory.arr_char [OF S.subcategory_axioms] apply simp
    using \<open>A.arr f\<close> by blast
  show "S.cod (\<tau> f) = G (A.cod f)"
    unfolding subcategory.cod_char [OF S.subcategory_axioms]
    using lands_in_subcat [OF \<open>A.arr f\<close>]
    unfolding subcategory.arr_char [OF S.subcategory_axioms] apply simp
    using \<open>A.arr f\<close> by blast
  have "S.arr (\<tau> (A.dom f)) \<and> S.arr (G f) \<and> B.seq (G f) (\<tau> (A.dom f))"
    unfolding subcategory.arr_char [OF S.subcategory_axioms]
    apply safe
      apply (rule_tac lands_in_subcat [OF A.arr_dom [OF \<open>A.arr f\<close>]])
     apply (rule_tac G_factors.lands_in_subcat [OF \<open>A.arr f\<close>])
    by (simp add: \<open>A.arr f\<close>)
  then show "S.comp (G f) (\<tau> (A.dom f)) = \<tau> f" 
    apply (subst subcategory.comp_char [OF S.subcategory_axioms])
    apply simp
    by blast
  have "S.arr (F f) \<and> S.arr (\<tau> (A.cod f)) \<and> B.seq (\<tau> (A.cod f)) (F f)"
    unfolding subcategory.arr_char [OF S.subcategory_axioms]
    apply safe
      apply (rule_tac F_factors.lands_in_subcat [OF \<open>A.arr f\<close>])
     apply (rule_tac lands_in_subcat [OF A.arr_cod [OF \<open>A.arr f\<close>]])
    by (simp add: \<open>A.arr f\<close>)
  then show "S.comp (\<tau> (A.cod f)) (F f) = \<tau> f"
    apply (subst subcategory.comp_char [OF S.subcategory_axioms])
    apply simp
    by blast
qed
  
end

end
