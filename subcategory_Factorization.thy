theory subcategory_Factorization
  imports Main
         "~~/myLibs/Category3/Category3/Subcategory"
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
    
    

  
end

end
