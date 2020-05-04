theory SomeCategoryTheory
  imports Main
         "Category3.Subcategory"
         "Category3.NaturalTransformation"
         "Category3.ProductCategory"
         "Category3.AbstractedCategory"
begin


lemma (in category) in_hom_dom : "\<guillemotleft> f : a \<rightarrow> b \<guillemotright> \<Longrightarrow> dom f = a"
  by blast
lemma (in category) in_hom_cod : "\<guillemotleft> f : a \<rightarrow> b \<guillemotright> \<Longrightarrow> cod f = b"
  by blast


lemma transport : "x \<in> A \<Longrightarrow> A = B \<Longrightarrow> x \<in> B"
  by simp


lemma (in natural_transformation) preserves_arr :
  assumes "A.arr f"
  shows "B.arr (\<tau> f)"
  using \<open>A.arr f\<close>
  unfolding preserves_reflects_arr.


lemma reverse_equality : "a = b \<Longrightarrow> b = a"
  by simp


fun MkFunctor :: "'a comp \<Rightarrow> 'b comp \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "MkFunctor C D f a = 
                 (if partial_magma.arr C a 
                 then f a
                 else partial_magma.null D)"


lemma (in category) seq_ide_arr : "ide a \<Longrightarrow> arr f \<Longrightarrow> cod f = a \<Longrightarrow> seq a f"
  apply (rule_tac seqI')
  by auto



locale binary_product =
  C : category C
  for C :: "'c comp"
  and factor1 factor2 :: "'c"
  and prod :: "'c"
  and proj1 proj2 :: "'c"
  and UP_map :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" +
assumes factor1_obj : "C.ide factor1"
  and factor2_obj : "C.ide factor2"
  and prod_obj : "C.ide prod"
  and proj1_in_hom : "C.in_hom proj1 prod factor1"
  and proj2_in_hom : "C.in_hom proj2 prod factor2"
  and UP_existence : "\<And>f g. C.arr f \<Longrightarrow> C.arr g \<Longrightarrow> C.dom f = C.dom g \<Longrightarrow>
                      C.cod f = factor1 \<Longrightarrow> C.cod g = factor2 \<Longrightarrow>
             C.in_hom (UP_map f g) (C.dom f) prod \<and>
                (C proj1 (UP_map f g) = f \<and>
                C proj2 (UP_map f g) = g)"
  and   UP_uniqueness: "\<And>f g. C.arr f \<Longrightarrow> C.arr g \<Longrightarrow> C.dom f = C.dom g \<Longrightarrow>
                      C.cod f = factor1 \<Longrightarrow> C.cod g = factor2 \<Longrightarrow> 
                       (\<And>h. C.in_hom h (C.dom f) prod \<and>
                             (C proj1 h = f \<and>
                              C proj2 h = g) 
                         \<Longrightarrow> h = UP_map f g)"
begin
end


locale category_with_products =
  C : category C
  for C :: "'c comp"
  and prod :: "'c \<Rightarrow> 'c \<Rightarrow> 'c"
  and proj1 :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" 
  and proj2 :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" 
  and UP_map :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" +
assumes product_existence : "\<And> a b. C.ide a \<Longrightarrow> C.ide b \<Longrightarrow>
        binary_product C a b (prod a b) (proj1 a b) (proj2 a b) UP_map"
begin

lemma prod_obj: "\<And>a b. C.ide a \<Longrightarrow> C.ide b \<Longrightarrow> C.ide (prod a b)"
  using binary_product.prod_obj [OF product_existence].

lemma proj1_in_hom : "\<And>a b. C.ide a \<Longrightarrow> C.ide b \<Longrightarrow> C.in_hom (proj1 a b) (prod a b) a"
  using binary_product.proj1_in_hom [OF product_existence].

lemma proj2_in_hom : "\<And>a b. C.ide a \<Longrightarrow> C.ide b \<Longrightarrow> C.in_hom (proj2 a b) (prod a b) b"
  using binary_product.proj2_in_hom [OF product_existence].

lemma UP_existence : "\<And>f g. C.arr f \<Longrightarrow> C.arr g \<Longrightarrow> C.dom f = C.dom g \<Longrightarrow>
                      C.in_hom (UP_map f g) (C.dom f) (prod (C.cod f) (C.cod g)) \<and>
                      (C (proj1 (C.cod f) (C.cod g)) (UP_map f g) = f \<and>
                       C (proj2 (C.cod f) (C.cod g)) (UP_map f g) = g)" 
  using binary_product.UP_existence [OF product_existence 
        [OF C.ide_cod C.ide_cod]]
  by simp

lemma UP_uniqueness: "\<And>f g. C.arr f \<Longrightarrow> C.arr g \<Longrightarrow> C.dom f = C.dom g \<Longrightarrow> 
               (\<And>h. C.in_hom h (C.dom f) (prod (C.cod f) (C.cod g)) \<and>
                (C (proj1 (C.cod f) (C.cod g)) h = f \<and>
                 C (proj2 (C.cod f) (C.cod g)) h = g) 
                 \<Longrightarrow> h = UP_map f g)"
  using binary_product.UP_uniqueness [OF product_existence 
        [OF C.ide_cod C.ide_cod]]
  by simp



definition prod_functor :: "'c \<times> 'c \<Rightarrow> 'c" where
  "prod_functor = MkFunctor (product_category.comp C C) C 
                  (\<lambda> (f, g). UP_map 
                  (C f (proj1 (C.dom f) (C.dom g))) 
                  (C g (proj2 (C.dom f) (C.dom g))))"


interpretation CxC : product_category C C
  unfolding product_category_def
  by (simp_all add: C.category_axioms)


lemma prod_functor : "functor (product_category.comp C C) C prod_functor"
  unfolding functor_def
  apply (simp add: C.category_axioms CxC.category_axioms)
  unfolding functor_axioms_def
  apply (subst prod_functor_def)
  apply simp
  apply safe
proof-
  fix a b
  assume arr_a :"C.arr a"
  assume arr_b :"C.arr b"

  have proj1_prop : "\<guillemotleft>proj1 (C.dom a) (C.dom b) : prod (C.dom a) (C.dom b) \<rightarrow> C.dom a\<guillemotright>"
    using proj1_in_hom [OF C.ide_dom [OF arr_a]
                           C.ide_dom [OF arr_b]].
  have proj2_prop : "\<guillemotleft>proj2 (C.dom a) (C.dom b) : prod (C.dom a) (C.dom b) \<rightarrow> C.dom b\<guillemotright>"
    using proj2_in_hom [OF C.ide_dom [OF arr_a]
                           C.ide_dom [OF arr_b]].

  define a1 where "a1 = (C a (proj1 (C.dom a) (C.dom b)))"
  have arr_a1 : "C.arr a1"
    unfolding a1_def
    apply (rule_tac C.seqI')
    using proj1_prop apply simp
    using C.in_homI [OF arr_a] by blast

  define b2 where "b2 = (C b (proj2 (C.dom a) (C.dom b)))"
  have arr_b2 : "C.arr b2"
    unfolding b2_def
    apply (rule_tac C.seqI')
    using proj2_prop apply simp
    using C.in_homI [OF arr_b] by blast

  have proj_dom_eq : "C.dom (proj1 (C.dom a) (C.dom b)) = C.dom (proj2 (C.dom a) (C.dom b))"
    apply (rule_tac C.in_homE [OF proj1_prop])
    apply (rule_tac C.in_homE [OF proj2_prop])
    by simp

  have UP_prop : "C.in_hom (UP_map a1 b2) (C.dom a1) (prod (C.cod a1) (C.cod b2)) \<and>
                             (C (proj1 (C.cod a1) (C.cod b2)) (UP_map a1 b2) = a1 \<and>
                              C (proj2 (C.cod a1) (C.cod b2)) (UP_map a1 b2) = b2)"
    apply (rule_tac UP_existence)
      apply (simp_all add: arr_a1 arr_b2)
    unfolding a1_def b2_def
    apply (subst C.dom_comp)
    using arr_a1
    unfolding a1_def apply simp
    apply (subst C.dom_comp)
    using arr_b2
    unfolding b2_def apply simp
    by (simp add: proj_dom_eq)

  then have UP_in_hom : "C.in_hom (UP_map a1 b2) (C.dom a1) (prod (C.cod a1) (C.cod b2))" 
    by simp

  show "C.arr (prod_functor (a, b))"
    unfolding prod_functor_def
    apply (simp add: arr_a arr_b)
    unfolding reverse_equality [OF a1_def]
    unfolding reverse_equality [OF b2_def]
    apply (rule_tac C.in_homE [OF UP_in_hom])
    by simp


  have dom_seq1 : "C.seq (C.dom a) (proj1 (C.dom a) (C.dom b))"
      apply (rule_tac C.seqI')
    using proj1_prop apply simp
    using C.in_homI [OF C.ideD(1) [OF C.ide_dom [OF arr_a]]]
    unfolding C.dom_dom [OF arr_a] by blast
  have dom_seq2 : "C.seq (C.dom b) (proj2 (C.dom a) (C.dom b))"
     apply (rule_tac C.seqI')
    using proj2_prop apply simp
    using C.in_homI [OF C.ideD(1) [OF C.ide_dom [OF arr_b]]]
    unfolding C.dom_dom [OF arr_b] by blast


  show "C.dom (prod_functor (a, b)) = prod_functor (C.dom a, C.dom b)"
    unfolding prod_functor_def
    apply (simp add: arr_a arr_b)
    unfolding reverse_equality [OF a1_def]
    unfolding reverse_equality [OF b2_def]
    apply (rule_tac UP_uniqueness)
       apply (simp add: dom_seq1)
      apply (simp add: dom_seq2)
    unfolding C.dom_comp [OF dom_seq1]
    unfolding C.dom_comp [OF dom_seq2]
     apply (simp add: proj_dom_eq)
    unfolding C.cod_comp [OF dom_seq1]
    unfolding C.cod_comp [OF dom_seq2]
    unfolding C.cod_dom [OF arr_a]
    unfolding C.cod_dom [OF arr_b]
    apply safe
  proof-
    have eq1: "C.dom (UP_map a1 b2) = C.dom (proj1 (C.dom a) (C.dom b))"
       apply (rule_tac C.in_homE [OF UP_in_hom])
       apply simp
       apply (subst a1_def)
       apply (subst C.dom_comp)
      using arr_a1 a1_def apply simp
      by simp

    have eq2: "C.dom (proj1 (C.dom a) (C.dom b)) = prod (C.dom a) (C.dom b)"
      apply (rule_tac C.in_homE [OF proj1_prop])
      by simp
    show dom_in_hom: "\<guillemotleft>C.dom (UP_map a1 b2) : C.dom (proj1 (C.dom a) (C.dom b)) \<rightarrow> prod (C.dom a) (C.dom b)\<guillemotright>"
      unfolding eq1
      unfolding eq2
      using C.ide_dom arr_a arr_b prod_obj by auto
    show "C (proj1 (C.dom a) (C.dom b)) (C.dom (UP_map a1 b2)) = C (C.dom a) (proj1 (C.dom a) (C.dom b))"
      apply (subst C.comp_ide_arr [OF C.ide_dom [OF arr_a] dom_seq1])
      apply (subst C.comp_arr_ide [OF C.ide_dom])
        apply (rule_tac C.in_homE [OF UP_in_hom])
        apply simp
       apply (rule_tac C.seqI')
      using dom_in_hom apply simp
      using proj1_prop apply simp
      by simp
    show "C (proj2 (C.dom a) (C.dom b)) (C.dom (UP_map a1 b2)) = C (C.dom b) (proj2 (C.dom a) (C.dom b))"
      apply (subst C.comp_ide_arr [OF C.ide_dom [OF arr_b] dom_seq2])
      apply (subst C.comp_arr_ide [OF C.ide_dom])
        apply (rule_tac C.in_homE [OF UP_in_hom])
        apply simp
       apply (rule_tac C.seqI')
      using dom_in_hom apply simp
      using proj2_prop apply simp
      by simp
  qed

  have proj1_prop2: "\<guillemotleft>proj1 (C.cod a) (C.cod b) : prod (C.cod a) (C.cod b) \<rightarrow> C.cod a\<guillemotright>"
    using proj1_in_hom [OF C.ide_cod [OF arr_a]
                           C.ide_cod [OF arr_b]].
  have proj2_prop2: "\<guillemotleft>proj2 (C.cod a) (C.cod b) : prod (C.cod a) (C.cod b) \<rightarrow> C.cod b\<guillemotright>"
    using proj2_in_hom [OF C.ide_cod [OF arr_a]
                           C.ide_cod [OF arr_b]].

  have proj_dom_eq2: "C.dom (proj1 (C.cod a) (C.cod b)) = C.dom (proj2 (C.cod a) (C.cod b))"
    apply (rule_tac C.in_homE [OF proj1_prop2])
    apply (rule_tac C.in_homE [OF proj2_prop2])
    by simp


  have cod_seq1: "C.seq (C.cod a) (proj1 (C.cod a) (C.cod b))"
    apply (rule_tac C.seqI')
    using proj1_prop2 apply simp
    apply (subst reverse_equality [OF C.ide_in_hom])
    using C.ide_cod [OF arr_a] by simp
  have cod_seq2 : "C.seq (C.cod b) (proj2 (C.cod a) (C.cod b))"
    apply (rule_tac C.seqI')
    using proj2_prop2 apply simp
    apply (subst reverse_equality [OF C.ide_in_hom])
    using C.ide_cod [OF arr_b] by simp


  show "C.cod (prod_functor (a, b)) = prod_functor (C.cod a, C.cod b)"
    unfolding prod_functor_def
    apply (simp add: arr_a arr_b)
    unfolding reverse_equality [OF a1_def]
    unfolding reverse_equality [OF b2_def]
    apply (rule_tac UP_uniqueness)
       apply (simp add: cod_seq1)
      apply (simp add: cod_seq2)
    unfolding C.dom_comp [OF cod_seq1]
    unfolding C.dom_comp [OF cod_seq2]
     apply (simp add: proj_dom_eq2)
    unfolding C.cod_comp [OF cod_seq1]
    unfolding C.cod_comp [OF cod_seq2]
    unfolding C.cod_cod [OF arr_a]
    unfolding C.cod_cod [OF arr_b]
    apply safe
  proof-
    have eq1: "C.cod (UP_map a1 b2) = prod (C.cod a) (C.cod b)"
       apply (rule_tac C.in_homE [OF UP_in_hom])
       apply simp
       apply (subst a1_def)
      apply (subst C.cod_comp)
       apply (rule_tac C.seqI')
      using proj1_prop apply simp
      using C.in_homI [OF arr_a] apply blast
      apply (subst b2_def)
      apply (subst C.cod_comp)
       apply (rule_tac C.seqI')
      using proj2_prop apply simp
      using C.in_homI [OF arr_b] apply blast
      by simp


    have eq2: "C.dom (proj1 (C.cod a) (C.cod b)) = prod (C.cod a) (C.cod b)"
      apply (rule_tac C.in_homE [OF proj1_prop2])
      by simp
    show cod_in_hom: "\<guillemotleft>C.cod (UP_map a1 b2) : C.dom (proj1 (C.cod a) (C.cod b)) \<rightarrow> prod (C.cod a) (C.cod b)\<guillemotright>"
      unfolding eq1
      unfolding eq2
      using C.ide_dom arr_a arr_b prod_obj by auto
    show "C (proj1 (C.cod a) (C.cod b)) (C.cod (UP_map a1 b2)) = C (C.cod a) (proj1 (C.cod a) (C.cod b))"
      apply (subst C.comp_ide_arr [OF C.ide_cod [OF arr_a] cod_seq1])
      apply (subst C.comp_arr_ide [OF C.ide_cod])
        apply (rule_tac C.in_homE [OF UP_in_hom])
        apply simp
       apply (rule_tac C.seqI')
      using cod_in_hom apply simp
      using proj1_prop2 apply simp
      by simp
    show "C (proj2 (C.cod a) (C.cod b)) (C.cod (UP_map a1 b2)) = C (C.cod b) (proj2 (C.cod a) (C.cod b))"
      apply (subst C.comp_ide_arr [OF C.ide_cod [OF arr_b] cod_seq2])
      apply (subst C.comp_arr_ide [OF C.ide_cod])
        apply (rule_tac C.in_homE [OF UP_in_hom])
        apply simp
       apply (rule_tac C.seqI')
      using cod_in_hom apply simp
      using proj2_prop2 apply simp
      by simp
  qed
next
  fix a b c d
  assume arr_comp1: "C.arr (fst (CxC.comp (a, b) (c, d)))"
  have "\<not> (C.arr c \<and> C.arr d \<and> C.arr a \<and> C.arr b \<and> C.cod c = C.dom a \<and> C.cod d = C.dom b) \<Longrightarrow> False"
  proof-
    assume "\<not> (C.arr c \<and> C.arr d \<and> C.arr a \<and> C.arr b \<and> C.cod c = C.dom a \<and> C.cod d = C.dom b)"
    then have null_eq: "fst (CxC.comp (a, b) (c, d)) = C.null"
      unfolding CxC.comp_def by auto
    show "False"
      using arr_comp1
      unfolding null_eq
      using C.not_arr_null 
      by simp
  qed
  then have arr_abcd: "C.arr c \<and> C.arr d \<and> C.arr a \<and> C.arr b \<and> C.cod c = C.dom a \<and> C.cod d = C.dom b"
    by auto

  from arr_abcd have "C.arr a" by blast
  from arr_abcd have "C.arr b" by blast
  from arr_abcd have "C.arr c" by blast
  from arr_abcd have "C.arr d" by blast
  from arr_abcd have "C.cod c = C.dom a" by blast
  from arr_abcd have "C.cod d = C.dom b" by blast

  have proj1_in_hom_cd : "\<guillemotleft>proj1 (C.dom c) (C.dom d) : prod (C.dom c) (C.dom d) \<rightarrow> (C.dom c)\<guillemotright>"
    apply (rule_tac proj1_in_hom [OF C.ide_dom C.ide_dom])
    by (simp_all add: arr_abcd)

  have seq_ac : "C.seq a c"
    apply (rule_tac C.seqI)
    using arr_abcd by simp_all
  have ac_in_hom : "\<guillemotleft>C a c : C.dom c \<rightarrow> C.cod a\<guillemotright>"
    apply (rule_tac C.comp_in_homI)
    using C.in_homI arr_abcd apply blast
    using C.in_homI arr_abcd by blast

  have proj2_in_hom_cd : "\<guillemotleft>proj2 (C.dom c) (C.dom d) : prod (C.dom c) (C.dom d) \<rightarrow> (C.dom d)\<guillemotright>"
    apply (rule_tac proj2_in_hom [OF C.ide_dom C.ide_dom])
    by (simp_all add: arr_abcd)

  have bd_in_hom : "\<guillemotleft>C b d : C.dom d \<rightarrow> C.cod b\<guillemotright>"
    apply (rule_tac C.comp_in_homI)
    using C.in_homI arr_abcd apply blast
    using C.in_homI arr_abcd by blast
  have seq_bd : "C.seq b d"
    apply (rule_tac C.seqI)
    using arr_abcd by simp_all

  assume arr_comp2: "C.arr (snd (CxC.comp (a, b) (c, d)))"

  define a1 where "a1 = C a (proj1 (C.dom a) (C.dom b))"
  define b2 where "b2 = C b (proj2 (C.dom a) (C.dom b))"
  define c1 where "c1 = C c (proj1 (C.dom c) (C.dom d))"
  define d2 where "d2 = C d (proj2 (C.dom c) (C.dom d))"

  have a1_in_hom : "\<guillemotleft> a1 : C.dom (proj1 (C.dom a) (C.dom b)) \<rightarrow> C.cod a \<guillemotright>"
    unfolding a1_def
    apply (rule_tac C.comp_in_homI)
     apply (rule_tac C.in_homE [OF proj1_in_hom 
                    [OF C.ide_dom [OF \<open>C.arr a\<close>] 
                        C.ide_dom [OF \<open>C.arr b\<close>]]])
     apply blast
    using C.in_homI [OF \<open>C.arr a\<close>] by simp 
  have b2_in_hom : "\<guillemotleft> b2 : C.dom (proj2 (C.dom a) (C.dom b)) \<rightarrow> C.cod b \<guillemotright>"
    unfolding b2_def
    apply (rule_tac C.comp_in_homI)
     apply (rule_tac C.in_homE [OF proj2_in_hom 
                    [OF C.ide_dom [OF \<open>C.arr a\<close>] 
                        C.ide_dom [OF \<open>C.arr b\<close>]]])
     apply blast
    using C.in_homI [OF \<open>C.arr b\<close>] by simp
    have c1_in_hom : "\<guillemotleft> c1 : C.dom (proj1 (C.dom c) (C.dom d)) \<rightarrow> C.cod c \<guillemotright>"
    unfolding c1_def
    apply (rule_tac C.comp_in_homI)
     apply (rule_tac C.in_homE [OF proj1_in_hom 
                    [OF C.ide_dom [OF \<open>C.arr c\<close>] 
                        C.ide_dom [OF \<open>C.arr d\<close>]]])
     apply blast
    using C.in_homI [OF \<open>C.arr c\<close>] by simp
  have d2_in_hom : "\<guillemotleft> d2 : C.dom (proj2 (C.dom c) (C.dom d)) \<rightarrow> C.cod d \<guillemotright>"
    unfolding d2_def
    apply (rule_tac C.comp_in_homI)
     apply (rule_tac C.in_homE [OF proj2_in_hom 
                    [OF C.ide_dom [OF \<open>C.arr c\<close>] 
                        C.ide_dom [OF \<open>C.arr d\<close>]]])
     apply blast
    using C.in_homI [OF \<open>C.arr d\<close>] by simp

  show "prod_functor (CxC.comp (a, b) (c, d)) = C (prod_functor (a, b)) (prod_functor (c, d))"
    unfolding prod_functor_def
    apply (simp add: arr_comp1 arr_comp2 arr_abcd)
    apply (rule_tac reverse_equality)
    apply (rule_tac UP_uniqueness)
       apply (rule_tac C.seqI' [OF proj1_in_hom_cd ac_in_hom])
      apply (rule_tac C.seqI' [OF proj2_in_hom_cd bd_in_hom])
    unfolding C.dom_comp [OF C.seqI' [OF proj1_in_hom_cd ac_in_hom]]
    unfolding C.dom_comp [OF C.seqI' [OF proj2_in_hom_cd bd_in_hom]]
    apply (rule_tac C.in_homE [OF proj1_in_hom_cd])
     apply (rule_tac C.in_homE [OF proj2_in_hom_cd])
     apply simp
    unfolding C.cod_comp [OF C.seqI' [OF proj1_in_hom_cd ac_in_hom]]
    unfolding C.cod_comp [OF C.seqI' [OF proj2_in_hom_cd bd_in_hom]]
    unfolding C.cod_comp [OF seq_ac]
    unfolding C.cod_comp [OF seq_bd]
    unfolding reverse_equality [OF a1_def]
    unfolding reverse_equality [OF b2_def]
    unfolding reverse_equality [OF c1_def]
    unfolding reverse_equality [OF d2_def]
    apply safe
      apply (rule_tac C.comp_in_homI)
  proof-
    have ab_dom_eq : "C.dom (proj1 (C.dom a) (C.dom b)) = C.dom (proj2 (C.dom a) (C.dom b))"
      apply (rule_tac C.in_homE [OF  proj1_in_hom 
                    [OF C.ide_dom [OF \<open>C.arr a\<close>] 
                        C.ide_dom [OF \<open>C.arr b\<close>]]])
      apply (rule_tac C.in_homE [OF  proj2_in_hom 
                    [OF C.ide_dom [OF \<open>C.arr a\<close>] 
                        C.ide_dom [OF \<open>C.arr b\<close>]]])
      by simp
    have ab_UP : "\<guillemotleft>UP_map a1 b2 : C.dom a1 \<rightarrow> prod (C.cod a1) (C.cod b2)\<guillemotright> \<and>
                   C (proj1 (C.cod a1) (C.cod b2)) (UP_map a1 b2) = a1 \<and>
                   C (proj2 (C.cod a1) (C.cod b2)) (UP_map a1 b2) = b2"
      apply (rule_tac UP_existence)
      using a1_in_hom apply blast
      using b2_in_hom apply blast
      apply (rule_tac C.in_homE [OF a1_in_hom])
      apply (rule_tac C.in_homE [OF b2_in_hom])
      by (simp add: ab_dom_eq)


    have cd_dom_eq : "C.dom (proj1 (C.dom c) (C.dom d)) = C.dom (proj2 (C.dom c) (C.dom d))"
      apply (rule_tac C.in_homE [OF  proj1_in_hom 
                    [OF C.ide_dom [OF \<open>C.arr c\<close>] 
                        C.ide_dom [OF \<open>C.arr d\<close>]]])
      apply (rule_tac C.in_homE [OF  proj2_in_hom 
                    [OF C.ide_dom [OF \<open>C.arr c\<close>] 
                        C.ide_dom [OF \<open>C.arr d\<close>]]])
      by simp
    have cd_UP : "\<guillemotleft>UP_map c1 d2 : C.dom c1 \<rightarrow> prod (C.cod c1) (C.cod d2)\<guillemotright> \<and>
                   C (proj1 (C.cod c1) (C.cod d2)) (UP_map c1 d2) = c1 \<and>
                   C (proj2 (C.cod c1) (C.cod d2)) (UP_map c1 d2) = d2"
      apply (rule_tac UP_existence)
      using c1_in_hom apply blast
      using d2_in_hom apply blast
      apply (rule_tac C.in_homE [OF c1_in_hom])
      apply (rule_tac C.in_homE [OF d2_in_hom])
      by (simp add: cd_dom_eq)
    show "\<guillemotleft>UP_map c1 d2 : C.dom (proj1 (C.dom c) (C.dom d)) \<rightarrow> prod (C.cod c) (C.cod d)\<guillemotright>"
      using conjunct1 [OF cd_UP] 
      unfolding C.in_hom_dom [OF c1_in_hom] 
                C.in_hom_cod [OF c1_in_hom]
                C.in_hom_cod [OF d2_in_hom].
    show "\<guillemotleft>UP_map a1 b2 : prod (C.cod c) (C.cod d) \<rightarrow> prod (C.cod a) (C.cod b)\<guillemotright>"
      using conjunct1 [OF ab_UP]
      unfolding C.in_hom_dom [OF a1_in_hom] 
                C.in_hom_cod [OF a1_in_hom]
                C.in_hom_cod [OF b2_in_hom]
                C.in_hom_dom [OF proj1_in_hom 
                    [OF C.ide_dom [OF \<open>C.arr a\<close>] 
                        C.ide_dom [OF \<open>C.arr b\<close>]]]
      using arr_abcd by simp
    show "C (proj1 (C.cod a) (C.cod b)) (C (UP_map a1 b2) (UP_map c1 d2)) = 
          C (C a c) (proj1 (C.dom c) (C.dom d))"
      apply (subst reverse_equality [OF C.comp_assoc])
      using conjunct2 [OF ab_UP]
      unfolding C.in_hom_cod [OF a1_in_hom]
                C.in_hom_cod [OF b2_in_hom]
      apply simp
      apply (subst a1_def)
      apply (subst C.comp_assoc)
      using conjunct2 [OF cd_UP]
      unfolding C.in_hom_cod [OF c1_in_hom]
                C.in_hom_cod [OF d2_in_hom]
      unfolding \<open>C.cod c = C.dom a\<close>
                \<open>C.cod d = C.dom b\<close>
      apply simp
      apply (subst c1_def)
      apply (subst C.comp_assoc)
      by simp
    show "C (proj2 (C.cod a) (C.cod b)) (C (UP_map a1 b2) (UP_map c1 d2)) = 
          C (C b d) (proj2 (C.dom c) (C.dom d))"
      apply (subst reverse_equality [OF C.comp_assoc])
      using conjunct2 [OF ab_UP]
      unfolding C.in_hom_cod [OF a1_in_hom]
                C.in_hom_cod [OF b2_in_hom]
      apply simp
      apply (subst b2_def)
      apply (subst C.comp_assoc)
      using conjunct2 [OF cd_UP]
      unfolding C.in_hom_cod [OF c1_in_hom]
                C.in_hom_cod [OF d2_in_hom]
      unfolding \<open>C.cod c = C.dom a\<close>
                \<open>C.cod d = C.dom b\<close>
      apply simp
      apply (subst d2_def)
      apply (subst C.comp_assoc)
      by simp
  qed
qed


lemma prod_functor_obj : "\<And>a b. C.ide a \<Longrightarrow> C.ide b \<Longrightarrow> prod_functor (a, b) = prod a b"
  unfolding prod_functor_def
  apply simp
  apply (rule_tac reverse_equality [OF UP_uniqueness])
proof-
  fix a b
  show seq1: "C.ide a \<Longrightarrow> C.ide b \<Longrightarrow> C.seq a (proj1 a b)"
    apply (rule_tac C.seqI')
    using proj1_in_hom apply blast
    using C.ide_in_hom by simp
  show seq2: "C.ide a \<Longrightarrow> C.ide b \<Longrightarrow> C.seq b (proj2 a b)"
    apply (rule_tac C.seqI')
    using proj2_in_hom apply blast
    using C.ide_in_hom by simp
  show "C.ide a \<Longrightarrow> C.ide b \<Longrightarrow> C.dom (C a (proj1 a b)) = C.dom (C b (proj2 a b))"
    unfolding C.dom_comp [OF seq1]
    unfolding C.dom_comp [OF seq2]
    unfolding C.in_hom_dom [OF proj1_in_hom]
    unfolding C.in_hom_dom [OF proj2_in_hom]
    by simp
  show "C.ide a \<Longrightarrow>
           C.ide b \<Longrightarrow>
           \<guillemotleft>prod a b : C.dom (C a (proj1 a b)) \<rightarrow> prod (C.cod (C a (proj1 a b))) (C.cod (C b (proj2 a b)))\<guillemotright> \<and>
           C (proj1 (C.cod (C a (proj1 a b))) (C.cod (C b (proj2 a b)))) (prod a b) = C a (proj1 a b) \<and>
           C (proj2 (C.cod (C a (proj1 a b))) (C.cod (C b (proj2 a b)))) (prod a b) = C b (proj2 a b)"
    apply auto
    unfolding C.dom_comp [OF seq1]
    unfolding C.cod_comp [OF seq1]
    unfolding C.cod_comp [OF seq2]
    unfolding C.in_hom_dom [OF proj1_in_hom]
    unfolding C.ideD(3)
    using prod_obj
    using C.ide_in_hom
      apply simp
     apply (subst C.comp_arr_ide)
       apply (simp add: prod_obj)
      apply (rule_tac C.seqI')
    using prod_obj C.ide_in_hom apply blast
    using proj1_in_hom apply blast
     apply (subst C.comp_ide_arr)
    apply simp
      apply (rule_tac C.seqI')
    using proj1_in_hom apply blast
    using C.ide_in_hom apply blast
     apply simp
    apply (subst C.comp_arr_ide)
      apply (simp add: prod_obj)
     apply (rule_tac C.seqI')
    using prod_obj C.ide_in_hom apply blast
    using proj2_in_hom apply blast
    apply (subst C.comp_ide_arr)
      apply simp
     apply (rule_tac C.seqI')
    using proj2_in_hom apply blast
    using C.ide_in_hom apply blast
    by simp
qed

end


locale classical_functor =
  CC1 : classical_category Obj1 Arr1 Dom1 Cod1 Ide1 Comp1 +
  CC2 : classical_category Obj2 Arr2 Dom2 Cod2 Ide2 Comp2
  for Obj1 :: "'a \<Rightarrow> bool"
    and Arr1 :: "'b \<Rightarrow> bool"
    and Dom1 :: "'b \<Rightarrow> 'a"
    and Cod1 :: "'b \<Rightarrow> 'a"
    and Ide1 :: "'a \<Rightarrow> 'b"
    and Comp1 :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
    and Obj2 :: "'c \<Rightarrow> bool"
    and Arr2 :: "'d \<Rightarrow> bool"
    and Dom2 :: "'d \<Rightarrow> 'c"
    and Cod2 :: "'d \<Rightarrow> 'c"
    and Ide2 :: "'c \<Rightarrow> 'd"
    and Comp2 :: "'d \<Rightarrow> 'd \<Rightarrow> 'd"
  and FOb :: "'a \<Rightarrow> 'c"
  and FArr :: "'b \<Rightarrow> 'd" +
assumes F_preserves_Obj : "\<And>a. Obj1 a \<Longrightarrow> Obj2 (FOb a)"
  and   F_preserves_Arr : "\<And>b. Arr1 b \<Longrightarrow> Arr2 (FArr b)"
  and   F_preserves_Dom : "\<And>b. Arr1 b \<Longrightarrow> Dom2 (FArr b) = FOb (Dom1 b)"
  and   F_preserves_Cod : "\<And>b. Arr1 b \<Longrightarrow> Cod2 (FArr b) = FOb (Cod1 b)"
  and   F_preserves_Id  : "\<And>a. Obj1 a \<Longrightarrow> FArr (Ide1 a) = Ide2 (FOb a)"
  and   F_preserves_Comp: "\<And>g f. Arr1 g \<Longrightarrow> Arr1 f \<Longrightarrow> Dom1 g = Cod1 f \<Longrightarrow>
                           FArr (Comp1 g f) = Comp2 (FArr g) (FArr f)"
begin

definition map :: "'b option \<Rightarrow> 'd option" where
  "map b = (if CC1.arr b then Some (FArr (the b)) else CC2.null)"

lemma is_functor : "functor CC1.comp CC2.comp map"
  unfolding functor_def
  apply (simp add: CC1.induces_category CC2.induces_category)
  unfolding functor_axioms_def
  apply safe
proof-
  show "\<And>f. \<not> CC1.arr f \<Longrightarrow> local.map f = CC2.null"
    unfolding map_def by simp
  show map_arr: "\<And>f. CC1.arr f \<Longrightarrow> CC2.arr (local.map f)"
    unfolding map_def apply simp
    unfolding CC1.arr_char CC2.arr_char
    using F_preserves_Arr by simp
  show map_dom: "\<And>f. CC1.arr f \<Longrightarrow> CC2.dom (local.map f) = local.map (CC1.dom f)"
    unfolding map_def apply simp
    unfolding CC1.dom_char CC2.dom_char apply auto
    using map_arr unfolding map_def apply auto
    unfolding CC1.arr_char
    apply (subst F_preserves_Dom)
     apply simp
    apply (subst F_preserves_Id)
    using CC1.Obj_Dom by simp_all
  show map_cod: "\<And>f. CC1.arr f \<Longrightarrow> CC2.cod (local.map f) = local.map (CC1.cod f)"
    unfolding map_def apply simp
    unfolding CC1.cod_char CC2.cod_char apply auto
    using map_arr unfolding map_def apply auto
    unfolding CC1.arr_char
    apply (subst F_preserves_Cod)
     apply simp
    apply (subst F_preserves_Id)
    using CC1.Obj_Cod by simp_all
  fix g f
  assume "CC1.seq g f"
  have H: "Ide1 (Dom1 (the g)) = Ide1 (Cod1 (the f)) \<Longrightarrow>
        Cod1 (the f) = Dom1 (the g)"
    using CC1.arr_char CC1.comp_def \<open>CC1.seq g f\<close> by fastforce

  show "local.map (CC1.comp g f) = CC2.comp (local.map g) (local.map f)"
    apply (rule_tac CC1.seqE [OF \<open>CC1.seq g f\<close>])
    unfolding map_def apply simp
    unfolding CC1.dom_char CC1.cod_char apply simp
    unfolding CC1.arr_char CC2.arr_char
    using H
    unfolding CC1.comp_char apply simp
    apply (subst F_preserves_Comp)
       apply simp_all
    unfolding CC2.comp_char apply simp
    using F_preserves_Arr F_preserves_Dom F_preserves_Cod 
    by simp
qed
end


locale classical_full_subcategory =
  CC : classical_category Obj Arr Dom Cod Ide Comp
    for Obj :: "'a \<Rightarrow> bool"
    and Arr :: "'b \<Rightarrow> bool"
    and Dom :: "'b \<Rightarrow> 'a"
    and Cod :: "'b \<Rightarrow> 'a"
    and Ide :: "'a \<Rightarrow> 'b"
    and Comp :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
    and SObj :: "'a \<Rightarrow> bool" +
  assumes SObj_Obj : "\<And>x. SObj x \<Longrightarrow> Obj x"
begin

definition SArr where
  "SArr x = (Arr x \<and> SObj (Dom x) \<and> SObj (Cod x))"

interpretation SCC : classical_category SObj SArr Dom Cod Ide Comp
  unfolding classical_category_def
  unfolding SArr_def
  using SObj_Obj by simp

lemma is_classical_category : "classical_category SObj SArr Dom Cod Ide Comp"
  using SCC.classical_category_axioms.

interpretation Inclusion: classical_functor 
       SObj SArr Dom Cod Ide Comp
       Obj Arr Dom Cod Ide Comp 
       "(\<lambda>x. x)"
       "(\<lambda>x. x)"
  unfolding classical_functor_def
  apply (simp add: CC.classical_category_axioms SCC.classical_category_axioms)
  unfolding classical_functor_axioms_def
  using SObj_Obj apply simp
  unfolding SArr_def by simp

definition inclusion_functor where
  "inclusion_functor = Inclusion.map"

lemma inclusion_functor: "functor SCC.comp CC.comp inclusion_functor"
  unfolding inclusion_functor_def
  using Inclusion.is_functor.

lemma inclusion_functor_simp : 
  "inclusion_functor x = (if SCC.arr x then x else None)"
  unfolding inclusion_functor_def
  unfolding Inclusion.map_def
  unfolding CC.null_char SCC.arr_char
  by simp
  
end

sublocale classical_full_subcategory \<subseteq> classical_category SObj SArr Dom Cod Ide Comp
  using is_classical_category.


context classical_category
begin

definition In_Hom where
  "In_Hom f A B = (Arr f \<and> Dom f = A \<and> Cod f = B)"

lemma in_hom_char: "in_hom f a b = (ide a \<and> ide b \<and> f \<noteq> None \<and> In_Hom (the f) (Dom (the a)) (Dom (the b)))"
  apply auto
proof-
  assume f_hom: "in_hom f a b"
  then have arr_f : "arr f"
    by blast
  then show "\<exists>y. f = Some y"
    unfolding arr_char by simp
  show "In_Hom (the f) (Dom (the a)) (Dom (the b))"
    apply (rule_tac in_homE [OF f_hom])
    unfolding In_Hom_def
    unfolding dom_char cod_char
    apply simp
    unfolding arr_char
    apply simp
  proof-
    assume eq_a: "Some (Id (Dom (the f))) = a"
    assume eq_b: "Some (Id (Cod (the f))) = b"
    show "Dom (the f) = Dom (the a) \<and> Cod (the f) = Dom (the b)"
      unfolding reverse_equality [OF eq_a]
      unfolding reverse_equality [OF eq_b]
      apply simp
      apply (subst Dom_Id)
       apply (rule_tac Obj_Dom)
      using arr_f arr_char apply simp
      apply (subst Dom_Id)
       apply (rule_tac Obj_Cod)
      using arr_f arr_char apply simp
      by simp
  qed
next
  fix y
  assume "ide a" "ide b"
  assume f_Hom: "In_Hom y (Dom (the a)) (Dom (the b))"
  assume "f = Some y"
  show "in_hom (Some y) a b"
    apply (rule_tac in_homI)
  proof-
    show arr_y: "arr (Some y)"
      unfolding arr_char apply simp
      using f_Hom 
      unfolding In_Hom_def by simp
    show "dom (Some y) = a"
      unfolding dom_char
      using arr_y apply simp
      using f_Hom
      unfolding In_Hom_def apply simp
      using \<open>ide a\<close>
      unfolding ide_char by simp
    show "cod (Some y) = b"
      unfolding cod_char
      using arr_y apply simp
      using f_Hom
      unfolding In_Hom_def apply simp
      using \<open>ide b\<close>
      unfolding ide_char by simp
  qed
qed




end

locale classical_category_with_products =
  CC: classical_category Obj Arr Dom Cod Ide Comp
  for Obj :: "'a \<Rightarrow> bool"
  and Arr :: "'b \<Rightarrow> bool"
  and Dom :: "'b \<Rightarrow> 'a"
  and Cod :: "'b \<Rightarrow> 'a"
  and Ide :: "'a \<Rightarrow> 'b"
  and Comp :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and Prod :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and Proj1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  and Proj2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'b" +
assumes Prod_Obj : "\<And> a b . Obj a \<Longrightarrow> Obj b \<Longrightarrow> Obj (Prod a b)"
  and Proj1_In_Hom : "\<And> a b . Obj a \<Longrightarrow> Obj b \<Longrightarrow> CC.In_Hom (Proj1 a b) (Prod a b) a"
  and Proj2_In_Hom : "\<And> a b . Obj a \<Longrightarrow> Obj b \<Longrightarrow> CC.In_Hom (Proj2 a b) (Prod a b) b"
  and UP : "\<And>a b c f g. CC.In_Hom f c a \<Longrightarrow> CC.In_Hom g c b \<Longrightarrow>
            \<exists>! h. CC.In_Hom h c (Prod a b) \<and> Comp (Proj1 a b) h = f \<and> Comp (Proj2 a b) h = g"
begin

definition UP_map where
  "UP_map a b c f g = (SOME h. CC.In_Hom h c (Prod a b) \<and> Comp (Proj1 a b) h = f \<and> Comp (Proj2 a b) h = g)"

lemma UP_existence : "\<And>a b c f g. CC.In_Hom f c a \<Longrightarrow> CC.In_Hom g c b \<Longrightarrow>
            CC.In_Hom (UP_map a b c f g) c (Prod a b) \<and>
            Comp (Proj1 a b) (UP_map a b c f g) = f \<and>
            Comp (Proj2 a b) (UP_map a b c f g) = g"
  unfolding UP_map_def
  apply (rule_tac someI_ex)
  using UP by blast

lemma UP_uniqueness: "\<And>a b c f g h. CC.In_Hom f c a \<Longrightarrow> CC.In_Hom g c b \<Longrightarrow>
            CC.In_Hom h c (Prod a b) \<and>
            Comp (Proj1 a b) h = f \<and>
            Comp (Proj2 a b) h = g
            \<Longrightarrow> h = (UP_map a b c f g)"
proof-
  fix a b c f g h
  assume f_hom : "CC.In_Hom f c a"
  assume g_hom : "CC.In_Hom g c b"
  assume h_prop: "CC.In_Hom h c (Prod a b) \<and> Comp (Proj1 a b) h = f \<and> Comp (Proj2 a b) h = g"
  have UP_map_prop: "CC.In_Hom (UP_map a b c f g) c (Prod a b) \<and>
        Comp (Proj1 a b) (UP_map a b c f g) = f \<and>
        Comp (Proj2 a b) (UP_map a b c f g) = g"
    using UP_existence [OF f_hom g_hom].
  have "\<exists>! h. CC.In_Hom h c (Prod a b) \<and> Comp (Proj1 a b) h = f \<and> Comp (Proj2 a b) h = g"
    using UP [OF f_hom g_hom].
  then show "h = UP_map a b c f g"
    using h_prop UP_map_prop by auto
qed


lemma "category_with_products CC.comp
       (\<lambda>a b . Some (Ide (Prod (Dom (the a)) (Dom (the b)))))
       (\<lambda>a b . Some (Proj1 (Dom (the a)) (Dom (the b))))
       (\<lambda>a b . Some (Proj2 (Dom (the a)) (Dom (the b))))
       (\<lambda>f g . Some (UP_map (Cod (the f)) (Cod (the g)) (Dom (the f)) (the f) (the g)))"
  unfolding category_with_products_def
  unfolding category_with_products_axioms_def
  unfolding binary_product_def
  apply (simp add: CC.induces_category)
  unfolding binary_product_axioms_def
  apply auto
proof-
  have prod_obj: "\<And>a b. CC.ide a \<Longrightarrow> CC.ide b \<Longrightarrow> Obj (Prod (Dom (the a)) (Dom (the b)))"
    apply (rule_tac Prod_Obj)
    unfolding CC.ide_char
    using CC.Obj_Dom by auto
  show prod_ide: "\<And>a b. CC.ide a \<Longrightarrow> CC.ide b \<Longrightarrow> CC.ide (Some (Ide (Prod (Dom (the a)) (Dom (the b)))))"
    apply (subst CC.ide_char)
    using CC.Dom_Id [OF prod_obj] CC.Arr_Id [OF prod_obj] by simp
  show "\<And>a b. CC.ide a \<Longrightarrow>
           CC.ide b \<Longrightarrow>
           CC.in_hom (Some (Proj1 (Dom (the a)) (Dom (the b)))) 
           (Some (Ide (Prod (Dom (the a)) (Dom (the b))))) a"
    unfolding CC.in_hom_char
    apply (simp add: prod_ide)
    apply (subst CC.Dom_Id)
    using prod_obj apply simp
    apply (rule_tac Proj1_In_Hom)
     apply (rule_tac CC.Obj_Dom)
    apply (simp add: CC.ide_char)
     apply (rule_tac CC.Obj_Dom)
    by (simp add: CC.ide_char)
  show "\<And>a b. CC.ide a \<Longrightarrow>
           CC.ide b \<Longrightarrow>
           CC.in_hom (Some (Proj2 (Dom (the a)) (Dom (the b)))) 
           (Some (Ide (Prod (Dom (the a)) (Dom (the b))))) b"
    unfolding CC.in_hom_char
    apply (simp add: prod_ide)
    apply (subst CC.Dom_Id)
    using prod_obj apply simp
    apply (rule_tac Proj2_In_Hom)
     apply (rule_tac CC.Obj_Dom)
    apply (simp add: CC.ide_char)
     apply (rule_tac CC.Obj_Dom)
    by (simp add: CC.ide_char)
  show "\<And>f g. CC.arr f \<Longrightarrow>
           CC.arr g \<Longrightarrow>
           CC.dom f = CC.dom g \<Longrightarrow>
           CC.in_hom (Some (UP_map (Cod (the f)) (Cod (the g)) (Dom (the f)) (the f) (the g))) (CC.dom g)
            (Some (Ide (Prod (Dom (the (CC.cod f))) (Dom (the (CC.cod g))))))"
    unfolding CC.in_hom_char
    apply auto
    using prod_ide apply simp
    apply (subst CC.Dom_Id)
    using prod_obj apply simp
  proof-
    fix f g
    assume "CC.arr f"
    then have "Arr (the f)"
      unfolding CC.arr_char by simp
    assume "CC.arr g"
    then have "Arr (the g)"
      unfolding CC.arr_char by simp
    assume "CC.dom f = CC.dom g"
    then have "Dom (the f) = Dom (the g)"
      unfolding CC.dom_char CC.cod_char
      apply (simp add: \<open>CC.arr f\<close> \<open>CC.arr g\<close>)
      using CC.Dom_Id CC.Obj_Dom \<open>Arr (the f)\<close> \<open>Arr (the g)\<close> by fastforce
    show "CC.In_Hom (UP_map (Cod (the f)) (Cod (the g)) (Dom (the f)) (the f) (the g)) (Dom (the (CC.dom g)))
            (Prod (Dom (the (CC.cod f))) (Dom (the (CC.cod g))))"
      unfolding CC.dom_char CC.cod_char
      apply (simp add: \<open>CC.arr f\<close> \<open>CC.arr g\<close>)
      unfolding CC.Dom_Id [OF CC.Obj_Cod [OF \<open>Arr (the f)\<close>]]
      unfolding CC.Dom_Id [OF CC.Obj_Dom [OF \<open>Arr (the g)\<close>]]
      unfolding CC.Dom_Id [OF CC.Obj_Cod [OF \<open>Arr (the g)\<close>]]
      unfolding \<open>Dom (the f) = Dom (the g)\<close>
      apply (rule_tac conjunct1 [OF UP_existence])
      unfolding CC.In_Hom_def
      unfolding \<open>Dom (the f) = Dom (the g)\<close>
      by (simp_all add: \<open>Arr (the f)\<close> \<open>Arr (the g)\<close>)
  qed
(*TODO: Complete proof *)
  oops


end





context abstracted_category
begin

definition A_functor where
  "A_functor f = (if C.arr f then A f else null)"

lemma A_functor: "functor C comp A_functor"
  unfolding functor_def
  apply (simp add: C.category_axioms is_category)
  unfolding functor_axioms_def
  apply auto
      apply (simp add: A_functor_def)
proof-
  show arr: "\<And>f. C.arr f \<Longrightarrow> arr (A_functor f)"
    unfolding A_functor_def apply simp
    using domain_closed arr_char rep_abs by force
  show dom: "\<And>f. C.arr f \<Longrightarrow> local.dom (A_functor f) = A_functor (C.dom f)"
    unfolding A_functor_def apply simp
    by (simp add: arr_char dom_char domain_closed rep_abs)
  show "\<And>f. C.arr f \<Longrightarrow> cod (A_functor f) = A_functor (C.cod f)"
    unfolding A_functor_def apply simp
    by (simp add: arr_char cod_char domain_closed rep_abs)
  fix g f
  assume arr_gf : "C.seq g f"
  show "A_functor (g \<cdot>\<^sub>C f) = A_functor g \<cdot> A_functor f"
    apply (rule_tac C.seqE [OF arr_gf])
    unfolding A_functor_def apply simp
    by (simp add: domain_closed local.comp_def rep_abs)
qed


end







end
