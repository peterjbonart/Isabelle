theory AbelianGroups
  imports Main
         "HOL-Algebra.Group"
         "HOL-Algebra.Free_Abelian_Groups"
         PointedSet
         "Category3.FunctorCategory"
         SomeCategoryTheory
         "Category3.Yoneda"
         "Category3.SetCategory"
         PointedSetFactorization
         H_Ab
         SimplicialSet
begin



lemma finite_induct' : 
  assumes "finite x"
  shows "P {} \<Longrightarrow> 
        (\<And>A a. finite A \<Longrightarrow> P A \<Longrightarrow> a \<notin> A \<Longrightarrow> P (insert a A)) 
         \<Longrightarrow> P x"
  apply (rule_tac finite.induct [OF assms])
   apply simp
proof-
  fix A a
  assume "P A"
  assume "finite A"
  assume step: "(\<And>A a. finite A \<Longrightarrow> P A \<Longrightarrow> a \<notin> A \<Longrightarrow> P (insert a A))"
  have "a \<in> A \<or> a \<notin> A" by auto
  then show "P (insert a A)"
  proof
    assume "a \<in> A"
    then have "insert a A = A" by auto
    then show "P (insert a A)"
      by (simp add: \<open>P A\<close>)
  next
    show "a \<notin> A \<Longrightarrow> P (insert a A)"
      apply (rule_tac step)
      using \<open>finite A\<close> \<open>P A\<close> by simp_all
  qed
qed







section "Category of abelian groups"

type_synonym ('c, 'd) Ab_hom = "(('c \<Rightarrow> 'c) \<times> ('c, 'd) monoid_scheme \<times> ('c, 'd) monoid_scheme) option"




locale abelian_group_category
begin


definition Obj' where
  "Obj' G = comm_group G"

definition Dom' where
  "Dom' f = fst (snd f)"

definition Cod' where
  "Cod' f = snd (snd f)"

definition Arr' where
  "Arr' f = (Obj' (Dom' f) \<and> Obj' (Cod' f) \<and>
            (fst f \<in> extensional (carrier (Dom' f))) \<and>
            (fst f \<in> hom (Dom' f) (Cod' f)))"

definition Id' where
  "Id' G = ((\<lambda>x \<in> carrier G. x), (G, G))"

definition Comp' where
  "Comp' f g = ((\<lambda>x \<in>carrier (Dom' g).  fst f (fst g x)), (Dom' g, Cod' f))"







interpretation AbCC : classical_category Obj' Arr' Dom' Cod' Id' Comp'
  unfolding classical_category_def
  apply auto
proof-
  fix G
  assume "Obj' G"
  then show "Arr' (Id' G)"
    unfolding Arr'_def Id'_def Dom'_def Cod'_def apply simp
    unfolding hom_def Obj'_def apply auto
    by (simp add: comm_groupE(1))
  show "Dom' (Id' G) = G"
    unfolding Arr'_def Id'_def Dom'_def by simp
  show "Cod' (Id' G) = G"
    unfolding Arr'_def Id'_def Cod'_def by simp
next
  fix f 
  fix G H :: "('a, 'b) monoid_scheme"
  assume "Arr' (f, G, H)"
  then show "Obj' (Dom' (f, G, H))"
    unfolding Arr'_def by simp
  from \<open>Arr' (f, G, H)\<close> show "Obj' (Cod' (f, G, H))"
    unfolding Arr'_def by simp
  from \<open>Arr' (f, G, H)\<close> have ext_f: "f \<in> extensional (carrier G)"
    unfolding Arr'_def Dom'_def by simp
  from \<open>Arr' (f, G, H)\<close> have hom_f: "f \<in> hom G H"
    unfolding Arr'_def Dom'_def Cod'_def by simp
  show "Comp' (f, G, H) (Id' (Dom' (f, G, H))) = (f, G, H)"
    unfolding Comp'_def Id'_def Dom'_def Cod'_def apply simp
    apply (rule_tac ext)
    using ext_f
    unfolding extensional_def by auto
  show "Comp' (Id' (Cod' (f, G, H))) (f, G, H) = (f, G, H)"
    unfolding Comp'_def Id'_def Dom'_def Cod'_def apply simp
    apply (rule_tac ext)
    using ext_f hom_f
    unfolding extensional_def hom_def by auto
next
  fix f g
  fix A B C D :: "('a, 'b) monoid_scheme"
  assume arr_f: "Arr' (f, A, B)"
  assume arr_g: "Arr' (g, C, D)"
  assume "Cod' (f, A, B) = Dom' (g, C, D)"
  then have "B = C"
    unfolding Cod'_def Dom'_def by simp
  show "Arr' (Comp' (g, C, D) (f, A, B))"
    using arr_f arr_g
    unfolding Arr'_def Comp'_def Dom'_def Cod'_def apply simp
    unfolding \<open>B = C\<close>
    unfolding hom_def
    apply auto
  proof-
    fix x y
    assume "Obj' A"
    then have "comm_group A"
      unfolding Obj'_def.
    assume x_A: "x \<in> carrier A" 
    assume y_A: "y \<in> carrier A"
    from x_A y_A \<open>comm_group A\<close> have "x \<otimes>\<^bsub>A\<^esub> y \<in> carrier A" 
      by (simp add: comm_groupE(1))
    then show "x \<otimes>\<^bsub>A\<^esub> y \<notin> carrier A \<Longrightarrow> undefined = g (f x) \<otimes>\<^bsub>D\<^esub> g (f y)"
      by simp
    assume f_AC: "f \<in> carrier A \<rightarrow> carrier C"
    from f_AC have fx_C : "f x \<in> carrier C"
      using x_A by auto
    from f_AC have fy_C : "f y \<in> carrier C"
      using y_A by auto
    assume "\<forall>x\<in>carrier C. \<forall>y\<in>carrier C. g (x \<otimes>\<^bsub>C\<^esub> y) = g x \<otimes>\<^bsub>D\<^esub> g y"
    then show "g (f x \<otimes>\<^bsub>C\<^esub> f y) = g (f x) \<otimes>\<^bsub>D\<^esub> g (f y)"
      using fx_C fy_C by simp
  qed
  show "Dom' (Comp' (g, C, D) (f, A, B)) = Dom' (f, A, B)"
    unfolding Comp'_def Dom'_def by simp
  show "Cod' (Comp' (g, C, D) (f, A, B)) = Cod' (g, C, D)"
    unfolding Comp'_def Cod'_def by simp
next
  fix f g h
  fix A B C D E F :: "('a, 'b) monoid_scheme"
  assume arr_f : "Arr' (f, A, B)"
  assume arr_g : "Arr' (g, C, D)"
  assume arr_h : "Arr' (h, E, F)"
  assume "Cod' (f, A, B) = Dom' (g, C, D)"
  then have "B = C"
    unfolding Cod'_def Dom'_def by simp
  assume "Cod' (g, C, D) = Dom' (h, E, F)"
  then have "D = E"
    unfolding Cod'_def Dom'_def by simp
  show "Comp' (Comp' (h, E, F) (g, C, D)) (f, A, B) =
       Comp' (h, E, F) (Comp' (g, C, D) (f, A, B))"
    using arr_f
    unfolding Comp'_def Dom'_def Cod'_def apply auto
    apply (rule_tac ext)
    unfolding Arr'_def Dom'_def Cod'_def hom_def \<open>B = C\<close>
    by auto
qed


definition comp where
  "comp = AbCC.comp"

lemma is_category : "category comp"
  unfolding comp_def
  using AbCC.induces_category.

lemma is_classical_category : "classical_category Obj' Arr' Dom' Cod' Id' Comp'"
  using AbCC.classical_category_axioms.


lemma fun_eqI:
  assumes "AbCC.arr f" "AbCC.arr g"
  and dom_eq:  "AbCC.dom f = AbCC.dom g"
  and cod_eq: "AbCC.cod f = AbCC.cod g"
  and fst_eq : "\<And>x. x \<in> carrier (Dom' (the f)) \<Longrightarrow>
                    x \<in> carrier (Dom' (the g)) \<Longrightarrow>
                    fst (the f) x = fst (the g) x"
shows "f = g"
proof-
  have dom_eq' : "Dom' (the f) = Dom' (the g)"
    using dom_eq
    unfolding AbCC.dom_char
    apply (simp add: assms)
    unfolding Id'_def by simp

  have "the f = the g"
  proof
    show "fst (the f) = fst (the g)"
      apply (rule_tac ext)
    proof-
      fix x
      have "x \<in> carrier (Dom' (the f)) \<or> x \<notin> carrier (Dom' (the f))" by auto
      then show "fst (the f) x = fst (the g) x"
      proof
        show "x \<in> carrier (Dom' (the f)) \<Longrightarrow> fst (the f) x = fst (the g) x"
          apply (rule_tac fst_eq)
          unfolding dom_eq'.
        show "x \<notin> carrier (Dom' (the f)) \<Longrightarrow> fst (the f) x = fst (the g) x"
          using \<open>AbCC.arr f\<close> \<open>AbCC.arr g\<close>
          unfolding AbCC.arr_char Arr'_def extensional_def
          unfolding dom_eq'
          by simp
      qed
    qed
    show "snd (the f) = snd (the g)"
    proof
      show "fst (snd (the f)) = fst (snd (the g))"
        using dom_eq'
        unfolding Dom'_def.
      show "snd (snd (the f)) = snd (snd (the g))"
        using cod_eq
        unfolding AbCC.cod_char
        apply (simp add: assms)
        unfolding Id'_def Cod'_def
        by simp
    qed
  qed
  then show "f = g"
    using \<open>AbCC.arr f\<close> \<open>AbCC.arr g\<close>
    unfolding AbCC.arr_char
    by auto
qed






lemma comp_eqI :
  assumes "AbCC.arr f" "AbCC.arr g" "AbCC.arr h"
  and "AbCC.dom f = AbCC.dom h"
  and "AbCC.cod f = AbCC.cod g"
  and "AbCC.cod h = AbCC.dom g"
  and fst_eq: "\<And>x. x \<in> carrier (Dom' (the f)) \<Longrightarrow>
           x \<in> carrier (Dom' (the h)) \<Longrightarrow>
           fst (the h) x \<in> carrier (Dom' (the g)) \<Longrightarrow>
         fst (the f) x = fst (the g) (fst (the h) x)"
shows "f = comp g h"
  unfolding comp_def
  apply (subst AbCC.comp_simp)
proof-
  have "AbCC.seq g h"
    apply (rule_tac AbCC.seqI)
    using assms by simp_all
  then show "AbCC.comp g h \<noteq> AbCC.null"
    by auto
  then have "f = Some (the f)"
    using \<open>AbCC.arr f\<close>
    unfolding AbCC.arr_char by simp

  show "f = Some (Comp' (the g) (the h))"
    unfolding Comp'_def
    apply (subst \<open>f = Some (the f)\<close>)
    apply simp
  proof

    have dom_eq : "Dom' (the f) = Dom' (the h)"
      using \<open>AbCC.dom f = AbCC.dom h\<close>
      unfolding AbCC.dom_char
      using \<open>AbCC.arr f\<close> \<open>AbCC.arr h\<close>
      apply simp
      unfolding Id'_def Dom'_def
      by simp

    show "snd (the f) =
    snd (\<lambda>x\<in>carrier (Dom' (the h)). fst (the g) (fst (the h) x), Dom' (the h),
         Cod' (the g))"
      apply simp
    proof
      show "fst (snd (the f)) = fst (Dom' (the h), Cod' (the g))"
        using dom_eq
        unfolding Dom'_def by simp
      show "snd (snd (the f)) = snd (Dom' (the h), Cod' (the g))"
        using \<open>AbCC.cod f = AbCC.cod g\<close>
        unfolding AbCC.cod_char
        using \<open>AbCC.arr f\<close> \<open>AbCC.arr g\<close>
        apply simp
        unfolding Id'_def Cod'_def
        by simp
    qed
    show "fst (the f) =
    fst (\<lambda>x\<in>carrier (Dom' (the h)). fst (the g) (fst (the h) x), Dom' (the h),
         Cod' (the g))"
      apply (rule_tac ext)
      apply auto
    proof-
      show "\<And>x. x \<notin> carrier (Dom' (the h)) \<Longrightarrow> fst (the f) x = undefined"
        unfolding reverse_equality [OF dom_eq]
        using \<open>AbCC.arr f\<close>
        unfolding AbCC.arr_char Arr'_def extensional_def
        by auto

      have seq_eq : "Dom' (the g) = Cod' (the h)"
        using \<open>AbCC.cod h = AbCC.dom g\<close>
        unfolding AbCC.cod_char AbCC.dom_char
        using \<open>AbCC.arr h\<close> \<open>AbCC.arr g\<close>
        apply simp
        unfolding Id'_def by simp

      fix x
      assume x_in: "x \<in> carrier (Dom' (the h))"
      then have hx_in: "(fst (the h) x) \<in> carrier (Dom' (the g))"
        unfolding seq_eq
        using \<open>AbCC.arr h\<close>
        unfolding AbCC.arr_char Arr'_def hom_def
        by auto
      show "fst (the f) x = fst (the g) (fst (the h) x)"
        apply (rule_tac fst_eq)
        unfolding dom_eq
        using x_in hx_in by auto
    qed
  qed
qed


lemma in_hom_mapsto:
  assumes "AbCC.in_hom f A B"
  and AC: "carrier (Dom' (the A)) = C"
  and BD: "carrier (Dom' (the B)) = D"
shows "fst (the f) \<in> C \<rightarrow> D"
proof-
  have In_Hom: "AbCC.In_Hom (the f) (Dom' (the A)) (Dom' (the B))"
  using \<open>AbCC.in_hom f A B\<close>
  unfolding AbCC.in_hom_char
  unfolding AbCC.In_Hom_def
  by simp
  then have dom_eq : "Dom' (the f) = Dom' (the A)"
    unfolding AbCC.In_Hom_def by simp
  from In_Hom have cod_eq : "Cod' (the f) = Dom' (the B)"
    unfolding AbCC.In_Hom_def by simp
  from In_Hom have "Arr' (the f)"
    unfolding AbCC.In_Hom_def by simp
  then show "fst (the f) \<in> C \<rightarrow> D"
    unfolding Arr'_def
    unfolding hom_def
    unfolding dom_eq cod_eq
    unfolding AC BD
    by simp
qed




context begin

section "Hom-functor for abelian groups"

interpretation Hom : hom_functor AbCC.comp SetCat.comp "(\<lambda>_. SetCat.UP)"
  using AbCC.has_hom_functor.

definition zero_map where
  "zero_map G H = (Some ((\<lambda>x \<in> carrier G. \<one>\<^bsub>H\<^esub>), G, H))"




lemma zero_in_hom1: assumes G : "comm_group G"
  and H : "comm_group H"
shows "AbCC.in_hom (zero_map G H) (Some (Id' G)) (Some (Id' H))"
proof-
  have arr: "AbCC.arr (Some (\<lambda>x\<in>carrier G. \<one>\<^bsub>H\<^esub>, G, H))"
    unfolding AbCC.arr_char apply simp
    unfolding Arr'_def Obj'_def Dom'_def Cod'_def apply (simp add: G H)
    unfolding hom_def apply auto
    using comm_groupE(2) [OF H] apply simp
    using comm_groupE(5) [OF H comm_groupE(2) [OF H]] apply simp
    using comm_groupE(1) [OF G] by simp
  show "AbCC.in_hom (zero_map G H) (Some (Id' G)) (Some (Id' H))"
    unfolding zero_map_def
    apply (rule_tac AbCC.in_homI)
    unfolding AbCC.dom_char AbCC.cod_char
      apply (simp_all add: arr)
    unfolding Dom'_def Cod'_def by simp_all
qed

lemma zero_in_hom2: assumes G : "comm_group G"
  and H : "comm_group H"
  shows "SetCat.UP (zero_map G H) \<in> Hom.set (Some (Id' G), Some (Id' H))"
proof-
  have in_hom: "AbCC.in_hom (zero_map G H) (Some (Id' G)) (Some (Id' H))"
    using zero_in_hom1 [OF G H].
  have ide_G: "AbCC.ide (Some (Id' G))"
    unfolding AbCC.ide_char apply auto
     apply (rule_tac AbCC.Arr_Id)
    unfolding Obj'_def apply (simp add: G)
    unfolding Id'_def Dom'_def by simp
  have ide_H: "AbCC.ide (Some (Id' H))"
    unfolding AbCC.ide_char apply auto
     apply (rule_tac AbCC.Arr_Id)
    unfolding Obj'_def apply (simp add: H)
    unfolding Id'_def Dom'_def by simp
  show "SetCat.UP (zero_map G H) \<in> Hom.set (Some (Id' G), Some (Id' H))"
    using Hom.\<phi>_local_bij [OF ide_G ide_H]
    unfolding bij_betw_def
    using in_hom by auto
qed





interpretation pfactor: pointed_set_factorization SetCat.comp Hom.CopxC.comp Hom.map 
     "(\<lambda>c. SetCat.UP (zero_map (fst (snd (the (fst c)))) (fst (snd (the (snd c))))))"
  unfolding pointed_set_factorization_def
  apply (simp add: SetCat.is_set_category Hom.functor_axioms)
  unfolding pointed_set_factorization_axioms_def
  apply auto
   apply (subst Hom.S.set_mkIde)
    apply (simp add: Hom.set_subset_Univ)
proof-
  have zero_in_hom: "\<And>a b. AbCC.ide a \<Longrightarrow>
           AbCC.ide b \<Longrightarrow> SetCat.UP (zero_map (fst (snd (the a))) (fst (snd (the b)))) \<in> Hom.set (a, b)
                       \<and> AbCC.in_hom (zero_map (fst (snd (the a))) (fst (snd (the b)))) a b "
  proof
    fix a b :: "(('c \<Rightarrow> 'c) \<times> ('c, 'd) monoid_scheme \<times> ('c, 'd) monoid_scheme) option"
    assume ide_a : "AbCC.ide a"
    then interpret A: comm_group "(fst (snd (the a)))"
      unfolding AbCC.ide_char Arr'_def Obj'_def Dom'_def by simp
    from ide_a have a_eq : "Some (Id' (fst (snd (the a)))) = a"
      unfolding AbCC.ide_char Dom'_def by simp
    assume ide_b : "AbCC.ide b"
    then interpret B: comm_group "(fst (snd (the b)))"
      unfolding AbCC.ide_char Arr'_def Obj'_def Dom'_def by simp
    from ide_b have b_eq : "Some (Id' (fst (snd (the b)))) = b"
      unfolding AbCC.ide_char Dom'_def by simp
    show "SetCat.UP (zero_map (fst (snd (the a))) (fst (snd (the b)))) \<in> Hom.set (a, b)"
      using zero_in_hom2 [OF A.comm_group_axioms B.comm_group_axioms]
      unfolding a_eq b_eq by simp
    show "AbCC.in_hom (zero_map (fst (snd (the a))) (fst (snd (the b)))) a b"
      using zero_in_hom1 [OF A.comm_group_axioms B.comm_group_axioms]
      unfolding a_eq b_eq by simp
  qed
  then show "\<And>a b. AbCC.ide a \<Longrightarrow>
           AbCC.ide b \<Longrightarrow>
           pointed_set.Obj' (SetCat.UP (zero_map (fst (snd (the a))) (fst (snd (the b)))), Hom.set (a, b))"
    unfolding pointed_set.Obj'_def apply simp
    by blast
  fix a b :: "(('c \<Rightarrow> 'c) \<times> ('c, 'd) monoid_scheme \<times> ('c, 'd) monoid_scheme) option"
  assume arr_a: "AbCC.arr a"
  assume arr_b: "AbCC.arr b"
  have arr_ab : "Hom.CopxC.arr (a, b)"
    by (simp add: arr_a arr_b)
  have arr_hom_ab : "Hom.S.arr (Hom.map (a, b))"
    apply (rule_tac Hom.preserves_arr)
    using arr_ab.

  show "Hom.S.Fun (Hom.map (a, b))
            (SetCat.UP (zero_map (fst (snd (the (AbCC.cod a)))) (fst (snd (the (AbCC.dom b)))))) =
           SetCat.UP (zero_map (fst (snd (the (AbCC.dom a)))) (fst (snd (the (AbCC.cod b)))))"
    unfolding Hom.map_def
    apply (simp add: arr_a arr_b)
    apply (subst Hom.S.Fun_mkArr)
    using arr_hom_ab
    unfolding Hom.map_def
    apply (simp add: arr_a arr_b)  
    apply (simp add: zero_in_hom  [OF AbCC.ide_cod
              [OF arr_a] AbCC.ide_dom [OF arr_b]])
  proof-
    define zero1 where "zero1 = (zero_map (fst (snd (the (AbCC.cod a)))) (fst (snd (the (AbCC.dom b)))))"
    have arr1: "AbCC.arr zero1"
      using zero_in_hom [OF AbCC.ide_cod
              [OF arr_a] AbCC.ide_dom [OF arr_b]]
      unfolding zero1_def by blast
    have seq1: "AbCC.seq zero1 a"
      apply (rule_tac AbCC.seqI')
       apply (rule_tac AbCC.in_homI)
      apply (simp_all add: arr_a)
      unfolding zero1_def
      apply (rule_tac conjunct2 [OF zero_in_hom])
      using AbCC.ide_cod arr_a apply simp
      using AbCC.ide_dom arr_b by simp
    define zero2 where "zero2 = (zero_map (fst (snd (the (AbCC.dom a)))) (fst (snd (the (AbCC.dom b)))))"
    have a_zero_eq: "AbCC.comp zero1 a = zero2"
      apply (subst AbCC.comp_def)
      using AbCC.seqE [OF seq1] arr_a arr1
      unfolding AbCC.arr_char
      apply simp
    proof-
      have a_carrier: "fst (the a) \<in> carrier (Dom' (the a)) \<rightarrow> carrier (Cod' (the a))"
        using arr_a
        unfolding AbCC.arr_char Arr'_def hom_def by simp
      have dom_eq: "fst (snd (the a)) = fst (snd (the (AbCC.dom a)))"
        unfolding AbCC.dom_char
        by (simp add: arr_a Id'_def Dom'_def)
      show "Some (Comp' (the zero1) (the a)) = zero2"
        apply (subst Comp'_def)
        unfolding zero1_def zero2_def
        unfolding zero_map_def
        apply (simp add: Dom'_def Cod'_def dom_eq)
        apply (rule_tac ext)
        apply auto
        unfolding AbCC.cod_char AbCC.dom_char
        apply (simp add: arr_a Id'_def Dom'_def Cod'_def)
        using a_carrier
        unfolding Dom'_def Cod'_def by auto
    qed
    have arr2: "AbCC.arr zero2"
      using zero_in_hom [OF AbCC.ide_dom
              [OF arr_a] AbCC.ide_dom [OF arr_b]]
      unfolding zero2_def by blast
    have seq2: "AbCC.seq b zero2"
      apply (rule_tac AbCC.seqI')
      unfolding zero2_def
      apply (rule_tac conjunct2 [OF zero_in_hom])
      using AbCC.ide_dom arr_a apply simp
      using AbCC.ide_dom arr_b apply simp
      apply (rule_tac AbCC.in_homI)
      by (simp_all add: arr_b)
    have b_zero_eq : "AbCC.comp b zero2 = (zero_map (fst (snd (the (AbCC.dom a)))) (fst (snd (the (AbCC.cod b)))))"
      apply (subst AbCC.comp_def)
      using AbCC.seqE [OF seq2] arr_b arr2
      unfolding AbCC.arr_char
      apply simp
    proof-
      have b_in_hom : "fst (the b) \<in> hom (Dom' (the b)) (Cod' (the b))"
        using arr_b
        unfolding AbCC.arr_char Arr'_def by simp
      interpret BDom: comm_group "(fst (snd (the b)))"
        using arr_b
        unfolding AbCC.arr_char Arr'_def Obj'_def Dom'_def by simp
      interpret BCod: comm_group "(snd (snd (the b)))"
        using arr_b
        unfolding AbCC.arr_char Arr'_def Obj'_def Cod'_def by simp
      have cod_eq : "snd (snd (the b)) = fst (snd (the (AbCC.cod b)))"
        unfolding AbCC.cod_char
        by (simp add: arr_b Id'_def Cod'_def)
      show "Some (Comp' (the b) (the zero2)) = zero_map (fst (snd (the (AbCC.dom a)))) (fst (snd (the (AbCC.cod b))))"
        apply (subst Comp'_def)
        unfolding zero2_def
        unfolding zero_map_def
        apply (simp add: Dom'_def Cod'_def cod_eq)
        apply (rule_tac ext)
        apply auto
        unfolding AbCC.cod_char AbCC.dom_char
        apply (simp add: arr_b arr_a Id'_def Dom'_def Cod'_def)
        using b_in_hom
        unfolding Dom'_def Cod'_def
        by (simp add: hom_one)
    qed
    show "SetCat.UP
     (AbCC.comp b (AbCC.comp (zero_map (fst (snd (the (AbCC.cod a)))) (fst (snd (the (AbCC.dom b))))) a)) =
    SetCat.UP (zero_map (fst (snd (the (AbCC.dom a)))) (fst (snd (the (AbCC.cod b)))))"
      unfolding reverse_equality [OF zero1_def]
      apply (subst a_zero_eq)
      using b_zero_eq by simp
  qed
qed



definition pointed_hom_functor where
  "pointed_hom_functor = pfactor.map"

lemma pointed_hom_functor : "functor Hom.CopxC.comp pointed_set.pointed_set_comp pointed_hom_functor"
  unfolding pointed_hom_functor_def
  using pfactor.is_functor.


lemma pointed_hom_binary_functor : "binary_functor Hom.Cop.comp comp pointed_set.pointed_set_comp
                                    pointed_hom_functor"
  unfolding binary_functor_def comp_def
  apply (simp add: pointed_hom_functor)
  unfolding product_category_def
  by (simp add: AbCC.induces_category Hom.Cop.category_axioms pointed_set.is_category)

end

section "Lawvere theory of abelian groups"

term free_Abelian_group 

definition is_Z_tothe_n :: "(nat \<Rightarrow>\<^sub>0 int) monoid \<Rightarrow> bool" where
  "is_Z_tothe_n A = (\<exists> (n :: nat). free_Abelian_group {(i :: nat). i < n} = A)"

interpretation LawvAb : classical_full_subcategory 
     Obj' Arr' Dom' Cod' Id' Comp' is_Z_tothe_n
  unfolding classical_full_subcategory_def
  apply (simp add: AbCC.classical_category_axioms)
  unfolding classical_full_subcategory_axioms_def
  unfolding is_Z_tothe_n_def Obj'_def
  apply auto
  by (simp add: abelian_free_Abelian_group)


definition Lawv_comp where
  "Lawv_comp = LawvAb.comp"

lemma Lawv_is_category : "category Lawv_comp"
  unfolding Lawv_comp_def
  using LawvAb.induces_category.

lemma Lawv_is_classical_category : "classical_category is_Z_tothe_n LawvAb.SArr Dom' Cod' Id' Comp'"
  using LawvAb.is_classical_category.

definition LawvInclusion where
  "LawvInclusion = LawvAb.inclusion_functor"


lemma LawvInclusion_functor : "functor LawvAb.comp AbCC.comp LawvInclusion"
  unfolding LawvInclusion_def
  using LawvAb.inclusion_functor.




end


locale group_to_Lawvere_theory_functor =
  A : comm_group A 
  for A :: "('a, 'b) monoid_scheme"
begin
(*Takes an abelian group A, and produces a product-preserving functor from the Lawvere theory
  of abelian groups, into the category of pointed sets.*)


type_synonym Lawv_arr = "(((nat \<Rightarrow>\<^sub>0 int) \<Rightarrow> nat \<Rightarrow>\<^sub>0 int) \<times> (nat \<Rightarrow>\<^sub>0 int) monoid \<times> (nat \<Rightarrow>\<^sub>0 int) monoid) option"
type_synonym Lawv_obj = "(nat \<Rightarrow>\<^sub>0 int)"


section "Embedding A into a larger type"

definition extend_monoid_scheme_left :: "('a, 'b) monoid_scheme \<Rightarrow> ('a + Lawv_obj, 'b + unit) monoid_scheme" where
  "extend_monoid_scheme_left B = \<lparr>carrier = Inl ` carrier B, 
         mult = (\<lambda>x y. Inl (mult B (SOME x'. x = Inl x') (SOME y'. y = Inl y'))), 
         one = Inl (one B),  \<dots> = Inl (monoid.more B)\<rparr>"

definition extend_monoid_scheme_right :: "(Lawv_obj, unit) monoid_scheme \<Rightarrow> ('a + Lawv_obj, 'b + unit) monoid_scheme" where
  "extend_monoid_scheme_right B = \<lparr>carrier = Inr ` carrier B, 
         mult = (\<lambda>x y. Inr (mult B (SOME x'. x = Inr x') (SOME y'. y = Inr y'))), 
         one = Inr (one B),  \<dots> = Inr (monoid.more B)\<rparr>"


lemma extend_comm_group_left: assumes "comm_group B"
  shows "comm_group (extend_monoid_scheme_left B)"
proof-
  interpret B : comm_group B
    using \<open>comm_group B\<close>.
  show "comm_group (extend_monoid_scheme_left B)"
    apply (rule_tac comm_groupI)
    unfolding extend_monoid_scheme_left_def
    using B.m_assoc B.m_comm
    by auto
qed

lemma extend_comm_group_left_iso: assumes "comm_group B"
  shows "group_isomorphisms B (extend_monoid_scheme_left B) Inl (\<lambda>x. (SOME x'. x = Inl x'))"
proof-
  interpret B : comm_group B
    using \<open>comm_group B\<close>.
  show "group_isomorphisms B (extend_monoid_scheme_left B) Inl (\<lambda>x. (SOME x'. x = Inl x'))"
  unfolding group_isomorphisms_def
  unfolding hom_def extend_monoid_scheme_left_def
  by auto
qed

lemma extend_comm_group_right: assumes "comm_group B"
  shows "comm_group (extend_monoid_scheme_right B)"
proof-
  interpret B : comm_group B
    using \<open>comm_group B\<close>.
  show "comm_group (extend_monoid_scheme_right B)"
    apply (rule_tac comm_groupI)
    unfolding extend_monoid_scheme_right_def
    using B.m_assoc B.m_comm
    by auto
qed

lemma extend_comm_group_right_iso: assumes "comm_group B"
  shows "group_isomorphisms B (extend_monoid_scheme_right B) Inr (\<lambda>x. (SOME x'. x = Inr x'))"
proof-
  interpret B : comm_group B
    using \<open>comm_group B\<close>.
  show "group_isomorphisms B (extend_monoid_scheme_right B) Inr (\<lambda>x. (SOME x'. x = Inr x'))"
  unfolding group_isomorphisms_def
  unfolding hom_def extend_monoid_scheme_right_def
  by auto
qed


definition A' :: "('a + Lawv_obj, 'b + unit) monoid_scheme" where
  "A' = extend_monoid_scheme_left A"

interpretation A' : comm_group A'
  unfolding A'_def
  using extend_comm_group_left [OF A.comm_group_axioms].


section "Embedding the Lawvere theory into a category of abelian groups of the desired type"

interpretation Ab : abelian_group_category.
interpretation AbCC : classical_category Ab.Obj' Ab.Arr' Ab.Dom' Ab.Cod' Ab.Id' Ab.Comp'
  using Ab.is_classical_category.


definition Inr_functor :: "Lawv_arr \<Rightarrow> ('a + Lawv_obj, 'b + unit) Ab_hom" where
  "Inr_functor = MkFunctor AbCC.comp AbCC.comp 
                 (\<lambda>f. Some ((\<lambda>a \<in> carrier (extend_monoid_scheme_right (Ab.Dom' (the f))). 
                  Inr (fst (the f) (SOME a'. a = Inr a'))) , 
                  extend_monoid_scheme_right (Ab.Dom' (the f)) , 
                  extend_monoid_scheme_right (Ab.Cod' (the f))))"

lemma Inr_functor : "functor AbCC.comp AbCC.comp Inr_functor"
  unfolding functor_def
  apply (simp add: AbCC.induces_category)
  unfolding functor_axioms_def
  apply auto
      apply (simp add: Inr_functor_def)
proof-
  show arr: "\<And>f. AbCC.arr f \<Longrightarrow> AbCC.arr (Inr_functor f)"
    apply (subst AbCC.arr_char)
    apply (subst Inr_functor_def)
    apply simp
    apply (subst Ab.Arr'_def)
    apply auto
  proof-
    fix f :: "Lawv_arr"
    assume arr_f : "AbCC.arr f"
    then have Arr'_f: "Ab.Arr' (the f)"
      unfolding AbCC.arr_char by simp
    show "Ab.Obj' (Ab.Dom' (the (Inr_functor f)))" 
      unfolding Inr_functor_def
      apply (simp add: arr_f)
      unfolding Ab.Dom'_def Ab.Obj'_def
      apply simp
      apply (rule_tac extend_comm_group_right)
      using Arr'_f
      unfolding Ab.Arr'_def Ab.Obj'_def Ab.Dom'_def
      by simp
    show "Ab.Obj' (Ab.Cod' (the (Inr_functor f)))" 
      unfolding Inr_functor_def
      apply (simp add: arr_f)
      unfolding Ab.Cod'_def Ab.Obj'_def
      apply simp
      apply (rule_tac extend_comm_group_right)
      using Arr'_f
      unfolding Ab.Arr'_def Ab.Obj'_def Ab.Cod'_def
      by simp
    show "fst (the (Inr_functor f)) \<in> extensional (carrier (Ab.Dom' (the (Inr_functor f))))"
      unfolding Inr_functor_def
      by (simp add: arr_f Ab.Dom'_def)
    have f_hom : "fst (the f) \<in> hom (Ab.Dom' (the f)) (Ab.Cod' (the f))"
      using Arr'_f unfolding Ab.Arr'_def by simp
    interpret Dom: comm_group "(fst (snd (the f)))"
      using Arr'_f
      unfolding Ab.Arr'_def Ab.Obj'_def Ab.Dom'_def
      by simp
    show "fst (the (Inr_functor f)) \<in> hom (Ab.Dom' (the (Inr_functor f))) (Ab.Cod' (the (Inr_functor f)))"
      unfolding Inr_functor_def
       apply (simp add: arr_f Ab.Dom'_def Ab.Cod'_def)
      using f_hom 
      apply (rule_tac homI)
      unfolding extend_monoid_scheme_right_def
       apply simp_all
      unfolding hom_def Ab.Dom'_def Ab.Cod'_def
      by auto
  qed
  show dom: "\<And>f. AbCC.arr f \<Longrightarrow> AbCC.dom (Inr_functor f) = Inr_functor (AbCC.dom f)"
    apply (subst AbCC.dom_char)
    apply (simp add: arr)
    unfolding Inr_functor_def 
    apply (simp add: Ab.Id'_def Ab.Dom'_def Ab.Cod'_def)
    unfolding AbCC.dom_char apply (simp add: Ab.Id'_def Ab.Dom'_def)
    unfolding extend_monoid_scheme_right_def
    apply simp
    apply (rule_tac ext)
    by auto
  show cod: "\<And>f. AbCC.arr f \<Longrightarrow> AbCC.cod (Inr_functor f) = Inr_functor (AbCC.cod f)"
    apply (subst AbCC.cod_char)
    apply (simp add: arr)
    unfolding Inr_functor_def 
    apply (simp add: Ab.Id'_def Ab.Dom'_def Ab.Cod'_def)
    unfolding AbCC.cod_char apply (simp add: Ab.Id'_def Ab.Cod'_def)
    unfolding extend_monoid_scheme_right_def
    apply simp
    apply (rule_tac ext)
    by auto
  fix g f :: "Lawv_arr"
  assume arr_gf : "AbCC.seq g f"
  interpret AbC : category Ab.comp
    using Ab.is_category.
  have arr_gf' : "AbC.seq g f"
    unfolding Ab.comp_def
    using arr_gf.
  have arr_igf : "AbCC.seq (Inr_functor g) (Inr_functor f)"
    apply (rule_tac AbC.seqE [OF arr_gf'])
    unfolding Ab.comp_def
    apply (rule_tac AbCC.seqI)
    unfolding dom cod
    by (simp_all add: arr)
  have arr_igf' : "AbC.seq (Inr_functor g) (Inr_functor f)"
    unfolding Ab.comp_def
    using arr_igf.
  show "Inr_functor (AbCC.comp g f) = AbCC.comp (Inr_functor g) (Inr_functor f)"
    apply (subst Inr_functor_def)
    apply (simp add: arr_gf)
    unfolding AbCC.comp_def
    apply (rule_tac AbC.seqE [OF arr_gf'])
    apply (rule_tac AbC.seqE [OF arr_igf'])
    unfolding Ab.comp_def
    using AbCC.seqE [OF arr_gf]
          AbCC.seqE [OF arr_igf] apply (simp add: AbCC.arr_char)
  proof-
    show "(\<lambda>a\<in>carrier (extend_monoid_scheme_right (Ab.Dom' (the f))).
        Inr (fst (Ab.Comp' (the g) (the f)) (SOME a'. a = Inr a')),
     extend_monoid_scheme_right (Ab.Dom' (the f)), extend_monoid_scheme_right (Ab.Cod' (the g))) =
    Ab.Comp' (the (Inr_functor g)) (the (Inr_functor f))"
      apply (rule_tac AbC.seqE [OF arr_gf'])
      unfolding Ab.comp_def
      unfolding Inr_functor_def apply simp
      apply (subst Ab.Comp'_def)
      apply (subst Ab.Comp'_def)
      apply (simp add: Ab.Dom'_def Ab.Cod'_def)
      unfolding extend_monoid_scheme_right_def
      apply simp
      apply (rule_tac ext)
      apply auto
      unfolding AbCC.dom_char AbCC.cod_char
      apply (simp add: Ab.Dom'_def Ab.Cod'_def Ab.Id'_def)
      unfolding AbCC.arr_char
    proof-
      fix x
      assume "f \<noteq> None \<and> Ab.Arr' (the f)"
      then have "Ab.Arr' (the f)" by simp
      then have f_mapsto: "fst (the f) \<in> carrier (fst (snd (the f))) \<rightarrow> carrier (snd (snd (the f)))"
        unfolding Ab.Arr'_def hom_def Ab.Dom'_def Ab.Cod'_def by simp
      assume "x \<in> carrier (fst (snd (the f)))"
      then have fx_in_cod: "(fst (the f) x) \<in> carrier (snd (snd (the f)))"
        using f_mapsto by auto
      assume "Inr (fst (the f) x) \<notin> Inr ` carrier (snd (snd (the f)))"
      then have "False"
        using fx_in_cod by simp
      then show "Inr (fst (the g) (fst (the f) x)) = undefined"
        by simp
    qed
  qed
qed



section "Constructing the functor" 



interpretation P : pointed_set.


definition Hom_into_A where
  "Hom_into_A f = Ab.pointed_hom_functor (f, Some (Ab.Id' A'))"

lemma Hom_into_A_functor : "functor (dual_category.comp Ab.comp) P.pointed_set_comp Hom_into_A"
  unfolding Hom_into_A_def Ab.comp_def
  apply (rule_tac binary_functor.fixing_ide_gives_functor_2 [OF Ab.pointed_hom_binary_functor])
  unfolding Ab.comp_def AbCC.ide_char apply auto
   apply (rule_tac AbCC.Arr_Id)
  unfolding Ab.Obj'_def
   apply (simp add: A'.comm_group_axioms)
  unfolding Ab.Id'_def Ab.Dom'_def by simp
  


definition map where
  "map = Hom_into_A \<circ> (dual_functor.map (Inr_functor \<circ> Ab.LawvInclusion))"

interpretation AF : "functor" "(dual_category.comp (Ab.Lawv_comp))" pointed_set.pointed_set_comp
                    map
  unfolding map_def
  apply (rule_tac functor_comp)
  apply (rule_tac dual_functor.is_functor)
  unfolding dual_functor_def
  unfolding dual_category_def
   apply (simp add: Ab.Lawv_is_category)
   apply (rule_tac conjI)
    apply (rule_tac functor_comp)
  unfolding Ab.Lawv_comp_def
  using Ab.LawvInclusion_functor apply simp
  using Inr_functor apply simp
  using AbCC.induces_category apply simp
  using Hom_into_A_functor
  unfolding Ab.comp_def.

end




end
