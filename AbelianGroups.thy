theory AbelianGroups
  imports Main
         "HOL-Algebra.Group"
         "HOL-Algebra.Free_Abelian_Groups"
         pointedSet
         "Category3.FunctorCategory"
         SomeCategoryTheory
         "Category3.Yoneda"
         "Category3.SetCategory"
         pointedSet_Factorization
         ColimitFunctoriality
         H_Ab
begin





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


(* Typeclass test
class semigroup = 
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes assoc : "mult x (mult y z) = mult (mult x y) z"

instantiation int :: semigroup
begin

definition
  mult_int_def2: "mult i j = i + (j :: int)"

instance
proof
  fix x y z :: int
  show "semigroup_class.mult x (semigroup_class.mult y z) = semigroup_class.mult (semigroup_class.mult x y) z"
    unfolding mult_int_def2 by simp
qed

end

(*Maybe the lesson here is that typeclasses in Isabelle are garbage?*)

*)


context pointed_set
begin



lemma finite_set_length_insert : 
  assumes "a \<notin> A" "A \<noteq> {}" "finite A"
  shows  "(finite_set_length (a, insert a A)) =
     Suc (finite_set_length (SOME x. x \<in> A, A))"
  apply (subst finite_set_length_def)
proof-
  define n where "n = finite_set_length (SOME x. x \<in> A, A)"
  define f where "f = finite_set_interval_bijection (SOME x. x \<in> A, A)"
  have A_snd: "A = snd (SOME x. x \<in> A, A)" by simp
  have f_bij: "bij_betw f {i. i < n} A"
    apply (subst A_snd)
    unfolding f_def n_def
    apply (rule_tac conjunct1 [OF finite_set_interval_bijection_char])
    unfolding Obj'_def
    using \<open>A \<noteq> {}\<close> some_in_eq apply auto[1]
    using \<open>finite A\<close> by simp
  have a_notin_f : "a \<notin> f ` {i. i < n}"
    using f_bij
    unfolding bij_betw_def
    using \<open>a \<notin> A\<close> by simp
  define g where "g = (\<lambda>k. if k = 0 then a else f (k -1))"
  have g_prop: "bij_betw g {i. i < Suc n} (snd (a, insert a A)) \<and>
            g 0 = fst (a, insert a A)"
    unfolding bij_betw_def
    apply auto
  proof-
    show "inj_on g {i. i < Suc n}"
      unfolding inj_on_def
      apply auto
    proof-
      fix x y
      assume "x < Suc n"
      assume "y < Suc n"
      assume "g x = g y"
      have "x = 0 \<or> x \<noteq> 0" by auto
      then show "x = y"
      proof
        assume "x = 0"
        then have "a = g y"
          using \<open>g x = g y\<close>
          unfolding g_def
          by simp
        then have "y \<noteq> 0 \<Longrightarrow> False"
        proof-
          assume "y \<noteq> 0"
          then have "a \<in> f ` {i . i < n}"
            unfolding \<open>a = g y\<close>
            unfolding g_def
            apply simp
            using \<open>y < Suc n\<close> by auto
          then show "False"
            using a_notin_f
            by simp
        qed
        then show "x = y"
          unfolding \<open>x = 0\<close> by auto
      next
        assume "x \<noteq> 0"
        then have "x - 1 < n"
          using \<open>x < Suc n\<close> by simp
        from \<open>x \<noteq> 0\<close> have "g y = f (x - 1)"
          using \<open>g x = g y\<close>
          unfolding g_def
          by simp
        have "g y \<in> f ` {i . i < n}"
          unfolding \<open>g y = f (x - 1)\<close>
          using \<open>x - 1 < n\<close> by simp
        then have "a \<noteq> g y"
          using a_notin_f 
          by auto
        then have "y \<noteq> 0"
          unfolding g_def
          by presburger
        have "x - 1 = y - 1"
          using \<open>g x = g y\<close>
          unfolding g_def
          using \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> apply simp
          using f_bij
          unfolding bij_betw_def inj_on_def
          using \<open>x - 1 < n\<close> \<open>y < Suc n\<close> by auto
        then show "x = y"
          using \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> by simp
      qed
    qed
    show "\<And>xa. g xa \<notin> A \<Longrightarrow> xa < Suc n \<Longrightarrow> g xa = a"
      unfolding g_def
      apply auto
      using f_bij
      unfolding bij_betw_def
      by auto
    show "g 0 = a"
      unfolding g_def by simp
    show "a \<in> g ` {i. i < Suc n}"
      unfolding reverse_equality [OF \<open>g 0 = a\<close>] by simp
    show "\<And>x. x \<in> A \<Longrightarrow> x \<in> g ` {i. i < Suc n}"
    proof-
      fix x
      assume "x \<in> A"
      then have "x \<in> f ` {i. i < n}"
        using f_bij
        unfolding bij_betw_def by simp
      then obtain y where y_def : "x = f y \<and> y < n" by blast
      have "x = g (Suc y) \<and> Suc y < Suc n"
        unfolding conjunct1 [OF y_def]
        unfolding g_def by (simp add: y_def)
      then show "x \<in> g ` {i. i < Suc n}"
        by simp
    qed
  qed
  show "(SOME n.
        \<exists>f. bij_betw f {i. i < n} (snd (a, insert a A)) \<and>
            f 0 = fst (a, insert a A)) =
    Suc (finite_set_length (SOME x. x \<in> A, A))"
      unfolding reverse_equality [OF n_def]
  proof
    show "\<exists>f. bij_betw f {i. i < Suc n}
         (snd (a, insert a A)) \<and>
        f 0 = fst (a, insert a A)"
      apply (rule_tac exI)
      using g_prop.
    fix m :: nat
    assume "\<exists>f. bij_betw f {i. i < m} (snd (a, insert a A)) \<and>
              f 0 = fst (a, insert a A)"
    then obtain h where h_def: "bij_betw h {i. i < m} (snd (a, insert a A)) \<and>
              h 0 = fst (a, insert a A)" by blast
    then obtain i where i_def : "bij_betw i (snd (a, insert a A)) {i. i < m}"
      using bij_betw_inv by blast
    have "bij_betw (i \<circ> g) {i. i < Suc n} {i . i < m}"
      apply (rule_tac bij_betw_trans)
      using g_prop apply blast
      using i_def.
    then have "card {i. i < Suc n} = card {i . i < m}"
      using bij_betw_same_card by blast
    then show "m = Suc n"
      by simp
  qed
qed

end



context comm_group
begin


definition finset_sum where
  "finset_sum S f = sum (fmap f (pointed_set.finite_set_to_list ((SOME x. x \<in> S), S)))"


lemma permutation_pushforward:
  "bij_betw f {i::nat . i < length xs} {i :: nat . i < length xs} \<Longrightarrow>
   \<forall>k < length xs. get xs k \<in> carrier G \<Longrightarrow>
   push_forward (length xs, (rev_get (length xs) (\<lambda>k. (SOME m. k = f m \<and> m < length xs)))) xs = rev_get (length xs) 
         (\<lambda>k. get xs (f k))"
  unfolding push_forward_def
  apply (rule_tac getFaithful)
   apply simp
  apply simp
proof-
  fix n
  assume f_bij : "bij_betw f {i. i < length xs} {i. i < length xs}"
  assume xs_in_G : "\<forall>k < length xs. get xs k \<in> carrier G"
  assume "n < length xs"
  then have "f n < length xs"
    using f_bij
    unfolding bij_betw_def by auto

  have f_some_inv:  "\<And>k. k < length xs \<Longrightarrow>
         k = f (SOME m. k = f m \<and> m < length xs)"
  proof-
    fix k
    assume "k < length xs"
    then have "k \<in> f ` {i . i < length xs}"
      using f_bij
      unfolding bij_betw_def
      by auto
    then obtain m where m_def : "k = f m \<and> m < length xs" 
      by blast
    have "(SOME m. k = f m \<and> m < length xs) = m"
    proof
      show "k = f m \<and> m < length xs" 
        using m_def.
      show "\<And>ma. k = f ma \<and> ma < length xs \<Longrightarrow> ma = m"
        using f_bij
        unfolding bij_betw_def inj_on_def
        using m_def by auto
    qed
    then show "k = f (SOME m. k = f m \<and> m < length xs)"
      unfolding conjunct1 [OF m_def] by simp
  qed
  show "local.sum (merge_with_zeros xs
            (\<lambda>i. get (rev_get (length xs) (\<lambda>k. SOME m. k = f m \<and> m < length xs))
             i = n)) = get xs (f n)"
    apply (subst one_sum)
     apply auto
    using \<open>f n < length xs\<close> apply simp
    unfolding merge_with_zeros_def
      apply auto
    using f_some_inv apply simp
    using \<open>f n < length xs\<close> apply simp
    using xs_in_G apply simp
    using \<open>f n < length xs\<close> apply auto
  proof-
    assume not_eq: "(SOME m. f n = f m \<and> m < length xs) \<noteq> n"
    have eq: "(SOME m. f n = f m \<and> m < length xs) = n"
    proof
      show "f n = f n \<and> n < length xs"
        using \<open>n < length xs\<close> by simp
      show "\<And>m. f n = f m \<and> m < length xs \<Longrightarrow> m = n"
        using \<open>n < length xs\<close>
        using f_bij
        unfolding bij_betw_def inj_on_def
        by auto
    qed
    show "\<one> = get xs (f n)"
      using eq not_eq by simp
  qed
qed

lemma sum_permutation_invariant :
   "bij_betw f {i::nat . i < (length xs)} {i :: nat . i < (length xs)} \<Longrightarrow>
    \<forall>k<length xs. get xs k \<in> carrier G \<Longrightarrow>
        sum xs = sum (rev_get (length xs) (\<lambda>k. get xs (f k)))"
  unfolding reverse_equality [OF permutation_pushforward]
  apply (subst push_forward_sum)
     apply auto
  unfolding fin_set.Arr'_def
  apply auto
proof-
  fix n
  assume f_bij: "bij_betw f {i. i < length xs} {i. i < length xs}"
  assume "n < length xs"
  then have "n \<in> f ` {i . i < length xs}"
    using f_bij
    unfolding bij_betw_def by auto
  then obtain m where m_def: "n = f m \<and> m < length xs" by blast
  have "(SOME m. n = f m \<and> m < length xs) = m"
  proof
    show "n = f m \<and> m < length xs"
      using m_def.
    show "\<And>ma. n = f ma \<and> ma < length xs \<Longrightarrow> ma = m"
      using f_bij
      unfolding bij_betw_def inj_on_def
      using m_def by auto
  qed
  then show "(SOME m. n = f m \<and> m < length xs) < length xs"
    by (simp add: m_def)
qed

lemma finset_sum_empty :
  "finset_sum {} f = \<one>"
proof-
  have n_some: "(SOME (n :: nat). \<exists>f. bij_betw f {i. i < n} {} \<and> f 0 = (SOME x. False)) = 0"
  proof
    show "\<exists> f. bij_betw f {i. i < (0 :: nat)} {} \<and> f 0 = (SOME x. False)"
      apply (rule_tac exI)
    proof-
      show "bij_betw (\<lambda>k. (SOME x. False)) {i. i < (0 :: nat)} {} \<and> 
            (\<lambda>k. (SOME x. False)) 0 = (SOME x. False)"
        unfolding bij_betw_def by auto
    qed
    fix n :: nat
    show "\<exists>f. bij_betw f {i. i < n} {} \<and> f 0 = (SOME x. False) \<Longrightarrow> n = 0"
      unfolding bij_betw_def
      by auto
  qed
  show "finset_sum {} f = \<one>"
    unfolding finset_sum_def
    unfolding pointed_set.finite_set_to_list.simps
    unfolding pointed_set.finite_set_length_def
    apply simp
    unfolding n_some
    by simp
qed

lemma finset_sum_insert :
  assumes "a \<notin> A" "A \<noteq> {}" "finite A"
  and "f a \<in> carrier G"
  and "finset_sum A f \<in> carrier G"
shows "finset_sum (insert a A) f = (f a) \<otimes> (finset_sum A f)"
proof-
  define n where n_def : "n = (pointed_set.finite_set_length (SOME x. x \<in> A, A))"
  have length_eq: "(pointed_set.finite_set_length (a, insert a A)) =
        Suc n"
    unfolding n_def
    apply (rule_tac pointed_set.finite_set_length_insert)
    using assms by simp_all

  have obj_aA: "pointed_set.Obj' (a, insert a A)"
    unfolding pointed_set.Obj'_def by simp
  define g where "g = pointed_set.finite_set_interval_bijection (a, insert a A)"
  have g_bij : "bij_betw g {i. i < Suc n} (insert a A) \<and> g 0 = a"
    unfolding g_def reverse_equality [OF length_eq]
    using pointed_set.finite_set_interval_bijection_char [OF obj_aA]
    using \<open>finite A\<close> by simp
  define h where "h = (\<lambda>k. g (Suc k))"
  have h_bij : "bij_betw h {i. i < n} A"
    using g_bij
    unfolding h_def bij_betw_def inj_on_def
    apply auto
  proof-
    fix x
    assume "x \<in> A"
    then have "x \<in> insert (g 0) A" by simp
    assume "g ` {i. i < Suc n} = insert (g 0) A"
    from this and \<open>x \<in> insert (g 0) A\<close> 
    have "x \<in> g ` {i. i < Suc n}" by simp
    then obtain i where i_def : "i < Suc n \<and> g i = x"
      by blast
    have "i \<noteq> 0"
    proof
      assume "i = 0"
      have "x = a"
        using i_def
        unfolding \<open>i = 0\<close>
        using g_bij by simp
      then show "False"
        using \<open>x \<in> A\<close> \<open>a \<notin> A\<close> by simp
    qed
    then have "g (Suc (i -1)) = x \<and> i - 1 < n"
      using i_def by auto
    then show "x \<in> (\<lambda>k. g (Suc k)) ` {i. i < n}"
      by auto
  qed
  have obj_A: "pointed_set.Obj' (SOME x. x \<in> A, A)"
    unfolding pointed_set.Obj'_def
    using \<open>A \<noteq> {}\<close>
    by (simp add: some_in_eq)
  define \<alpha> where "\<alpha> = pointed_set.finite_set_interval_bijection (SOME x. x \<in> A, A)"
  have bij_\<alpha> : "bij_betw \<alpha> {i . i < n} A"
    unfolding \<alpha>_def n_def
    using pointed_set.finite_set_interval_bijection_char [OF obj_A]
    using \<open>finite A\<close> by simp
  (*TODO: Compose an inverse of \<alpha> with h, and prove that it is the desired permutation below.*)
      
  have "local.sum
     (fmap f (pointed_set.finite_set_to_list (a, insert a A))) =
    f a \<otimes> finset_sum A f"
    unfolding finset_sum_def
    unfolding pointed_set.finite_set_to_list.simps
    unfolding length_eq
    apply simp
    apply (subst conjunct2 [OF pointed_set.finite_set_interval_bijection_char])
    unfolding pointed_set.Obj'_def apply simp
    using \<open>finite A\<close> apply simp
    apply simp
    unfolding reverse_equality [OF n_def]
    apply (subst sum_permutation_invariant)
      apply simp_all
    
    








lemma finset_sum_carrier :
  assumes "finite S"
shows "(\<forall>x \<in> S. f x \<in> carrier G) \<longrightarrow> finset_sum S f \<in> carrier G"
  apply (rule_tac finite.induct [OF \<open>finite S\<close>])
  apply auto
proof-
  show "finset_sum {} f \<in> carrier G"
    unfolding finset_sum_empty
    by simp

  fix A a
  assume "finset_sum A f \<in> carrier G"
  assume "finite A"
  show "finset_sum (insert a A) f \<in> carrier G"
    
      



end


locale coproduct_of_A_functor =
  A : comm_group A
  for A :: "('a , 'b) monoid_scheme"
begin






definition coproduct_carrier :: "'s set \<Rightarrow> ('s \<Rightarrow> 'a) set" where
  "coproduct_carrier S = {c. c \<in> extensional S \<and> c \<in> S \<rightarrow> carrier A \<and> finite {x \<in> S. c x \<noteq> one A}}"

definition coproduct_of_A :: "'s set \<Rightarrow> ('s \<Rightarrow> 'a, 'b) monoid_scheme" where
  "coproduct_of_A S = \<lparr>carrier = coproduct_carrier S, 
                       mult = (\<lambda>a b. (\<lambda>s \<in> S. mult A (a s) (b s))),
                       one = (\<lambda>s \<in> S. one A),
                       \<dots> = monoid.more A\<rparr>"




lemma coproduct_comm_group : "comm_group (coproduct_of_A S)"
  apply (rule_tac comm_groupI)
  unfolding coproduct_of_A_def
       apply simp_all
proof-
  show "\<And>x y. x \<in> coproduct_carrier S \<Longrightarrow>
           y \<in> coproduct_carrier S \<Longrightarrow>
           (\<lambda>s\<in>S. x s \<otimes>\<^bsub>A\<^esub> y s) \<in> coproduct_carrier S"
    unfolding coproduct_carrier_def
    apply auto
  proof-
    fix x y
    assume x_fin: "finite {a \<in> S. x a \<noteq> \<one>\<^bsub>A\<^esub>}"
    assume y_fin: "finite {a \<in> S. y a \<noteq> \<one>\<^bsub>A\<^esub>}"
    have xy_fin: "finite ({a \<in> S. x a \<noteq> \<one>\<^bsub>A\<^esub>} \<union> {a \<in> S. y a \<noteq> \<one>\<^bsub>A\<^esub>})"
      using x_fin y_fin by auto
    show "finite {a.(a \<in> S \<longrightarrow> 
          x a \<otimes>\<^bsub>A\<^esub> y a \<noteq> \<one>\<^bsub>A\<^esub>) \<and> a \<in> S}"
      apply (rule_tac rev_finite_subset)
      using xy_fin apply blast
      by auto
  qed
  show "(\<lambda>s\<in>S. \<one>\<^bsub>A\<^esub>) \<in> coproduct_carrier S"
    unfolding coproduct_carrier_def
    by auto
  show "\<And>x y z.
       x \<in> coproduct_carrier S \<Longrightarrow>
       y \<in> coproduct_carrier S \<Longrightarrow>
       z \<in> coproduct_carrier S \<Longrightarrow>
       (\<lambda>s\<in>S. (if s \<in> S then x s \<otimes>\<^bsub>A\<^esub> y s
                else undefined) \<otimes>\<^bsub>A\<^esub> z s) =
       (\<lambda>s\<in>S. x s \<otimes>\<^bsub>A\<^esub> (if s \<in> S then y s \<otimes>\<^bsub>A\<^esub> z s
                else undefined))"
    apply (rule_tac ext)
    apply auto
    apply (rule_tac A.m_assoc)
    unfolding coproduct_carrier_def
    by auto
  show "\<And>x y. x \<in> coproduct_carrier S \<Longrightarrow>
           y \<in> coproduct_carrier S \<Longrightarrow>
           (\<lambda>s\<in>S. x s \<otimes>\<^bsub>A\<^esub> y s) = (\<lambda>s\<in>S. y s \<otimes>\<^bsub>A\<^esub> x s)"
    apply (rule_tac ext)
    apply auto
    apply (rule_tac A.m_comm)
    unfolding coproduct_carrier_def
    by auto
  show "\<And>x. x \<in> coproduct_carrier S \<Longrightarrow>
         (\<lambda>s\<in>S. (if s \<in> S then \<one>\<^bsub>A\<^esub>
                  else undefined) \<otimes>\<^bsub>A\<^esub>
                 x s) = x"
    apply (rule_tac ext)
    unfolding coproduct_carrier_def
    apply auto
     apply (rule_tac A.l_one)
    unfolding extensional_def by auto
  fix x
  assume x_in: "x \<in> coproduct_carrier S"
  define y where "y = (\<lambda>s \<in> S. inv\<^bsub>A\<^esub> (x s))"

  show "\<exists>y\<in>coproduct_carrier S.
            (\<lambda>s\<in>S. y s \<otimes>\<^bsub>A\<^esub> x s) = (\<lambda>s\<in>S. \<one>\<^bsub>A\<^esub>)"
  proof
    show "y \<in> coproduct_carrier S"
      using x_in
      unfolding coproduct_carrier_def y_def
      apply auto
    proof-
      assume fin: "finite {xa \<in> S. x xa \<noteq> \<one>\<^bsub>A\<^esub>}"
      show "finite
     {xa. (xa \<in> S \<longrightarrow> inv\<^bsub>A\<^esub> x xa \<noteq> \<one>\<^bsub>A\<^esub>) \<and> xa \<in> S}"
        apply (rule_tac rev_finite_subset)
        using fin apply blast
        by auto
    qed
    show "(\<lambda>s\<in>S. y s \<otimes>\<^bsub>A\<^esub> x s) = (\<lambda>s\<in>S. \<one>\<^bsub>A\<^esub>)"
      apply (rule_tac ext)
      unfolding y_def
      apply auto
      apply (rule_tac A.l_inv)
      using x_in 
      unfolding coproduct_carrier_def
      by auto
  qed
qed




      


interpretation Ab : abelian_group_category.
interpretation AbCC : classical_category Ab.Obj' Ab.Arr' Ab.Dom' Ab.Cod' Ab.Id' Ab.Comp'
  using Ab.is_classical_category.
interpretation S: set_category SetCat.comp
  using SetCat.is_set_category.


definition obj where
  "obj = Some (Ab.Id' (coproduct_of_A {(SOME y. True)}))"

definition A_to_obj where
  "A_to_obj a = (\<lambda>s \<in> {(SOME y. True)}. a)"


lemma A_to_obj_in_hom: "A_to_obj \<in> hom A (coproduct_of_A {(SOME y. True)})"
  unfolding A_to_obj_def hom_def coproduct_of_A_def
  unfolding coproduct_carrier_def
  by auto



definition coproduct_inclusion :: "'s set \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 'a, 'b) Ab_hom" where
  "coproduct_inclusion S s = Some ((\<lambda>x \<in> coproduct_carrier {(SOME y. True)}.
             (\<lambda>t \<in> S. (if t = s then x (SOME y. True) else \<one>\<^bsub>A\<^esub>))),
             (coproduct_of_A {(SOME y. True)},
             (coproduct_of_A S)))"




lemma coproduct_inclusion_in_hom : 
    "AbCC.in_hom (coproduct_inclusion S s) obj 
     (Some (Ab.Id' (coproduct_of_A S)))"
  apply (rule_tac AbCC.in_homI)
proof-
  show arr: "AbCC.arr (coproduct_inclusion S s)"
    unfolding AbCC.arr_char coproduct_inclusion_def
    apply simp
    unfolding Ab.Arr'_def
    apply (simp add: Ab.Dom'_def Ab.Cod'_def Ab.Obj'_def coproduct_comm_group)
    unfolding coproduct_of_A_def
    apply simp
    unfolding hom_def apply auto
    unfolding coproduct_carrier_def
    by auto
  show "AbCC.dom (coproduct_inclusion S s) = obj"
    unfolding AbCC.dom_char
    apply (simp add: arr)
    unfolding obj_def coproduct_inclusion_def
    by (simp add: Ab.Dom'_def)
  show "AbCC.cod (coproduct_inclusion S s) = Some (Ab.Id' (coproduct_of_A S))"
    unfolding AbCC.cod_char
    apply (simp add: arr)
    unfolding coproduct_inclusion_def
    by (simp add: Ab.Cod'_def)
qed


definition coproduct_UP_map where
  "coproduct_UP_map c X \<sigma> = Some ((\<lambda>x \<in> coproduct_carrier (S.set c). 
      comm_group.finset_sum (Ab.Dom' (the X)) 
      {s \<in> (S.set c). x s \<noteq> one A}
      (\<lambda>s \<in> (S.set c). fst (the (\<sigma> (discrete_category.mkIde (S.set c) s))) 
        (A_to_obj (x s)))), 
       (coproduct_of_A (S.set c),  Ab.Dom' (the X)))"



interpretation Cocone: coproduct_cocone Ab.comp obj
  unfolding coproduct_cocone_def
  apply (simp add: Ab.is_category)
  unfolding coproduct_cocone_axioms_def
  unfolding Ab.comp_def
  unfolding obj_def
  apply (rule_tac classical_category.ide_Some_Id [OF Ab.is_classical_category])
  unfolding Ab.Obj'_def
  using coproduct_comm_group by blast

interpretation \<tau> : functor_to_cat_overX SetCat.comp Ab.comp 
   "(\<lambda>S. discrete_category.comp (S.set S))"
   Cocone.discrete_functor Cocone.cocone
  using Cocone.const_functor_overX.

term "coproduct_of_A (S.set (c :: ((((nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a) \<times>
    (nat \<Rightarrow> 'a, 'b) monoid_scheme \<times>
    (nat \<Rightarrow> 'a, 'b) monoid_scheme) option SetCat.arr)))"



definition coproduct_inc_nattrafo where
  "coproduct_inc_nattrafo c = MkFunctor (discrete_category.comp (S.set c)) Ab.comp
                 (\<lambda>d. coproduct_inclusion (S.set c) (discrete_category.toObj d))"


lemma "colimit_functoriality 
       SetCat.comp 
       Ab.comp
       (\<lambda>S. discrete_category.comp (S.set S))
       Cocone.discrete_functor 
       Cocone.cocone
       (\<lambda>c. Some (Ab.Id' (coproduct_of_A (S.set c))))
       coproduct_inc_nattrafo
       coproduct_UP_map"
  unfolding colimit_functoriality_def
  apply (simp add: \<tau>.functor_to_cat_overX_axioms)
  unfolding colimit_functoriality_axioms_def
  apply auto
proof-
  fix c
  assume ide_c: "S.ide c"
  then have arr_c : "S.arr c" by simp

  interpret DC : discrete_category "S.set c"
    using Cocone.is_discrete_category.
  interpret AbC : category Ab.comp
    using Ab.is_category.
  interpret F : "functor" DC.comp Ab.comp "(Cocone.cocone c)"
    using \<tau>.\<tau>fun [OF ide_c].

  show "colimit (discrete_category.comp (S.set c)) Ab.comp (Cocone.cocone c)
          (coproduct_inc_nattrafo c) (Some (Ab.Id' (coproduct_of_A (S.set c))))
          (coproduct_UP_map c)"
    unfolding colimit_def
    apply (simp add: AbC.category_axioms DC.category_axioms F.functor_axioms)
  proof
    interpret Const : constant_functor 
     "(discrete_category.comp (S.set c))" Ab.comp
     "(Some (Ab.Id' (coproduct_of_A (S.set c))))"
      unfolding constant_functor_def
      apply (simp add: DC.category_axioms AbC.category_axioms)
      unfolding constant_functor_axioms_def
      unfolding Ab.comp_def
      unfolding AbCC.ide_char
      apply auto
       apply (rule_tac AbCC.Arr_Id)
      unfolding Ab.Obj'_def
      using coproduct_comm_group apply blast
      by (simp add: Ab.Dom'_def Ab.Id'_def)

    have ide_cop : "AbCC.ide (Some (Ab.Id' (coproduct_of_A (S.set c))))"
      apply (rule_tac AbCC.ide_Some_Id)
      unfolding Ab.Obj'_def
      using coproduct_comm_group by blast
    show nat: "natural_transformation DC.comp Ab.comp (Cocone.cocone c) Const.map
     (coproduct_inc_nattrafo c)"
      unfolding natural_transformation_def
      apply (simp add: AbC.category_axioms DC.category_axioms 
                       F.functor_axioms Const.is_functor)
      unfolding natural_transformation_axioms_def
      apply auto
    proof-
      show "\<And>f. \<not> DC.arr f \<Longrightarrow> coproduct_inc_nattrafo c f = AbC.null"
        unfolding coproduct_inc_nattrafo_def
        by simp
      have hom_implies_arr: "\<And>x y z. AbCC.in_hom x y z \<Longrightarrow> AbCC.arr x" by blast
      have arr : "\<And>f. DC.arr f \<Longrightarrow> AbCC.arr (coproduct_inc_nattrafo c f)"
        unfolding coproduct_inc_nattrafo_def
        apply simp
        using hom_implies_arr [OF coproduct_inclusion_in_hom].
      interpret Constf : constant_functor DC.comp AbCC.comp obj
        unfolding constant_functor_def
        unfolding constant_functor_axioms_def
         apply (simp add: DC.category_axioms AbCC.induces_category)
        using Cocone.ide_obj
        unfolding Ab.comp_def by simp
      show dom: "\<And>f. DC.arr f \<Longrightarrow> AbC.dom (coproduct_inc_nattrafo c f) = Cocone.cocone c f"
        unfolding Ab.comp_def
        unfolding AbCC.dom_char
        apply (simp add: arr)
        apply (subst coproduct_cocone.cocone_def)
        unfolding coproduct_cocone_def
        unfolding coproduct_cocone_axioms_def
         apply (simp add: AbCC.induces_category)
        using Cocone.ide_obj
        unfolding Ab.comp_def
         apply simp
        unfolding S.ideD(2) [OF ide_c]
        apply (subst Constf.map_def)
        unfolding coproduct_inc_nattrafo_def
        apply simp
        unfolding coproduct_inclusion_def
        apply (simp add: Ab.Dom'_def)
        unfolding obj_def
        by simp
      show cod: "\<And>f. DC.arr f \<Longrightarrow>
         AbC.cod (coproduct_inc_nattrafo c f) =
         Some (Ab.Id' (coproduct_of_A (S.set c)))"
        unfolding Ab.comp_def
        unfolding AbCC.cod_char
        apply (simp add: arr)
        unfolding coproduct_inc_nattrafo_def
        apply simp
        unfolding coproduct_inclusion_def
        by (simp add: Ab.Cod'_def)

      show "\<And>f. DC.arr f \<Longrightarrow>
         Ab.comp (Some (Ab.Id' (coproduct_of_A (S.set c))))
          (coproduct_inc_nattrafo c f) =
         coproduct_inc_nattrafo c f"
        apply (rule_tac AbC.comp_ide_arr)
        unfolding Ab.comp_def
        apply (simp add: ide_cop)
        apply (rule_tac AbCC.seqI)
        using arr apply simp
         apply (simp add: ide_cop)
        unfolding reverse_equality [OF Ab.comp_def]
        unfolding cod
        apply (rule_tac AbC.ideD(2))
        unfolding Ab.comp_def
        using ide_cop.
      show "\<And>f. DC.arr f \<Longrightarrow>
         Ab.comp (coproduct_inc_nattrafo c f) (Cocone.cocone c f) =
         coproduct_inc_nattrafo c f"
        apply (rule_tac AbC.comp_arr_ide)
        unfolding Cocone.cocone_def
        unfolding S.ideD(2) [OF ide_c]
        unfolding Ab.comp_def
        unfolding Constf.map_def
         apply simp
        using Cocone.ide_obj
        unfolding Ab.comp_def apply simp
        apply simp
        apply (rule_tac AbCC.seqI)
          apply (rule_tac AbCC.ideD(1))
        unfolding reverse_equality [OF Ab.comp_def]
        using Cocone.ide_obj apply simp
        using arr apply (simp add: Ab.comp_def)
        unfolding dom
        unfolding Cocone.cocone_def
        unfolding S.ideD(2) [OF ide_c]
        unfolding Ab.comp_def
        unfolding Constf.map_def
        apply simp
        apply (subst AbCC.ideD(3))
        using Cocone.ide_obj
        unfolding Ab.comp_def
        by simp_all
    qed
    show "colimit_axioms DC.comp Ab.comp (Cocone.cocone c) (coproduct_inc_nattrafo c)
     (Some (Ab.Id' (coproduct_of_A (S.set c)))) (coproduct_UP_map c)"
      unfolding colimit_axioms_def
      apply auto
    proof-
      show "AbC.ide (Some (Ab.Id' (coproduct_of_A (S.set c))))"
        using ide_cop
        unfolding Ab.comp_def.
      show "cocone DC.comp Ab.comp (Cocone.cocone c)
     (Some (Ab.Id' (coproduct_of_A (S.set c)))) (coproduct_inc_nattrafo c)"
        unfolding cocone_def
        using nat.
      show UP_in_hom: "\<And>\<sigma> x. cocone DC.comp Ab.comp (Cocone.cocone c) x \<sigma> \<Longrightarrow>
           AbC.ide x \<Longrightarrow>
           AbC.in_hom (coproduct_UP_map c x \<sigma>)
            (Some (Ab.Id' (coproduct_of_A (S.set c)))) x"
        apply (rule_tac AbC.in_homI)
      proof-
        fix \<sigma> :: "'d SetCat.arr DC.arr \<Rightarrow> ('d SetCat.arr \<Rightarrow> 'a, 'b) Ab_hom" 
        fix x :: "('d SetCat.arr \<Rightarrow> 'a, 'b) Ab_hom"
        assume "cocone DC.comp Ab.comp (Cocone.cocone c) x \<sigma>"
        then interpret \<sigma>: natural_transformation DC.comp Ab.comp 
          "(Cocone.cocone c)" "(constant_functor.map DC.comp Ab.comp x)" \<sigma>
          unfolding cocone_def.
        assume ide_x : "AbC.ide x"
        then interpret X : comm_group "Ab.Dom' (the x)"
          unfolding Ab.comp_def
          unfolding AbCC.ide_char
          unfolding Ab.Arr'_def
          unfolding Ab.Obj'_def
          by simp
        show "AbC.arr (coproduct_UP_map c x \<sigma>)"
          unfolding Ab.comp_def
          unfolding AbCC.arr_char
          apply (subst coproduct_UP_map_def)
          apply simp
          unfolding Ab.Arr'_def
          unfolding Ab.Obj'_def Ab.Dom'_def Ab.Cod'_def
          unfolding coproduct_UP_map_def
          apply auto
          using coproduct_comm_group apply blast
          using X.comm_group_axioms apply simp
          unfolding coproduct_of_A_def apply simp
          unfolding hom_def apply auto
          unfolding X.finset_sum_def
          apply (rule_tac X.sum_carrier)








(*TODO: Define a colimit_functor, that sends a set S to the direct sum of S copies of A*)

end



locale functor_restricts_to_Ab =
  A_set : functor_category A pointed_set.pointed_set_comp +
  B_set : functor_category B pointed_set.pointed_set_comp +
  F : "functor" A_set.comp B_set.comp F
  for A :: "'a comp"
  and B :: "'b comp"
  and F +
assumes F_preserves_binary_products : "\<And>a b p p1 p2 up.
      binary_product A_set.comp a b p p1 p2 up \<Longrightarrow>
\<exists>Fup. binary_product B_set.comp (F a) (F b) (F p) (F p1) (F p2) Fup"
  and F_preserves_terminal_object : "\<And>a.
       A_set.terminal a \<Longrightarrow> B_set.terminal (F a)"
begin

(*TODO: Construct a functor from A_Ab to B_Ab*)
(*Later use this locale to restrict pi0 and \<Omega> to abelian groups.*)

end


end
