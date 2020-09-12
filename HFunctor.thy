theory HFunctor
  imports Main
         "HOL-Algebra.Group"
         AbelianGroups
         Gamma
         "HOL-Library.Poly_Mapping"
begin





section "Abelian Groups to Gammaset"

locale group_to_gammaset =
  A: comm_group A
  for A:: "('a,'b) monoid_scheme"
begin


interpretation Ab : abelian_group_category.
interpretation AbCC : classical_category Ab.Obj' Ab.Arr' Ab.Dom' Ab.Cod' Ab.Id' Ab.Comp'
  using Ab.is_classical_category.

interpretation T: group_to_Lawvere_theory_functor A
  unfolding group_to_Lawvere_theory_functor_def
  using A.comm_group_axioms.


lift_definition HFunctorHat_on_arr :: "(nat \<times> nat list) option \<Rightarrow> (nat \<Rightarrow>\<^sub>0 int) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 int)" is
  "\<lambda>f g x. if 0 < x \<and> x < fin_set.Dom' (the f) then g (get (snd (the f)) x) else 0"
proof-
  fix f :: "(nat \<times> nat list) option"
  fix g :: "(nat \<Rightarrow> int)"
  assume "finite {y. g y \<noteq> 0}"
  show "finite {x. (if 0 < x \<and> x < length (snd (the f)) then g (get (snd (the f)) x) else 0) \<noteq> 0}"
    by simp
qed


definition HFunctorHat :: "(nat \<times> nat list) option \<Rightarrow> T.Lawv_arr" where
  "HFunctorHat = MkFunctor pointed_fin_set.comp (dual_category.comp (Ab.Lawv_comp))
               (\<lambda>f. Ab.MkArr (free_Abelian_group {i. 0 < i \<and> i < fin_set.Cod' (the f)}) 
                             (free_Abelian_group {i. 0 < i \<and> i < fin_set.Dom' (the f)}) 
                             (HFunctorHat_on_arr f))"

lemma HFunctorHat : "functor pointed_fin_set.comp (dual_category.comp (Ab.Lawv_comp)) HFunctorHat"
  unfolding functor_def
  apply (simp add: pointed_fin_set.is_category)
  apply auto
   apply (rule_tac dual_category.is_category)
  unfolding dual_category_def
   apply (simp add: Ab.Lawv_is_category)
  unfolding functor_axioms_def
  apply auto
proof-
  interpret PFT : category pointed_fin_set.comp
    using pointed_fin_set.is_category.
  interpret DL : dual_category "Ab.Lawv_comp"
    by (simp add: Ab.Lawv_is_category dual_category_def)
  show "\<And>f. \<not> PFT.arr f \<Longrightarrow> HFunctorHat f = DL.null"
    unfolding HFunctorHat_def by simp
  show arr: "\<And>f. PFT.arr f \<Longrightarrow> DL.arr (HFunctorHat f)"
    unfolding DL.arr_char
    unfolding Ab.Lawv_comp_def
    apply (subst classical_category.arr_char)
    using Ab.Lawv_is_classical_category apply simp
    unfolding HFunctorHat_def Ab.MkArr_def
    apply simp
    unfolding classical_full_subcategory.SArr_def 
          [OF Ab.Lawv_is_classical_full_subcategory]
    unfolding Ab.is_Z_tothe_n_def Ab.Dom'_def Ab.Cod'_def
    apply simp
    apply safe
  proof-
    fix f
    assume arr_f : "PFT.arr f"
    define S1 where "S1 = {i. 0 < i \<and> i < fst (the f)}"
    have "finite S1 \<and> free_Abelian_group S1 = free_Abelian_group {i. 0 < i \<and> i < fst (the f)}"
      unfolding S1_def by simp
    then show "\<exists>S. finite S \<and> free_Abelian_group S = free_Abelian_group {i. 0 < i \<and> i < fst (the f)}"
      apply (rule_tac exI)
      by simp
    define S2 where "S2 = {i. 0 < i \<and> i < length (snd (the f))}"
    have "finite S2 \<and> free_Abelian_group S2 = free_Abelian_group {i. 0 < i \<and> i < length (snd (the f))}"
      unfolding S2_def by simp
    then show "\<exists>S. finite S \<and> free_Abelian_group S = free_Abelian_group {i. 0 < i \<and> i < length (snd (the f))}"
      apply (rule_tac exI)
      by simp

    show "Ab.Arr'
          (restrict (HFunctorHat_on_arr f) (carrier (free_Abelian_group {i. 0 < i \<and> i < fst (the f)})),
           free_Abelian_group {i. 0 < i \<and> i < fst (the f)}, free_Abelian_group {i. 0 < i \<and> i < length (snd (the f))})"
      apply (simp add: Ab.Arr'_def Ab.Obj'_def Ab.Dom'_def Ab.Cod'_def)
      apply (simp add: abelian_free_Abelian_group)
      apply (simp add: hom_def free_Abelian_group_def)
      apply (simp add: HFunctorHat_on_arr_def Poly_Mapping.keys_def)
      apply auto
        apply (rule_tac poly_mapping_eqI)
      unfolding lookup_add
        apply simp
    proof-
      fix x y :: "nat \<Rightarrow>\<^sub>0 int"
      fix xa
      assume "poly_mapping.lookup x xa + poly_mapping.lookup y xa \<noteq> 0"
      then have "poly_mapping.lookup x xa \<noteq> 0 \<or> poly_mapping.lookup y xa \<noteq> 0"
        by simp
      then have T: "{k. poly_mapping.lookup x k \<noteq> 0} \<subseteq> {i. 0 < i \<and> i < fst (the f)} \<Longrightarrow>
       {k. poly_mapping.lookup y k \<noteq> 0} \<subseteq> {i. 0 < i \<and> i < fst (the f)} \<Longrightarrow> 0 < xa \<and> xa < fst (the f)"
      proof
        show "{k. poly_mapping.lookup x k \<noteq> 0} \<subseteq> {i. 0 < i \<and> i < fst (the f)} \<Longrightarrow>
              poly_mapping.lookup x xa \<noteq> 0 \<Longrightarrow> 0 < xa \<and> xa < fst (the f) "
          by auto
        show "{k. poly_mapping.lookup y k \<noteq> 0} \<subseteq> {i. 0 < i \<and> i < fst (the f)} \<Longrightarrow> 
              poly_mapping.lookup y xa \<noteq> 0 \<Longrightarrow> 0 < xa \<and> xa < fst (the f) "
          by auto
      qed
      then show "{k. poly_mapping.lookup x k \<noteq> 0} \<subseteq> {i. 0 < i \<and> i < fst (the f)} \<Longrightarrow>
       {k. poly_mapping.lookup y k \<noteq> 0} \<subseteq> {i. 0 < i \<and> i < fst (the f)} \<Longrightarrow> 0 < xa"
        by simp
      from T show "{k. poly_mapping.lookup x k \<noteq> 0} \<subseteq> {i. 0 < i \<and> i < fst (the f)} \<Longrightarrow>
       {k. poly_mapping.lookup y k \<noteq> 0} \<subseteq> {i. 0 < i \<and> i < fst (the f)} \<Longrightarrow> xa < fst (the f)"
        by simp
    qed
  qed

  show dom : "\<And>f. PFT.arr f \<Longrightarrow> DL.dom (HFunctorHat f) = HFunctorHat (PFT.dom f)"
    using arr
    unfolding DL.dom_char DL.arr_char
    unfolding Ab.Lawv_comp_def
    unfolding classical_category.cod_char [OF Ab.Lawv_is_classical_category]
    apply simp
  proof-
    fix f
    assume arr_f : "PFT.arr f"
    show "Some (Ab.Id' (Ab.Cod' (the (HFunctorHat f)))) = HFunctorHat (PFT.dom f)"
      unfolding HFunctorHat_def
      apply (simp add: arr_f Ab.Id'_def Ab.Cod'_def Ab.MkArr_def)
      unfolding pointed_fin_set.dom_char [OF arr_f]
      apply (simp add: fin_set.Id'_def)
    proof
      fix x
      show "(\<lambda>x\<in>carrier (free_Abelian_group {i. 0 < i \<and> i < length (snd (the f))}). x) x =
         restrict (HFunctorHat_on_arr (Some (length (snd (the f)), rev_get (length (snd (the f))) (\<lambda>k. k))))
          (carrier (free_Abelian_group {i. 0 < i \<and> i < length (snd (the f))})) x"
        unfolding HFunctorHat_on_arr_def 
        apply auto
        apply (rule_tac poly_mapping_eqI)
        apply auto
        
      proof-
        assume A: "Poly_Mapping.keys x \<subseteq> {i. 0 < i \<and> i < length (snd (the f))}"
        have "0 \<notin> {i. 0 < i \<and> i < length (snd (the f))}"
          by simp
        from this and A have " 0 \<notin> Poly_Mapping.keys x"
          by auto
        then show "poly_mapping.lookup x 0 = 0"
          by (simp add: in_keys_iff)
        fix k
        assume "\<not> k < length (snd (the f))"
        then have "k \<notin> {i. 0 < i \<and> i < length (snd (the f))}"
          by simp
        from this and A have "k \<notin> Poly_Mapping.keys x" 
          by auto
        then show "poly_mapping.lookup x k = 0"
          by (simp add: in_keys_iff)
      qed
    qed
  qed
  show cod : "\<And>f. PFT.arr f \<Longrightarrow> DL.cod (HFunctorHat f) = HFunctorHat (PFT.cod f)"
    using arr
    unfolding DL.cod_char DL.arr_char
    unfolding Ab.Lawv_comp_def
    unfolding classical_category.dom_char [OF Ab.Lawv_is_classical_category]
    apply simp
  proof-
    fix f
    assume arr_f : "PFT.arr f"
    show "Some (Ab.Id' (Ab.Dom' (the (HFunctorHat f)))) = HFunctorHat (PFT.cod f)"
      unfolding HFunctorHat_def
      apply (simp add: arr_f Ab.Id'_def Ab.Dom'_def Ab.MkArr_def)
      unfolding pointed_fin_set.cod_char [OF arr_f]
      apply (simp add: fin_set.Id'_def)
    proof
      fix x
      show "(\<lambda>x\<in>carrier (free_Abelian_group {i. 0 < i \<and> i < fst (the f)}). x) x =
         restrict (HFunctorHat_on_arr (Some (fst (the f), rev_get (fst (the f)) (\<lambda>k. k))))
          (carrier (free_Abelian_group {i. 0 < i \<and> i < fst (the f)})) x"
        unfolding HFunctorHat_on_arr_def 
        apply auto
        apply (rule_tac poly_mapping_eqI)
        apply auto
        
      proof-
        assume A: "Poly_Mapping.keys x \<subseteq> {i. 0 < i \<and> i < fst (the f)}"
        have "0 \<notin> {i. 0 < i \<and> i < length (snd (the f))}"
          by simp
        from this and A have " 0 \<notin> Poly_Mapping.keys x"
          by auto
        then show "poly_mapping.lookup x 0 = 0"
          by (simp add: in_keys_iff)
        fix k
        assume "\<not> k < fst (the f)"
        then have "k \<notin> {i. 0 < i \<and> i < fst (the f)}"
          by simp
        from this and A have "k \<notin> Poly_Mapping.keys x" 
          by auto
        then show "poly_mapping.lookup x k = 0"
          by (simp add: in_keys_iff)
      qed
    qed
  qed
  fix g f
  assume arr_gf : "PFT.seq g f"
  have arr_hgf : "DL.seq (HFunctorHat g) (HFunctorHat f)"
    apply (rule_tac PFT.seqE [OF arr_gf])
    apply (rule_tac DL.seqI)
    using arr dom cod by simp_all

  have arr_f : "PFT.arr f"
    apply (rule_tac PFT.seqE [OF arr_gf])
    by simp
  have arr_g : "PFT.arr g"
    apply (rule_tac PFT.seqE [OF arr_gf])
    by simp
  have seq : "PFT.dom g = PFT.cod f"
    apply (rule_tac PFT.seqE [OF arr_gf])
    by simp


  interpret LawvCC : classical_category Ab.is_Z_tothe_n
   "(classical_full_subcategory.SArr Ab.Arr' Ab.Dom' Ab.Cod' Ab.is_Z_tothe_n)" Ab.Dom' Ab.Cod' Ab.Id'
   Ab.Comp'
    using Ab.Lawv_is_classical_category.

  have LA_arr : "\<And>f. DL.arr f \<Longrightarrow> AbCC.arr f"
    unfolding AbCC.arr_char
    unfolding DL.arr_char 
    unfolding Ab.Lawv_comp_def
    unfolding LawvCC.arr_char
    unfolding classical_full_subcategory.SArr_def 
          [OF Ab.Lawv_is_classical_full_subcategory]
    by simp
  have LA_dom : "\<And>f. DL.arr f \<Longrightarrow> AbCC.cod f = DL.dom f"
    unfolding AbCC.cod_char
    apply (simp add: LA_arr)
    unfolding DL.dom_char
    unfolding Ab.Lawv_comp_def
    unfolding LawvCC.cod_char
    by simp
  have LA_cod : "\<And>f. DL.arr f \<Longrightarrow> AbCC.dom f = DL.cod f"
    unfolding AbCC.dom_char
    apply (simp add: LA_arr)
    unfolding DL.cod_char
    unfolding Ab.Lawv_comp_def
    unfolding LawvCC.dom_char
    by simp
  have LA_comp : "\<And>g f. DL.seq g f \<Longrightarrow> DL.comp g f = Ab.comp f g"
    unfolding Ab.comp_def
    apply (subst AbCC.comp_simp)
    using LA_arr
    unfolding AbCC.arr_char AbCC.null_char
     apply (metis AbCC.arr_char AbCC.classical_category_axioms DL.seqE
            LA_cod LA_dom category.seqI classical_category.induces_category)
    apply simp
    unfolding Ab.Lawv_comp_def
    apply (subst LawvCC.comp_simp)
    by auto


  show "HFunctorHat (pointed_fin_set.comp g f) = DL.comp (HFunctorHat g) (HFunctorHat f)"
    apply (subst LA_comp [OF arr_hgf])
    apply (rule_tac Ab.comp_eqI)
          apply (rule_tac LA_arr [OF arr [OF arr_gf]])
         apply (rule_tac LA_arr [OF arr [OF arr_f]])
        apply (rule_tac LA_arr [OF arr [OF arr_g]])
    unfolding LA_cod [OF arr [OF arr_g]]
    unfolding LA_cod [OF arr [OF arr_gf]]
    unfolding cod [OF arr_g] cod [OF arr_gf]
    unfolding PFT.cod_comp [OF arr_gf] apply simp
    unfolding LA_dom [OF arr [OF arr_f]]
    unfolding LA_dom [OF arr [OF arr_gf]]
    unfolding dom [OF arr_f] dom [OF arr_gf]
    unfolding PFT.dom_comp [OF arr_gf] apply simp
    unfolding LA_dom [OF arr [OF arr_g]]
    unfolding LA_cod [OF arr [OF arr_f]]
    unfolding dom [OF arr_g] cod [OF arr_f]
     apply (simp add: seq)
    unfolding HFunctorHat_def
    apply (simp add: arr_f arr_g arr_gf Ab.MkArr_def Ab.Dom'_def)
    unfolding pointed_fin_set.comp_char [OF arr_f arr_g seq]
    unfolding fin_set.Comp'_def
    apply auto
    apply (simp add: HFunctorHat_on_arr_def)
    apply (rule_tac poly_mapping_eqI)
    apply auto
  proof-
    fix x :: "nat \<Rightarrow>\<^sub>0 int"
    fix k :: nat
    have g_zero: "get (snd (the g)) 0 = 0"
      using arr_g
      unfolding pointed_fin_set.comp_def
      unfolding subcategory.arr_char [OF pointed_fin_set.is_subcategory]
      unfolding pointed_fin_set.PointedArr'_def
      by simp
    assume A: "Poly_Mapping.keys x \<subseteq> {i. 0 < i \<and> i < fst (the g)}"
    have "0 \<notin> {i. 0 < i \<and> i < fst (the g)}"
      by simp
    from this and A have "0 \<notin> Poly_Mapping.keys x" by auto
    then show "poly_mapping.lookup x (get (snd (the g)) 0) = 0"
      unfolding g_zero
      by (simp add: in_keys_iff)
    assume "k < length (snd (the f))"
    then have fk_less: "get (snd (the f)) k < fst (the f)"
      using arr_f
      unfolding pointed_fin_set.comp_def
      unfolding subcategory.arr_char [OF pointed_fin_set.is_subcategory]
      unfolding pointed_fin_set.PointedArr'_def
      unfolding fin_set.arr_char
      unfolding fin_set.Arr'_def
      by simp
    have seq_eq : "fst (the f) = length (snd (the g))"
      using seq arr_f arr_g
      unfolding pointed_fin_set.comp_def
      unfolding subcategory.dom_char [OF pointed_fin_set.is_subcategory]
      unfolding subcategory.cod_char [OF pointed_fin_set.is_subcategory]
      unfolding subcategory.arr_char [OF pointed_fin_set.is_subcategory]
      apply simp
      unfolding fin_set.dom_char fin_set.cod_char pointed_fin_set.PointedArr'_def
      unfolding reverse_equality [OF fin_set.comp_def]
      by (simp add: fin_set.Id'_def)
    assume "\<not> get (snd (the f)) k < length (snd (the g))"
    then have "False"
      using fk_less
      unfolding seq_eq by simp
    then show "poly_mapping.lookup x (get (snd (the g)) (get (snd (the f)) k)) = 0"
      by simp
  qed
qed
    






definition HFunctor where
  "HFunctor = T.map \<circ> HFunctorHat"

lemma is_functor : "functor pointed_fin_set.comp pointed_set.pointed_set_comp HFunctor"
  unfolding HFunctor_def
  apply (rule_tac functor_comp)
   apply (rule_tac HFunctorHat)
  by (rule_tac T.is_functor)



end



end
