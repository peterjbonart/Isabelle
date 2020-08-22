theory LoopSpace
  imports Main
          SimplicialSet
          "Category3.FunctorCategory"
          Homotopy
begin



lemma (in horizontal_composite) interchange_fun:
  assumes "A.arr x"
  shows "(\<tau> \<circ> G) (A.cod x) \<cdot>\<^sub>C (H \<circ> \<sigma>) x = (K \<circ> \<sigma>) (A.cod x) \<cdot>\<^sub>C (\<tau> \<circ> F) x"
proof-
  have eq1: "vertical_composite.map A C (H \<circ> \<sigma>) (\<tau> \<circ> G) =
         vertical_composite.map A C (\<tau> \<circ> F) (K \<circ> \<sigma>)"
  using interchange [OF \<sigma>.natural_transformation_axioms
                        \<tau>.natural_transformation_axioms]
  by simp
  interpret H\<sigma>: horizontal_composite A B C F G H H \<sigma> H
    unfolding horizontal_composite_def
    using \<sigma>.natural_transformation_axioms
          functor_is_transformation [OF H.functor_axioms]
    unfolding natural_transformation_def
    by auto
  have G_functor: "functor A B G"
    using \<sigma>.natural_transformation_axioms
    unfolding natural_transformation_def
    by simp
  interpret \<tau>G: horizontal_composite A B C G G H K G \<tau>
    unfolding horizontal_composite_def
    using \<tau>.natural_transformation_axioms
          functor_is_transformation [OF G_functor]
    unfolding natural_transformation_def
    by auto


  have eq2: "vertical_composite.map A C (H \<circ> \<sigma>) (\<tau> \<circ> G) x = \<tau>G.map (A.cod x) \<cdot>\<^sub>C H\<sigma>.map x"
    apply (subst vertical_composite.map_def)
    unfolding vertical_composite_def
    using H\<sigma>.is_natural_transformation \<tau>G.is_natural_transformation
    using natural_transformation_def apply blast
    by (simp add: \<open>A.arr x\<close>)

  interpret K\<sigma>: horizontal_composite A B C F G K K \<sigma> K
    unfolding horizontal_composite_def
    using \<sigma>.natural_transformation_axioms
          functor_is_transformation [OF K.functor_axioms]
    unfolding natural_transformation_def
    by auto
  have F_functor: "functor A B F"
    using \<sigma>.natural_transformation_axioms
    unfolding natural_transformation_def
    by simp
  interpret \<tau>F: horizontal_composite A B C F F H K F \<tau>
    unfolding horizontal_composite_def
    using \<tau>.natural_transformation_axioms
          functor_is_transformation [OF F_functor]
    unfolding natural_transformation_def
    by auto

  have eq3: "vertical_composite.map A C (\<tau> \<circ> F) (K \<circ> \<sigma>) x = K\<sigma>.map (A.cod x) \<cdot>\<^sub>C \<tau>F.map x"
    apply (subst vertical_composite.map_def)
    unfolding vertical_composite_def
    using K\<sigma>.is_natural_transformation \<tau>F.is_natural_transformation
    using natural_transformation_def apply blast
    by (simp add: \<open>A.arr x\<close>)
  show "\<tau>G.map (A.cod x) \<cdot>\<^sub>C H\<sigma>.map x = K\<sigma>.map (A.cod x) \<cdot>\<^sub>C \<tau>F.map x"
    using eq1 eq2 eq3 by simp
qed




interpretation P: pointed_set.

definition pointed_subset where
  "pointed_subset X S = (fst S = fst X \<and> snd S \<subseteq> snd X)"

locale sub_functor =
  F: "functor" C P.pointed_set_comp F
  for C :: "'c comp" 
  and F :: "'c \<Rightarrow> 'a P.parr option"
  and S :: "'c \<Rightarrow> 'a pointed_set" +
assumes S_obj : "\<And>f. F.A.ide f \<Longrightarrow> P.Obj' (S f)"
  and   S_subseteq: "\<And>f. F.A.ide f \<Longrightarrow> pointed_subset (P.Dom' (the (F f))) (S f)"
  and   S_restrict : "\<And>f. F.A.arr f \<Longrightarrow> fst (the (F f)) \<in> snd (S (F.A.dom f)) \<rightarrow> snd (S (F.A.cod f))"
begin

definition map :: "'c \<Rightarrow> 'a pointed_set.parr option" where
  "map = MkFunctor C P.pointed_set_comp
         (\<lambda>f. Some (P.MkArr (S (F.A.dom f)) (S (F.A.cod f)) (fst (the (F f)))))"


lemma subfunctor_arr : assumes arr_f : "F.A.arr f"
  shows "F.B.arr (map f)"
  unfolding map_def
  apply (simp add: arr_f)
  unfolding P.arr_char
  apply simp
  unfolding P.MkArr_def P.Arr'_def
  using S_obj [OF F.A.ide_dom [OF arr_f]]
  using S_obj [OF F.A.ide_cod [OF arr_f]]
  unfolding P.Obj'_def
  apply auto
  unfolding setcat.Arr_def
  using S_restrict [OF arr_f]
   apply auto
  using S_subseteq [OF F.A.ide_dom [OF arr_f]]
  using S_subseteq [OF F.A.ide_cod [OF arr_f]]
  unfolding pointed_subset_def
  apply simp
proof-
  show "fst (the (F f)) (fst (fst (snd (the (F (F.A.dom f)))))) =
    fst (fst (snd (the (F (F.A.cod f)))))"
    unfolding reverse_equality [OF F.preserves_dom [OF arr_f]]
    unfolding reverse_equality [OF F.preserves_cod [OF arr_f]]
    unfolding P.dom_char [OF F.preserves_arr [OF arr_f]]
    unfolding P.cod_char [OF F.preserves_arr [OF arr_f]]
    unfolding P.Id'_def apply simp
    using F.preserves_arr [OF arr_f]
    unfolding P.arr_char P.Arr'_def
    by simp
qed

lemma subfunctor_dom : assumes arr_f : "F.A.arr f"
  shows "map (F.A.dom f) = F.B.dom (map f)"
  unfolding P.dom_char [OF subfunctor_arr [OF arr_f]]
  unfolding map_def
  apply (simp add: arr_f)
  unfolding P.MkArr_def P.Id'_def apply simp
proof-
  have eq1: "(F (F.A.dom f)) = Some (P.Id' (P.Dom' (the (F (F.A.dom f)))))"
    using F.preserves_ide [OF F.A.ide_dom [OF arr_f]]
    unfolding P.ide_char
    by simp
  have eq2: "snd (fst (snd (the (F (F.A.dom f))))) \<inter> snd (S (F.A.dom f)) = snd (S (F.A.dom f))"
    using S_subseteq [OF F.A.ide_dom [OF arr_f]]
    unfolding pointed_subset_def
    by auto
  show "restrict (fst (the (F (F.A.dom f)))) (snd (S (F.A.dom f))) = (\<lambda>x\<in>snd (S (F.A.dom f)). x)"
    apply (subst eq1)
    unfolding P.Id'_def
    by (simp add: eq2)
qed

lemma subfunctor_cod : assumes arr_f : "F.A.arr f"
  shows "map (F.A.cod f) = F.B.cod (map f)"
  unfolding P.cod_char [OF subfunctor_arr [OF arr_f]]
  unfolding map_def
  apply (simp add: arr_f)
  unfolding P.MkArr_def P.Id'_def apply simp
proof-
  have eq1: "(F (F.A.cod f)) = Some (P.Id' (P.Dom' (the (F (F.A.cod f)))))"
    using F.preserves_ide [OF F.A.ide_cod [OF arr_f]]
    unfolding P.ide_char
    by simp
  have eq2: "snd (fst (snd (the (F (F.A.cod f))))) \<inter> snd (S (F.A.cod f)) = snd (S (F.A.cod f))"
    using S_subseteq [OF F.A.ide_cod [OF arr_f]]
    unfolding pointed_subset_def
    by auto
  show "restrict (fst (the (F (F.A.cod f)))) (snd (S (F.A.cod f))) = (\<lambda>x\<in>snd (S (F.A.cod f)). x)"
    apply (subst eq1)
    unfolding P.Id'_def
    by (simp add: eq2)
qed



lemma is_functor : "functor C P.pointed_set_comp map"
  unfolding functor_def
  apply (simp add: F.A.category_axioms F.B.category_axioms)
  unfolding functor_axioms_def
  apply safe
proof-
  show "\<And>f. \<not> F.A.arr f \<Longrightarrow> local.map f = F.B.null"
    unfolding map_def by simp
  show "\<And>f. F.A.arr f \<Longrightarrow> F.B.arr (local.map f)"
    using subfunctor_arr.
  show "\<And>f. F.A.arr f \<Longrightarrow> F.B.dom (local.map f) = local.map (F.A.dom f)"
    using reverse_equality [OF subfunctor_dom].
  show "\<And>f. F.A.arr f \<Longrightarrow> F.B.cod (local.map f) = local.map (F.A.cod f)"
    using reverse_equality [OF subfunctor_cod].
next
  fix g f
  assume arr_gf : "F.A.seq g f"
  then have arr_f : "F.A.arr f" by blast
  from arr_gf have arr_g : "F.A.arr g" by blast
  have arr_sgf : "F.B.seq (local.map g) (local.map f)"
    apply (rule_tac F.A.seqE [OF arr_gf])
    apply (rule_tac F.B.seqI)
    unfolding reverse_equality [OF subfunctor_dom]
    unfolding reverse_equality [OF subfunctor_cod]
    using subfunctor_arr by simp_all
  show "local.map (C g f) = P.pointed_set_comp (local.map g) (local.map f)"
    apply (rule_tac reverse_equality)
    apply (rule_tac P.comp_eq_char2)
        apply (simp add: arr_sgf)
       apply (simp add: subfunctor_arr [OF arr_gf])
    unfolding reverse_equality [OF subfunctor_dom [OF arr_gf]]
    unfolding reverse_equality [OF subfunctor_dom [OF arr_f]]
    using F.A.dom_comp [OF arr_gf] apply simp
    unfolding reverse_equality [OF subfunctor_cod [OF arr_gf]]
    unfolding reverse_equality [OF subfunctor_cod [OF arr_g]]
    using F.A.cod_comp [OF arr_gf] apply simp
  proof-
    fix x
    show "x \<in> snd (fst (snd (the (local.map f)))) \<Longrightarrow>
         x \<in> snd (fst (snd (the (local.map (C g f))))) \<Longrightarrow>
         fst (the (local.map f)) x \<in> snd (fst (snd (the (local.map g)))) \<Longrightarrow>
         fst (the (local.map g)) (fst (the (local.map f)) x) = fst (the (local.map (C g f))) x"
      unfolding map_def
      apply (simp add: arr_f arr_g arr_gf)
      unfolding P.MkArr_def apply simp
      apply (subst P.fst_comp_char)
      using F.preserves_arr [OF arr_gf]
      unfolding F.preserves_comp [OF arr_gf]
        apply simp
      using S_subseteq [OF F.A.ide_dom [OF arr_f]]
      unfolding pointed_subset_def
      unfolding reverse_equality [OF F.preserves_dom [OF arr_f]]
      unfolding P.dom_char [OF F.preserves_arr [OF arr_f]]
      unfolding P.Id'_def
      by auto
  qed
qed


lemma on_obj : "F.A.ide c \<Longrightarrow> map c = Some (P.Id' (S c))"
proof-
  interpret G : "functor" C P.pointed_set_comp map
    using is_functor.
  assume ide_c: "F.A.ide c"
  have ide_eq: "F c = Some (P.Id' (P.Dom' (the (F c))))"
    using F.preserves_ide [OF ide_c]
    unfolding P.ide_char by simp
  have "the (map c) = P.Id' (S c)"
    apply (rule_tac P.fun_eq_char)
    using G.preserves_ide [OF ide_c] P.ide_char apply blast
    using classical_category.Arr_Id [OF P.ccpf S_obj [OF ide_c]] apply simp
    unfolding P.Id'_def map_def P.MkArr_def
      apply (simp_all add: ide_c)
    apply (subst ide_eq)
    unfolding P.Id'_def apply simp
    using S_subseteq [OF ide_c]
    unfolding pointed_subset_def
    by auto
  then show "map c = Some (P.Id' (S c))"
    by (metis G.preserves_ide ide_c option.sel pointed_set.ide_char)
qed



end





context begin

interpretation Delta : simplex.
interpretation D : category Delta.comp
  using Delta.is_category.

definition plusone_functor where
  "plusone_functor = MkFunctor Delta.comp Delta.comp
         (\<lambda>f. Some ((fst (the f) + 1, 0 # (fmap Suc (snd (the f))))))"

lemma plusone_arr:
  assumes arr_f : "D.arr f"
  shows "D.arr (plusone_functor f)"
  unfolding plusone_functor_def
  apply (simp add: arr_f)
  using arr_f
  unfolding Delta.comp_def
  unfolding dual_category.arr_char [OF Delta.is_dual_category]
  unfolding subcategory.arr_char [OF Delta.is_subcategory]
  unfolding Delta.OrdArr_def
  unfolding fin_set.comp_def
  unfolding classical_category.arr_char [OF fin_set.is_classical_category]
  unfolding fin_set.Arr'_def
  apply auto
proof-
  fix a b
  assume "f = Some (a, b)"
  assume "\<forall>n<length b. get b n < a"
  assume "\<forall>i j. i \<le> j \<longrightarrow> j < length b \<longrightarrow> get b i \<le> get b j"
  fix n
  assume "n < Suc (length b)"
  show "get (0 # rev_get (length b) (\<lambda>n. Suc (get b n))) n < Suc a"
    apply (cases n)
     apply simp
    apply simp
    apply (subst get_rev_get)
    using \<open>n < Suc (length b)\<close> apply simp
    using \<open>\<forall>n<length b. get b n < a\<close> \<open>n < Suc (length b)\<close> 
    by simp
  fix i
  assume "i \<le> n"
  show "get (0 # rev_get (length b) (\<lambda>k. Suc (get b k))) i
       \<le> get (0 # rev_get (length b) (\<lambda>k. Suc (get b k))) n"
    apply (cases n)
     apply (cases i)
      apply simp
     apply simp
     apply (subst get_rev_get)
    using \<open>i \<le> n\<close> \<open>n < Suc (length b)\<close> apply simp
    using \<open>i \<le> n\<close> apply simp
    apply simp
    apply (subst get_rev_get)
    using \<open>n < Suc (length b)\<close> apply simp
    apply (cases i)
     apply simp
    apply simp
    apply (subst get_rev_get)
    using \<open>i \<le> n\<close> \<open>n < Suc (length b)\<close> apply simp
    using \<open>\<forall>i j. i \<le> j \<longrightarrow> j < length b \<longrightarrow> get b i \<le> get b j\<close>
          \<open>i \<le> n\<close> \<open>n < Suc (length b)\<close> by simp
qed

lemma plusone_Id :
  assumes "0 < n"
  shows "Some (fin_set.Id' (Suc n)) =
    plusone_functor (Some (fin_set.Id' n))"
  unfolding plusone_functor_def
  using Delta.ide_Dn [OF \<open>0 < n\<close>]
  apply simp
  unfolding fin_set.Id'_def
  apply safe
  apply simp
  apply (rule_tac getFaithful)
  unfolding rev_get_length
   apply simp
  unfolding get_rev_get
proof-
  fix k
  assume "k < Suc n"
  show "k =
          get (0 #
               rev_get (length (snd (n, rev_get n (\<lambda>k. k))))
                (\<lambda>na. Suc (get (snd (n, rev_get n (\<lambda>k. k))) na)))
           k"
    apply (cases k)
     apply simp
    using \<open>k < Suc n\<close> by (simp add: get_rev_get)
qed


lemma plusone_dom :
  assumes arr_f : "D.arr f"
  shows "D.dom (plusone_functor f) = plusone_functor (D.dom f)"
  using arr_f plusone_arr [OF arr_f]
  unfolding Delta.comp_def
  unfolding dual_category.dom_char [OF Delta.is_dual_category]
  unfolding dual_category.arr_char [OF Delta.is_dual_category]
  unfolding subcategory.cod_char [OF Delta.is_subcategory]
  apply simp
  unfolding subcategory.arr_char [OF Delta.is_subcategory]
  unfolding Delta.OrdArr_def
  unfolding fin_set.comp_def
  unfolding classical_category.cod_char [OF fin_set.is_classical_category]
  apply simp
  unfolding classical_category.arr_char [OF fin_set.is_classical_category]
proof-
  assume A: "(f \<noteq> None \<and> fin_set.Arr' (the f)) \<and>
    snd (the f) \<noteq> [] \<and>
    (\<forall>i j. i \<le> j \<longrightarrow>
           j < length (snd (the f)) \<longrightarrow>
           get (snd (the f)) i \<le> get (snd (the f)) j)"
  then have rule: "(\<And>n. n<length (snd (the f)) \<Longrightarrow>
        get (snd (the f)) n < fst (the f))"
    unfolding fin_set.Arr'_def by simp
  have "get (snd (the f)) 0 < fst (the f)"
    apply (rule_tac rule)
    using A
    unfolding fin_set.Arr'_def
    by simp
  then have "0 < fst (the f)" by simp
  show "Some (fin_set.Id' (fst (the (plusone_functor f)))) =
    plusone_functor (Some (fin_set.Id' (fst (the f))))"
    apply (subst reverse_equality [OF plusone_Id])
    unfolding plusone_functor_def
    using \<open>0 < fst (the f)\<close> apply simp
    by (simp add: arr_f)
qed

lemma plusone_cod :
  assumes arr_f : "D.arr f"
  shows "D.cod (plusone_functor f) = plusone_functor (D.cod f)"
  using arr_f plusone_arr [OF arr_f]
  unfolding Delta.comp_def
  unfolding dual_category.cod_char [OF Delta.is_dual_category]
  unfolding dual_category.arr_char [OF Delta.is_dual_category]
  unfolding subcategory.dom_char [OF Delta.is_subcategory]
  apply simp
  unfolding subcategory.arr_char [OF Delta.is_subcategory]
  unfolding Delta.OrdArr_def
  unfolding fin_set.comp_def
  unfolding classical_category.dom_char [OF fin_set.is_classical_category]
  apply simp
  unfolding classical_category.arr_char [OF fin_set.is_classical_category]
proof-
  assume "(f \<noteq> None \<and> fin_set.Arr' (the f)) \<and>
    snd (the f) \<noteq> [] \<and>
    (\<forall>i j. i \<le> j \<longrightarrow>
           j < length (snd (the f)) \<longrightarrow>
           get (snd (the f)) i \<le> get (snd (the f)) j)"
  then have "snd (the f) \<noteq> []" by simp
  show "Some (fin_set.Id' (length (snd (the (plusone_functor f))))) =
    plusone_functor (Some (fin_set.Id' (length (snd (the f)))))"
    apply (subst reverse_equality [OF plusone_Id])
    using \<open>snd (the f) \<noteq> []\<close> apply simp
    unfolding plusone_functor_def
    by (simp add: arr_f)
qed



lemma plusone_functor : "functor Delta.comp Delta.comp
                         plusone_functor"
  unfolding functor_def
  apply (simp add: Delta.is_category)
  unfolding functor_axioms_def
  apply safe
proof-
  show "\<And>f. \<not> D.arr f \<Longrightarrow> plusone_functor f = D.null"
    unfolding plusone_functor_def by simp
  show "\<And>f. D.arr f \<Longrightarrow> D.arr (plusone_functor f)"
    using plusone_arr.
  show "\<And>f. D.arr f \<Longrightarrow>
         D.dom (plusone_functor f) = plusone_functor (D.dom f)"
    using plusone_dom.
  show "\<And>f. D.arr f \<Longrightarrow>
         D.cod (plusone_functor f) = plusone_functor (D.cod f)"
    using plusone_cod.
next
  fix g f
  assume arr_gf : "D.seq g f"
  have arr_pgf : "D.seq (plusone_functor g) (plusone_functor f)"
    apply (rule_tac D.seqE [OF arr_gf])
    apply (rule_tac D.seqI)
    unfolding plusone_dom plusone_cod
    using plusone_arr by simp_all
  show "plusone_functor (Delta.comp g f) =
           Delta.comp (plusone_functor g) (plusone_functor f)"
    apply (rule_tac D.seqE [OF arr_gf])
    apply (rule_tac D.seqE [OF arr_pgf])
    apply (subst plusone_functor_def)
    apply simp
    unfolding Delta.comp_def
    unfolding dual_category.arr_char [OF Delta.is_dual_category]
    unfolding dual_category.dom_char [OF Delta.is_dual_category]
    unfolding dual_category.cod_char [OF Delta.is_dual_category]
    unfolding dual_category.comp_def [OF Delta.is_dual_category]
    unfolding subcategory.dom_char [OF Delta.is_subcategory]
    unfolding subcategory.cod_char [OF Delta.is_subcategory]
    unfolding subcategory.arr_char [OF Delta.is_subcategory]
    unfolding subcategory.comp_def [OF Delta.is_subcategory]
    apply simp
    unfolding Delta.OrdArr_def
    unfolding fin_set.comp_def
    unfolding classical_category.dom_char [OF fin_set.is_classical_category]
    unfolding classical_category.cod_char [OF fin_set.is_classical_category]
    unfolding classical_category.arr_char [OF fin_set.is_classical_category]
    unfolding classical_category.comp_char [OF fin_set.is_classical_category]
    unfolding fin_set.Id'_def
    apply simp
  proof-
    assume "fst (the g) = length (snd (the f)) \<and>
    rev_get (fst (the g)) (\<lambda>k. k) =
    rev_get (length (snd (the f))) (\<lambda>k. k)"
    then have "length (snd (the f)) = fst (the g)" by simp
    assume A_g: "(\<exists>a b. g = Some (a, b)) \<and>
    fin_set.Arr' (the g) \<and>
    snd (the g) \<noteq> [] \<and>
    (\<forall>i j. i \<le> j \<longrightarrow>
           j < length (snd (the g)) \<longrightarrow>
           get (snd (the g)) i \<le> get (snd (the g)) j)"
    then have "snd (the g) \<noteq> []" by simp
    from A_g have "fin_set.Arr' (the g)" by simp
    have prod_collapse_rule : "\<And>x y. fst x = fst y 
     \<Longrightarrow> snd x = snd y \<Longrightarrow> x = y" by auto

    show "(Suc (fst (fin_set.Comp' (the f) (the g))),
     0 #
     rev_get (length (snd (fin_set.Comp' (the f) (the g))))
      (\<lambda>n. Suc (get (snd (fin_set.Comp' (the f) (the g))) n))) =
    fin_set.Comp' (the (plusone_functor f))
     (the (plusone_functor g))"
      apply (rule_tac D.seqE [OF arr_gf])
      unfolding plusone_functor_def
      apply simp
      apply (rule_tac prod_collapse_rule)
       apply (subst fin_set.Comp'_def)
       apply (subst fin_set.Comp'_def)
       apply (subst fin_set.Comp'_def)
       apply (subst fin_set.Comp'_def)
       apply simp
      apply simp
      apply (rule_tac getFaithful)
       apply (subst fin_set.Comp'_def)
       apply (subst fin_set.Comp'_def)
       apply (subst fin_set.Comp'_def)
       apply (simp add: app_length)
      apply simp
    proof-
      fix n
      assume nl: "n < Suc (length
                   (snd (fin_set.Comp' (the f) (the g))))"
      then have "n < Suc (length (snd (the g)))"
        unfolding fin_set.Comp'_def
        by simp
      define rev_get_nosimp :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat list"
        where "rev_get_nosimp = rev_get"
      show "get (0 # rev_get
       (length (snd (fin_set.Comp' (the f) (the g))))
       (\<lambda>n. Suc (get (snd (fin_set.Comp' (the f)
       (the g))) n))) n =
         get (snd (fin_set.Comp' (Suc (fst (the f)),
         0 # rev_get (length (snd (the f)))
          (\<lambda>n. Suc (get (snd (the f)) n)))
           (Suc (fst (the g)), 0 #
           rev_get (length (snd (the g)))
           (\<lambda>n. Suc (get (snd (the g)) n))))) n"
        apply (cases n)
         apply simp
         apply (subst fin_set.Comp'_def)
         apply simp
          apply (simp add: \<open>snd (the g) \<noteq> []\<close>)
        apply (subst get_rev_get)
        using nl apply simp
        apply (subst fin_set.Comp'_def)
        apply simp
        apply (subst get_rev_get)
        using \<open>n < Suc (length (snd (the g)))\<close> apply simp
        unfolding fin_set.Comp'_def
        unfolding reverse_equality [OF rev_get_nosimp_def]
        apply simp
        apply (subst rev_get_nosimp_def)
        apply (subst get_rev_get)
         apply (subst rev_get_nosimp_def)
        using \<open>n < Suc (length (snd (the g)))\<close> apply simp
        apply simp
        apply (subst rev_get_nosimp_def)
        apply (subst rev_get_nosimp_def)
        apply (subst get_rev_get)
        using \<open>n < Suc (length (snd (the g)))\<close> apply simp
        apply simp
        apply (subst get_rev_get)
        unfolding \<open>length (snd (the f)) = fst (the g)\<close>
        using \<open>fin_set.Arr' (the g)\<close>
        unfolding fin_set.Arr'_def
        using \<open>n < Suc (length (snd (the g)))\<close> apply simp
        by simp
    qed
  qed
qed

definition d0_nattrafo where
  "d0_nattrafo = MkFunctor Delta.comp Delta.comp 
              (\<lambda>f. Delta.comp f (Delta.d (fst (the (D.dom f))) 0))"


lemma arr_f_n_dom : assumes arr_f : "D.arr f"
  shows "0 < fst (the (D.dom f))"
  using arr_f 
  by (metis D.arr_dom assms fin_set.Arr'_def fin_set.arr_char 
                gr_implies_not_zero gr_zeroI length_greater_0_conv 
                simplex.OrdArr_def simplex.arr_char)


lemma d0_nattrafo_arr : assumes arr_f : "D.arr f"
  shows "D.arr (d0_nattrafo f)"
  unfolding d0_nattrafo_def
  apply (simp add: arr_f)
  apply (rule_tac D.seqI')
   apply (rule_tac Delta.d_in_hom)
  using arr_f_n_dom [OF arr_f] apply simp
  apply (subst reverse_equality [OF Delta.dom_char])
  using D.ide_dom [OF arr_f] apply simp
  unfolding D.dom_dom [OF arr_f]
  apply (rule_tac D.in_homI)
  by (simp_all add: arr_f)


lemma d0_nattrafo : "natural_transformation Delta.comp Delta.comp
                    plusone_functor (identity_functor.map Delta.comp)
                    d0_nattrafo"
  unfolding natural_transformation_def
  apply (simp add: Delta.is_category plusone_functor D.is_functor)
  unfolding natural_transformation_axioms_def
  apply safe
proof-
  show "\<And>f. \<not> D.arr f \<Longrightarrow> d0_nattrafo f = D.null"
    unfolding d0_nattrafo_def by simp
  fix f
  assume arr_f : "D.arr f"
  then have arr_df : "D.arr (d0_nattrafo f)"
    using d0_nattrafo_arr by simp
  then have seq : "D.seq f (Delta.d (fst (the (D.dom f))) 0)"
    unfolding d0_nattrafo_def by (simp add: arr_f)
  show "D.dom (d0_nattrafo f) = plusone_functor (D.dom f)"
    unfolding d0_nattrafo_def
    apply (simp add: arr_f)
    apply (subst D.dom_comp [OF seq])
    apply (subst D.in_hom_dom [OF Delta.d_in_hom])
    using arr_f_n_dom [OF arr_f] apply simp
    apply (subst plusone_Id)
    using arr_f_n_dom [OF arr_f] apply simp
    apply (subst reverse_equality [OF Delta.dom_char])
    using D.ide_dom [OF arr_f] apply simp
    using D.dom_dom [OF arr_f] by simp
  show "D.cod (d0_nattrafo f) = D.map (D.cod f)"
    unfolding d0_nattrafo_def
    apply (simp add: arr_f)
    apply (subst D.cod_comp [OF seq])
    by simp
  show "Delta.comp (D.map f) (d0_nattrafo (D.dom f)) = d0_nattrafo f"
    unfolding D.map_def d0_nattrafo_def
    apply (simp add: arr_f)
    apply (subst D.comp_ide_arr [OF D.ide_dom [OF arr_f]])
    using d0_nattrafo_arr [OF D.ideD(1) [OF D.ide_dom [OF arr_f]]]
    unfolding d0_nattrafo_def
     apply (simp add: D.ideD(1) [OF D.ide_dom [OF arr_f]])
    unfolding D.dom_dom [OF arr_f] apply simp
    by simp
  show "Delta.comp (d0_nattrafo (D.cod f)) (plusone_functor f) = d0_nattrafo f"
    unfolding d0_nattrafo_def
    apply (simp add: arr_f)
    apply (subst D.comp_ide_arr [OF D.ide_cod [OF arr_f]])
    using d0_nattrafo_arr [OF D.ideD(1) [OF D.ide_cod [OF arr_f]]]
    unfolding d0_nattrafo_def
     apply (simp add: D.ideD(1) [OF D.ide_cod [OF arr_f]])
    unfolding D.dom_cod [OF arr_f] apply simp
    apply (subst Delta.comp_char)
     apply (rule_tac D.seqI')
      apply (rule_tac functor.preserves_hom [OF plusone_functor])
    using D.in_homI [OF arr_f] apply blast
    unfolding Delta.cod_char [OF arr_f]
    apply (subst reverse_equality [OF plusone_Id])
    using arr_f unfolding Delta.arr_char Delta.OrdArr_def
      apply simp
     apply (subst fin_set.Id'_def)
     apply simp
     apply (rule_tac Delta.d_in_hom)
    using arr_f unfolding Delta.arr_char Delta.OrdArr_def
     apply simp
    apply (subst Delta.comp_char)
    using arr_df
    unfolding d0_nattrafo_def
     apply (simp add: arr_f)
    unfolding fin_set.Comp'_def
    apply auto
  proof-
    show "fst (the (plusone_functor f)) = fst (the (Delta.d (fst (the (D.dom f))) 0))"
      unfolding plusone_functor_def Delta.d_def
      apply (simp add: arr_f)
      unfolding Delta.dom_char [OF arr_f]
      unfolding fin_set.Id'_def
      by simp
    show "rev_get
     (length (snd (the (Delta.d (fst (fin_set.Id' (length (snd (the f))))) 0))))
     (\<lambda>n. get (snd (the (plusone_functor f)))
           (get (snd (the (Delta.d (fst (fin_set.Id' (length (snd (the f))))) 0)))
             n)) =
    rev_get (length (snd (the f)))
     (\<lambda>n. get (snd (the (Delta.d (fst (the (D.dom f))) 0))) (get (snd (the f)) n))"
      apply (rule_tac getFaithful)
       apply (simp add: Delta.d_def fin_set.Id'_def)
      apply (simp add: get_rev_get)
      unfolding Delta.dom_char [OF arr_f]
      unfolding Delta.d_def fin_set.Id'_def
      apply (simp add: get_rev_get)
      unfolding plusone_functor_def
      apply (simp add: arr_f get_rev_get)
      apply (subst get_rev_get)
      using arr_f unfolding Delta.arr_char Delta.OrdArr_def
      unfolding fin_set.arr_char fin_set.Arr'_def apply simp
      by simp
  qed
qed


lemma d0_nattrafo_id : assumes "D.ide a"
  shows "d0_nattrafo a = Delta.d (fst (the a)) 0"
  unfolding d0_nattrafo_def
  apply (simp add: \<open>D.ide a\<close>)
  apply (subst D.comp_ide_arr)
  using \<open>D.ide a\<close> apply simp
   apply (rule_tac D.seqI')
    apply (rule_tac Delta.d_in_hom)
    apply (metis D.ideD(1) D.ideD(2) arr_f_n_dom assms)
   apply (subst reverse_equality [OF Delta.dom_char])
  using \<open>D.ide a\<close> apply simp
  using \<open>D.ide a\<close> D.ide_in_hom apply simp
  by simp







end



context pointed_simplicial_set
begin
interpretation simplex.

fun apply_d_list :: "nat list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "apply_d_list [] x = x" |
  "apply_d_list (n # ns) x = (apply_d_list ns (fst (the (X (d (Suc (length ns)) n))) x))" 

lemma apply_d_list_char :
  "x \<in> snd (P.Dom' (the (X (Some (fin_set.Id' (Suc (length xs)))))))  
  \<Longrightarrow> apply_d_list xs x = fst (the (X (X.A.comp_list (d_chain xs (length xs)) 
                       (Some (fin_set.Id' (Suc (length xs))))))) x"
  apply (induction xs arbitrary: x)
   apply simp
proof-
  fix x
  have "X.B.ide (X (Some (fin_set.Id' (Suc 0))))"
    apply (rule_tac X.preserves_ide)
    using ide_Dn by simp
  then have ide_eq: "(X (Some (fin_set.Id' (Suc 0)))) =
             Some (P.Id' (P.Dom' (the (X (Some (fin_set.Id' (Suc 0)))))))"
    unfolding P.ide_char by simp
  show "x \<in> snd (fst (snd (the (X (Some (fin_set.Id' (Suc 0))))))) \<Longrightarrow>
    x = fst (the (X (Some (fin_set.Id' (Suc 0))))) x"
    apply (subst ide_eq)
    unfolding P.Id'_def
    by simp
next
  fix a xs x
  assume ind : "(\<And>x. x \<in> snd (fst (snd (the (X (Some (fin_set.Id' (Suc (length xs)))))))) \<Longrightarrow>
             apply_d_list xs x =
             fst (the (X (X.A.comp_list (d_chain xs (length xs))
                           (Some (fin_set.Id' (Suc (length xs))))))) x)"
  assume x_in_dom: "x \<in> snd (fst (snd (the (X (Some (fin_set.Id' (Suc (length (a # xs)))))))))"

  have seq : "X.A.seq
     (X.A.comp_list (rev_get (length xs) (\<lambda>k. d (length xs - k) (get xs k)))
       (X.A.cod (d (Suc (length xs)) a)))
     (d (Suc (length xs)) a)"
    apply (rule_tac X.A.seqI')
    using d_in_hom apply blast
    apply (subst X.A.in_hom_cod [OF d_in_hom])
     apply simp
    apply (rule_tac X.A.comp_list_in_hom)
    unfolding reverse_equality [OF d_chain.simps]
    apply (rule_tac d_chain_arr)
    by simp

  have arr_d : "X.A.arr (d (Suc (length xs)) a)"
    using d_in_hom by blast

  have x_in_d_dom : "x \<in> snd (fst (snd (the (X (d (Suc (length xs)) a)))))"
    apply (subst P.Dom_dom)
    using X.preserves_arr [OF arr_d] apply simp
    apply (subst X.preserves_dom [OF arr_d])
    apply (subst X.A.in_hom_dom [OF d_in_hom])
     apply simp
    using x_in_dom by simp

  show "apply_d_list (a # xs) x =
       fst (the (X (X.A.comp_list (d_chain (a # xs) (length (a # xs)))
                     (Some (fin_set.Id' (Suc (length (a # xs)))))))) x"
    apply simp
    apply (subst X.preserves_comp [OF seq])
    apply (subst P.fst_comp_char)
      apply (rule_tac X.preserves_seq [OF seq])
     apply (rule_tac x_in_d_dom)
    apply (subst ind)
    using P.arr_x_in_dom [OF X.preserves_arr [OF arr_d] x_in_d_dom]
    unfolding P.Dom_cod [OF X.preserves_arr [OF arr_d]]
    unfolding X.preserves_cod [OF arr_d]
    using X.A.in_hom_cod [OF d_in_hom] apply simp
    apply (subst X.A.in_hom_cod [OF d_in_hom])
    by simp_all
qed
    






definition \<Omega>_obj where
  "\<Omega>_obj k = (fst (simplices (Suc k)), 
         {x \<in> snd (simplices (Suc k)). fst (the (X (d (Suc k) 0))) x = fst (simplices k) \<and>
          (\<forall>ns. length ns = Suc k \<longrightarrow> apply_d_list ns x = fst (simplices 0))})"

lemma \<Omega>_obj: "P.Obj' (\<Omega>_obj k)"
  unfolding P.Obj'_def \<Omega>_obj_def
  apply auto
proof-
  show "fst (simplices (Suc k)) \<in> snd (simplices (Suc k))"
    unfolding simplices_def
    unfolding reverse_equality [OF P.Obj'_def]
    apply (rule_tac classical_category.Obj_Dom [OF P.ccpf])
    using X.preserves_arr [OF X.A.ideD(1) [OF ide_Dn]]
    unfolding P.arr_char by simp
  have "Suc k > 0" by simp
  have "fst (the (X (d (Suc k) 0)))
     (fst (fst (snd (the (X (Some (fin_set.Id' (Suc (Suc k))))))))) =
    fst (fst (snd (the (X (Some (fin_set.Id' (Suc k)))))))"
    using P.in_hom_basepoint_eq 
          [OF X.preserves_hom [OF d_in_hom [OF \<open>Suc k > 0\<close>]]].
  then show "fst (the (X (d (Suc k) 0))) (fst (simplices (Suc k))) 
             = fst (simplices k)"
    unfolding simplices_def
    by simp
  fix ns :: "nat list"
  assume "length ns = Suc k" 
  have "\<And>k. length ns = k \<Longrightarrow>
          apply_d_list ns
           (fst (fst (snd (the (X (Some (fin_set.Id' (Suc k)))))))) =
          fst (fst (snd (the (X (Some (fin_set.Id' (Suc 0)))))))"
    apply (induction ns)
    apply simp
  proof-
    fix a ns k
    assume ind: "(\<And>k. length ns = k \<Longrightarrow>
             apply_d_list ns
              (fst (fst (snd (the (X (Some (fin_set.Id' (Suc k)))))))) =
             fst (fst (snd (the (X (Some (fin_set.Id' (Suc 0))))))))"
    assume "length (a # ns) = k"
    then have "Suc (length ns) = k" by simp
    from reverse_equality [OF this]
    and ind have EQ: "apply_d_list ns
              (fst (fst (snd (the (X (Some (fin_set.Id' k))))))) =
             fst (fst (snd (the (X (Some (fin_set.Id' (Suc 0)))))))"
      by simp
    show "apply_d_list (a # ns)
        (fst (fst (snd (the (X (Some (fin_set.Id' (Suc k)))))))) =
       fst (fst (snd (the (X (Some (fin_set.Id' (Suc 0)))))))"
      unfolding apply_d_list.simps \<open>Suc (length ns) = k\<close>
      apply (subst P.in_hom_basepoint_eq [OF X.preserves_hom [OF d_in_hom]])
      using \<open>Suc (length ns) = k\<close> apply simp
      using EQ.
  qed
  from this and \<open>length ns = Suc k\<close> 
  show "apply_d_list ns (fst (simplices (Suc k))) = fst (simplices 0)"
    unfolding simplices_def
    by simp
qed

end

context begin

interpretation Delta: simplex.
interpretation sSet: functor_category Delta.comp P.pointed_set_comp
  unfolding functor_category_def
  by (simp add: Delta.is_category P.is_category)

interpretation eval : evaluation_functor Delta.comp P.pointed_set_comp
  unfolding evaluation_functor_def
  unfolding functor_category_def product_category_def
  by (simp add: Delta.is_category P.is_category sSet.is_category)

interpretation IdxPlusone: product_functor sSet.comp Delta.comp sSet.comp Delta.comp
               "(identity_functor.map sSet.comp)"
               plusone_functor
  unfolding product_functor_def
  unfolding product_category_def
  apply (simp add: sSet.is_category Delta.is_category)
  by (simp add: plusone_functor sSet.is_functor)




definition \<Omega>_obj where
  "\<Omega>_obj f = pointed_simplicial_set.\<Omega>_obj (sSet.Fun (fst f)) 
             (fst (the (snd f))-1)"

interpretation \<Omega>_curried : sub_functor eval.A_BxA.comp 
                    "eval.map \<circ> IdxPlusone.map"  \<Omega>_obj
  unfolding sub_functor_def
  apply safe
   apply (rule_tac functor_comp)
  using IdxPlusone.is_functor apply simp
  using eval.is_functor apply simp
  unfolding sub_functor_axioms_def
  apply auto
proof-
  fix a :: "((nat \<times> nat list) option,
       (('a \<Rightarrow> 'a) \<times> ('a \<times> 'a set) \<times> 'a \<times> 'a set) option) sSet.arr" 
  fix b :: "(nat \<times> nat list) option"
  assume "a \<noteq> sSet.null"
  assume "functor Delta.comp P.pointed_set_comp (sSet.Fun a)"
  then interpret S: pointed_simplicial_set "sSet.Fun a"
    unfolding pointed_simplicial_set_def.
  assume "sSet.Dom a = sSet.Fun a" "sSet.Cod a = sSet.Fun a"
  have "sSet.ide a"
    unfolding sSet.ide_char
    using \<open>a \<noteq> sSet.null\<close> \<open>functor Delta.comp P.pointed_set_comp (sSet.Fun a)\<close>
          \<open>sSet.Dom a = sSet.Fun a\<close> \<open>sSet.Cod a = sSet.Fun a\<close> by simp

  assume "sSet.A.ide b"
  then have eqb1: "Delta.OrdArr b \<and> b = Some (fin_set.Id' (length (snd (the b))))"
    unfolding Delta.ide_char.
  have "fst (the b) = length (snd (the b))"
    apply (subst eqb1)
    unfolding fin_set.Id'_def by simp
  from this and eqb1 have eqb2: "b = Some (fin_set.Id' (fst (the b)))"
    by simp
  have "0 < fst (the b)"
    using eqb1
    unfolding Delta.OrdArr_def
    unfolding \<open>fst (the b) = length (snd (the b))\<close>
    by simp

  show "P.Obj' (\<Omega>_obj (a, b))"
    unfolding \<Omega>_obj_def apply simp
    using S.\<Omega>_obj.
  show "pointed_subset (fst (snd (the (eval.map (a, plusone_functor b)))))
            (\<Omega>_obj (a, b))"
    apply (subst eval.map_simp)
    using \<open>sSet.ide a\<close> \<open>sSet.A.ide b\<close> apply simp
    unfolding \<Omega>_obj_def
    apply simp
    apply (subst eqb2)
    apply (subst reverse_equality [OF plusone_Id])
    using \<open>0 < fst (the b)\<close> apply simp
    unfolding S.\<Omega>_obj_def pointed_subset_def
    using \<open>0 < fst (the b)\<close> S.simplices_def
    by auto
next
  fix a b x
  assume "sSet.arr a"
  then interpret a_nat : natural_transformation Delta.comp P.pointed_set_comp 
    "(sSet.Dom a)" "(sSet.Cod a)" "(sSet.Fun a)"
    unfolding sSet.arr_char by simp
  interpret S : pointed_simplicial_set "(sSet.Dom a)"
    unfolding pointed_simplicial_set_def
    using a_nat.F.functor_axioms.
  interpret T : pointed_simplicial_set "(sSet.Cod a)"
    unfolding pointed_simplicial_set_def
    using a_nat.G.functor_axioms.
  assume "sSet.A.arr b"
  then have "snd (the b) \<noteq> []"
    unfolding Delta.arr_char
    unfolding Delta.OrdArr_def by simp
  have "get (snd (the b)) 0 < fst (the b)"
    using \<open>sSet.A.arr b\<close>
    unfolding Delta.arr_char
    unfolding Delta.OrdArr_def
    unfolding fin_set.arr_char
    unfolding fin_set.Arr'_def
    by simp
  then have "0 < fst (the (sSet.A.dom b))"
    apply (subst Delta.dom_char [OF \<open>sSet.A.arr b\<close>])
    unfolding fin_set.Id'_def
    by simp
  then have S_simplex_simp : "S.simplices (fst (the (sSet.A.dom b))) = 
              fst (snd (the (sSet.Dom a (plusone_functor (sSet.A.dom b)))))"
    unfolding S.simplices_def
    apply (subst plusone_Id)
     apply simp
    apply (subst reverse_equality [OF Delta.dom_char])
    using sSet.A.ide_dom [OF \<open>sSet.A.arr b\<close>] apply simp
    unfolding sSet.A.dom_dom [OF \<open>sSet.A.arr b\<close>]
    by simp

  then have "0 < fst (the (sSet.A.cod b))"
    unfolding Delta.cod_char [OF \<open>sSet.A.arr b\<close>]
    unfolding fin_set.Id'_def
    using \<open>snd (the b) \<noteq> []\<close> by simp
  then have T_simplex_simp : "T.simplices (fst (the (sSet.A.cod b))) = 
              fst (snd (the (sSet.Cod a (plusone_functor (sSet.A.cod b)))))"
    unfolding T.simplices_def
    apply (subst plusone_Id)
     apply simp
    apply (subst reverse_equality [OF Delta.dom_char])
    using sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>] apply simp
    unfolding sSet.A.dom_cod [OF \<open>sSet.A.arr b\<close>]
    by simp

  assume "x \<in> snd (\<Omega>_obj (sSet.dom a, sSet.A.dom b))"
  then have x_in_\<Omega>: 
    "x \<in> snd (S.simplices (fst (the (sSet.A.dom b)))) \<and>
    fst (the (sSet.Dom a (Delta.d (fst (the (sSet.A.dom b))) 0)))
     x = fst (S.simplices (fst (the (sSet.A.dom b)) - Suc 0)) \<and>
    (\<forall>ns. length ns = (fst (the (sSet.A.dom b))) \<longrightarrow>
          S.apply_d_list ns x = fst (S.simplices 0))"
    unfolding \<Omega>_obj_def apply (simp add: sSet.Fun_dom [OF \<open>sSet.arr a\<close>])
    unfolding S.\<Omega>_obj_def 
    using \<open>0 < fst (the (sSet.A.dom b))\<close> by simp

  show "fst (the (eval.map (a, plusone_functor b))) x
       \<in> snd (\<Omega>_obj (sSet.cod a, sSet.A.cod b))"
    apply (subst eval.map_simp)
     apply (simp add: \<open>sSet.arr a\<close> \<open>sSet.A.arr b\<close>)
    unfolding \<Omega>_obj_def apply simp
    unfolding sSet.Fun_cod [OF \<open>sSet.arr a\<close>]
    unfolding T.\<Omega>_obj_def
    using \<open>0 < fst (the (sSet.A.cod b))\<close> apply auto
  proof-
    show fx_in_Ts: "fst (the (sSet.Fun a (plusone_functor b))) x
    \<in> snd (T.simplices (fst (the (sSet.A.cod b))))"
      apply (rule_tac P.arr_x_in_dom')
         apply (rule_tac a_nat.preserves_arr 
                     [OF functor.preserves_arr 
                     [OF plusone_functor \<open>sSet.A.arr b\<close>]])
    proof-
      show "x \<in> snd (S.simplices (fst (the (sSet.A.dom b))))"
        using conjunct1 [OF x_in_\<Omega>].
      show "snd (snd (the (sSet.Fun a (plusone_functor b)))) =
    T.simplices (fst (the (sSet.A.cod b)))"
      unfolding T_simplex_simp
       apply (subst reverse_equality [OF functor.preserves_cod 
                      [OF plusone_functor \<open>sSet.A.arr b\<close>]])
       apply (subst reverse_equality [OF a_nat.preserves_cod])
      apply (rule_tac functor.preserves_arr
                      [OF plusone_functor \<open>sSet.A.arr b\<close>])
       apply (subst P.cod_char)
      apply (rule_tac a_nat.preserves_arr [OF functor.preserves_arr
                      [OF plusone_functor \<open>sSet.A.arr b\<close>]])
      unfolding P.Id'_def by simp
    show "fst (snd (the (sSet.Fun a (plusone_functor b)))) =
    S.simplices (fst (the (sSet.A.dom b)))"
      unfolding S_simplex_simp
       apply (subst reverse_equality [OF functor.preserves_dom 
                      [OF plusone_functor \<open>sSet.A.arr b\<close>]])
       apply (subst reverse_equality [OF a_nat.preserves_dom])
      apply (rule_tac functor.preserves_arr
                      [OF plusone_functor \<open>sSet.A.arr b\<close>])
       apply (subst P.dom_char)
      apply (rule_tac a_nat.preserves_arr [OF functor.preserves_arr
                      [OF plusone_functor \<open>sSet.A.arr b\<close>]])
      unfolding P.Id'_def by simp
  qed


  interpret a_d0 : horizontal_composite Delta.comp Delta.comp pointed_set.pointed_set_comp
     plusone_functor sSet.A.map "(sSet.Dom a)" "(sSet.Cod a)" 
                                "d0_nattrafo" "(sSet.Fun a)"
    unfolding horizontal_composite_def
    using a_nat.natural_transformation_axioms
          d0_nattrafo
    unfolding natural_transformation_def
    by auto

  have interchange: "pointed_set.pointed_set_comp ((sSet.Fun a \<circ> sSet.A.map) (sSet.A.cod b))
   ((sSet.Dom a \<circ> d0_nattrafo) b) =
  pointed_set.pointed_set_comp ((sSet.Cod a \<circ> d0_nattrafo) (sSet.A.cod b))
   ((sSet.Fun a \<circ> plusone_functor) b)"
    using a_d0.interchange_fun [OF \<open>sSet.A.arr b\<close>].

  have eq1: "(pointed_set.pointed_set_comp
               (sSet.Cod a (Delta.d (fst (the (sSet.A.cod b))) 0))
               (sSet.Fun a (plusone_functor b))) = 
       pointed_set.pointed_set_comp ((sSet.Cod a \<circ> d0_nattrafo) (sSet.A.cod b))
              ((sSet.Fun a \<circ> plusone_functor) b)"
    unfolding d0_nattrafo_def
    apply (simp add: sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>])
    apply (subst sSet.A.comp_ide_arr)
    using sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>] apply simp
     apply (rule_tac sSet.A.seqI')
      apply (rule_tac Delta.d_in_hom)
    using \<open>0 < fst (the (sSet.A.cod b))\<close> apply simp
     apply (rule_tac sSet.A.in_homI)
    using sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>] apply simp
      apply (subst reverse_equality [OF Delta.dom_char])
    using sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>] apply simp
      apply simp
     apply simp
    by simp

  have seq1: "sSet.B.seq (sSet.Cod a (Delta.d (fst (the (sSet.A.cod b))) 0))
     (sSet.Fun a (plusone_functor b))"
     apply (rule_tac sSet.B.seqI')
     apply (rule_tac a_nat.preserves_hom)
     apply (rule_tac functor.preserves_hom [OF plusone_functor])
    using sSet.A.in_homI [OF \<open>sSet.A.arr b\<close>] apply blast
     apply (rule_tac a_nat.G.preserves_hom)
     apply (subst Delta.cod_char [OF \<open>sSet.A.arr b\<close>])
     apply (subst Delta.cod_char [OF \<open>sSet.A.arr b\<close>])
     apply (subst reverse_equality [OF plusone_Id])
    using \<open>sSet.A.arr b\<close>
    unfolding Delta.arr_char Delta.OrdArr_def apply simp
     apply (subst fin_set.Id'_def)
     apply simp
     apply (rule_tac Delta.d_in_hom)
    using \<open>sSet.A.arr b\<close>
    unfolding Delta.arr_char Delta.OrdArr_def by simp
  have seq2 : "sSet.A.seq b (Delta.d (fst (the (sSet.A.dom b))) 0)"
    apply (rule_tac sSet.A.seqI')
     apply (rule_tac Delta.d_in_hom)
    using \<open>0 < fst (the (sSet.A.dom b))\<close> apply simp
    apply (subst reverse_equality [OF Delta.dom_char])
    using sSet.A.ide_dom [OF \<open>sSet.A.arr b\<close>] apply simp
    unfolding sSet.A.dom_dom [OF \<open>sSet.A.arr b\<close>]
    using \<open>sSet.A.arr b\<close> by blast

  have seq3 : "sSet.B.seq ((sSet.Fun a \<circ> sSet.A.map) (sSet.A.cod b))
     ((sSet.Dom a \<circ> d0_nattrafo) b)"
    unfolding sSet.A.map_def d0_nattrafo_def
    apply (simp add: \<open>sSet.A.arr b\<close>)
    apply (rule_tac sSet.B.seqI)
      apply (rule_tac a_nat.F.preserves_arr)
    using seq2 apply simp
     apply (rule_tac a_nat.preserves_arr)
    using sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>] apply simp
    apply (subst a_nat.F.preserves_cod)
    using seq2 apply simp
    apply (subst sSet.A.cod_comp)
    using seq2 apply simp
    apply (subst a_nat.preserves_dom)
    using sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>] apply simp
    using sSet.A.dom_cod [OF \<open>sSet.A.arr b\<close>] by simp
  have "sSet.B.dom (sSet.Dom a (sSet.A.dom (d0_nattrafo b))) =
        sSet.B.dom (sSet.Dom a (d0_nattrafo b))"
    apply (subst reverse_equality [OF a_nat.F.preserves_dom])
     apply (rule_tac a_d0.\<sigma>.preserves_arr [OF \<open>sSet.A.arr b\<close>])
    apply (rule_tac sSet.B.dom_dom)
    using a_nat.F.preserves_arr [OF a_d0.\<sigma>.preserves_arr [OF \<open>sSet.A.arr b\<close>]].
  then have dom_eq2 : "(S.simplices (fst (the (sSet.A.dom b)))) =
                 (fst (snd (the ((sSet.Dom a \<circ> d0_nattrafo) b))))"
    unfolding S_simplex_simp
    unfolding reverse_equality [OF a_d0.\<sigma>.preserves_dom [OF \<open>sSet.A.arr b\<close>]]
    unfolding P.dom_char [OF a_nat.F.preserves_arr 
          [OF sSet.A.ideD(1) [OF sSet.A.ide_dom 
          [OF a_d0.\<sigma>.preserves_arr [OF \<open>sSet.A.arr b\<close>]]]]]
    unfolding P.dom_char [OF a_nat.F.preserves_arr 
          [OF a_d0.\<sigma>.preserves_arr [OF \<open>sSet.A.arr b\<close>]]]
    by (simp add: P.Id'_def)

  show "fst (the (sSet.Cod a (Delta.d (fst (the (sSet.A.cod b))) 0)))
     (fst (the (sSet.Fun a (plusone_functor b))) x) =
    fst (T.simplices (fst (the (sSet.A.cod b)) - Suc 0))"
    apply (subst reverse_equality [OF P.fst_comp_char])
      apply (simp add: seq1)
     apply (rule_tac transport [OF conjunct1 [OF x_in_\<Omega>]])
    unfolding S_simplex_simp
    unfolding reverse_equality [OF functor.preserves_dom 
                  [OF plusone_functor \<open>sSet.A.arr b\<close>]]
     apply (subst reverse_equality [OF a_nat.preserves_dom])
      apply (rule_tac functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>])
     apply (subst P.dom_char)
    using a_nat.preserves_arr [OF functor.preserves_arr 
                     [OF plusone_functor \<open>sSet.A.arr b\<close>]] apply simp
     apply (simp add: P.Id'_def)
    apply (subst eq1)
    apply (subst reverse_equality [OF interchange])
    apply (subst P.fst_comp_char)
    using seq3 apply simp
    unfolding reverse_equality [OF dom_eq2] 
    using x_in_\<Omega> apply simp
    unfolding d0_nattrafo_def
    apply (simp add: \<open>sSet.A.arr b\<close>)
    apply (subst functor.preserves_comp [OF S.is_functor])
    using seq2 apply simp
    apply (subst P.fst_comp_char)
      apply (rule_tac a_nat.F.preserves_seq)
    using seq2 apply simp
     apply (rule_tac transport [OF conjunct1 [OF x_in_\<Omega>]])
    unfolding S_simplex_simp
     apply (subst reverse_equality [OF d0_nattrafo_id])
    using sSet.A.ide_dom [OF \<open>sSet.A.arr b\<close>] apply simp
    apply (rule_tac reverse_equality)
     apply (subst P.Dom_dom)
      apply (rule_tac a_nat.F.preserves_arr [OF a_d0.\<sigma>.preserves_arr])
    using sSet.A.ide_dom [OF \<open>sSet.A.arr b\<close>] apply simp
     apply (subst a_nat.F.preserves_dom)
      apply (rule_tac a_d0.\<sigma>.preserves_arr)
    using sSet.A.ide_dom [OF \<open>sSet.A.arr b\<close>] apply simp
     apply (subst a_d0.\<sigma>.preserves_dom)
    using sSet.A.ide_dom [OF \<open>sSet.A.arr b\<close>] apply simp
    unfolding sSet.A.dom_dom [OF \<open>sSet.A.arr b\<close>]
     apply simp
  proof-
    define dummy where "dummy = sSet.A.cod b"
    show "fst (the (sSet.Fun a (sSet.A.cod b)))
     (fst (the (sSet.Dom a b))
       (fst (the (sSet.Dom a (Delta.d (fst (the (sSet.A.dom b))) 0))) x)) =
    fst (T.simplices (fst (the (sSet.A.cod b)) - Suc 0))"
      apply (subst conjunct1 [OF conjunct2 [OF x_in_\<Omega>]])
      unfolding S.simplices_def
      using \<open>0 < fst (the (sSet.A.dom b))\<close> apply simp
      apply (subst reverse_equality [OF Delta.dom_char])
      using sSet.A.ide_dom [OF \<open>sSet.A.arr b\<close>] apply simp
      unfolding sSet.A.dom_dom [OF \<open>sSet.A.arr b\<close>]
      apply (subst P.in_hom_basepoint_eq)
       apply (rule_tac a_nat.F.preserves_hom)
      using sSet.A.in_homI [OF \<open>sSet.A.arr b\<close>] apply blast
      apply (subst reverse_equality [OF dummy_def])
      apply (subst reverse_equality [OF sSet.A.dom_cod [OF \<open>sSet.A.arr b\<close>]])
      unfolding dummy_def
      apply (subst reverse_equality [OF a_nat.preserves_dom])
      using sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>] apply simp
      apply (subst P.in_hom_basepoint_eq)
      using sSet.B.in_homI [OF a_nat.preserves_arr 
      [OF sSet.A.ideD(1) [OF sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>]]]]
       apply blast
      unfolding T.simplices_def
      using \<open>0 < fst (the (sSet.A.cod b))\<close> apply simp
      apply (subst reverse_equality [OF Delta.dom_char])
      using sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>] apply simp
      apply (subst a_nat.preserves_cod)
      using sSet.A.ide_cod [OF \<open>sSet.A.arr b\<close>] apply simp
      unfolding sSet.A.dom_cod [OF \<open>sSet.A.arr b\<close>]
      unfolding sSet.A.cod_cod [OF \<open>sSet.A.arr b\<close>]
      by simp
  qed
  fix ns :: "nat list"

  assume "length ns = fst (the (sSet.A.cod b))"
  then have "length ns = length (snd (the b))"
    unfolding Delta.cod_char [OF \<open>sSet.A.arr b\<close>] 
    unfolding fin_set.Id'_def by simp 

  define k where "k = (get (snd (the (sSet.A.comp_list (Delta.d_chain ns (length ns))
                      (Some (fin_set.Id' (Suc (length ns)))))))  0)"

  have k_bound: "k < Suc (length (snd (the b)))"
    unfolding k_def
    apply (rule_tac Delta.in_hom_get_bound)
    unfolding reverse_equality [OF \<open>length ns = length (snd (the b))\<close>]
     apply (rule_tac sSet.A.comp_list_in_hom)
     apply (rule_tac Delta.d_chain_arr)
    by simp_all

  have "length ns \<le> length ns" by simp
  have d_to_inc : "(sSet.A.comp_list (Delta.d_chain ns (length ns))
       (Some (fin_set.Id' (Suc (length ns))))) = Delta.inc k (Suc (length ns))"
    apply (subst Delta.arr_to_inc)
     apply (rule_tac sSet.A.comp_list_in_hom)
    using Delta.d_chain_arr [OF \<open>length ns \<le> length ns\<close>] apply simp
    unfolding reverse_equality [OF k_def]
    unfolding fin_set.Id'_def by simp
  have arr_inc : "sSet.A.arr (Delta.inc k (Suc (length ns)))"
    using Delta.inc_in_hom [OF k_bound]
    unfolding reverse_equality [OF \<open>length ns = length (snd (the b))\<close>]
    by blast

  assume "0 < fst (the (sSet.A.cod b))"
  then have " 0 < length (snd (the b))"
    unfolding Delta.cod_char [OF \<open>sSet.A.arr b\<close>]
    unfolding fin_set.Id'_def by simp
  have "get (snd (the b)) 0 < fst (the b)"
    using \<open>sSet.A.arr b\<close>
    unfolding Delta.arr_char Delta.OrdArr_def fin_set.arr_char fin_set.Arr'_def
    using \<open>0 < length (snd (the b))\<close> by simp
  then have "0 < fst (the b)" by simp

  have eq1: "(sSet.A.cod (plusone_functor b)) = sSet.A.dom (Delta.inc k (Suc (length ns)))"
    apply (subst sSet.A.in_hom_dom [OF Delta.inc_in_hom])
    using k_bound \<open>length ns = length (snd (the b))\<close>
    apply simp
    apply (subst Delta.cod_char)
    using functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>] apply simp
    unfolding plusone_functor_def
    apply (simp add: \<open>sSet.A.arr b\<close>)
    using \<open>length ns = length (snd (the b))\<close> by simp
  have seq1 : "sSet.A.seq (Delta.inc k (Suc (length ns))) (plusone_functor b)"
    apply (rule_tac sSet.A.seqI)
    using functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>] apply simp
    using arr_inc apply simp
    using eq1 by simp

  define l where "l = (get (snd (the (Delta.comp (Delta.inc k (Suc (length ns))) 
                       (plusone_functor b)))) 0)"

  have inc_eq : "(Delta.comp (Delta.inc k (Suc (length ns))) (plusone_functor b)) =
                 Delta.inc l (Suc (fst (the b)))"
    apply (subst Delta.arr_to_inc [OF sSet.A.comp_in_homI])
    using functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>] apply blast
    unfolding eq1
     apply (subst Delta.dom_char)
    using arr_inc apply simp
    using Delta.inc_in_hom [OF k_bound]
    unfolding \<open>length ns = length (snd (the b))\<close>
     apply (simp add: Delta.inc_def)
    unfolding functor.preserves_dom [OF plusone_functor \<open>sSet.A.arr b\<close>]
    unfolding Delta.dom_char [OF \<open>sSet.A.arr b\<close>]
    apply (subst reverse_equality [OF plusone_Id])
    using \<open>0 < fst (the b)\<close> apply simp
    unfolding l_def \<open>length ns = length (snd (the b))\<close>
    unfolding fin_set.Id'_def by simp

  have l_bound : "l < Suc (fst (the b))" 
    unfolding l_def
    apply (rule_tac Delta.in_hom_get_bound)
    apply (rule_tac sSet.A.in_homI [OF seq1])
      apply (subst sSet.A.dom_comp [OF seq1])
      apply (subst plusone_Id)
    using \<open>0 < fst (the b)\<close> apply simp
    apply (subst functor.preserves_dom [OF plusone_functor \<open>sSet.A.arr b\<close>])
    using Delta.dom_char [OF \<open>sSet.A.arr b\<close>] apply simp
     apply (subst sSet.A.cod_comp [OF seq1])
     apply (rule_tac sSet.A.in_hom_cod [OF Delta.inc_in_hom])
    using k_bound \<open>length ns = length (snd (the b))\<close> apply simp
    by simp
  have inc_to_d : "\<exists>xs. length xs = fst (the b) \<and> (Delta.inc l (Suc (fst (the b)))) =
       sSet.A.comp_list (Delta.d_chain xs (fst (the b))) (Some (fin_set.Id' (Suc (fst (the b)))))"
    apply (rule_tac Delta.inc_to_d_chain)
    using l_bound by simp
  then obtain xs where xs_def: "length xs = fst (the b) \<and>  (Delta.inc l (Suc (fst (the b)))) =
       sSet.A.comp_list (Delta.d_chain xs (fst (the b))) (Some (fin_set.Id' (Suc (fst (the b)))))"
    by auto


  have xs_fst_eq : "(S.apply_d_list xs x) = fst (S.simplices 0)"
    using conjunct2 [OF conjunct2 [OF x_in_\<Omega>]]
          conjunct1 [OF xs_def]
    unfolding Delta.dom_char [OF \<open>sSet.A.arr b\<close>]
    unfolding fin_set.Id'_def
    by simp

  have x_in_1 : "x \<in> snd (fst (snd (the (sSet.Fun a (plusone_functor b)))))"
    apply (rule_tac transport [OF conjunct1 [OF x_in_\<Omega>]])
    unfolding S_simplex_simp
    apply (subst reverse_equality [OF functor.preserves_dom [OF plusone_functor]])
     apply (simp add: \<open>sSet.A.arr b\<close>)
    apply (subst reverse_equality [OF a_nat.preserves_dom])
    using functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>] apply simp
    using P.Dom_dom [OF a_nat.preserves_arr [OF 
          functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>]]] by simp


  show "0 < fst (the (sSet.A.cod b)) \<Longrightarrow>
          length ns = fst (the (sSet.A.cod b)) \<Longrightarrow>
          T.apply_d_list ns (fst (the (sSet.Fun a (plusone_functor b))) x) =
          fst (T.simplices 0)"
    apply (subst T.apply_d_list_char)
    using fx_in_Ts
    unfolding T.simplices_def
    unfolding Delta.cod_char [OF \<open>sSet.A.arr b\<close>]
     apply (simp add: fin_set.Id'_def)
    apply (subst d_to_inc)
    apply (subst reverse_equality [OF P.fst_comp_char])
      apply (rule_tac sSet.B.seqI')
       apply (rule_tac a_nat.preserves_hom)
       apply (rule_tac functor.preserves_hom [OF plusone_functor])
    using \<open>sSet.A.arr b\<close> apply blast
      apply (rule_tac a_nat.G.preserves_hom)
      apply (subst Delta.cod_char [OF \<open>sSet.A.arr b\<close>])
      apply (subst reverse_equality [OF plusone_Id])
       apply (simp add: fin_set.Id'_def)
      apply simp
      apply (subst fin_set.Id'_def)
    apply simp
      apply (rule_tac Delta.inc_in_hom)
      apply (simp add: k_bound)
    using x_in_1 apply simp
    unfolding reverse_equality [OF a_nat.is_natural_2 [OF 
          functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>]]]
    apply (subst eq1)
    unfolding reverse_equality [OF sSet.B.comp_assoc]
    apply (subst a_nat.is_natural_1 [OF arr_inc])
    apply (subst reverse_equality [OF a_nat.is_natural_2 [OF arr_inc]])
    unfolding sSet.B.comp_assoc
    apply (subst reverse_equality [OF a_nat.F.preserves_comp [OF seq1]])
    apply (subst P.fst_comp_char)
      apply (rule_tac sSet.B.seqI')
       apply (rule_tac a_nat.F.preserves_hom)
    using seq1 apply blast
      apply (rule_tac a_nat.preserves_hom)
      apply (subst sSet.A.cod_comp)
    using seq1 apply simp
      apply (subst reverse_equality [OF sSet.A.ide_in_hom])
      apply (rule_tac sSet.A.ide_cod)
    using arr_inc apply simp
     apply (subst P.Dom_dom)
      apply (rule_tac a_nat.F.preserves_arr [OF seq1])
     apply (subst a_nat.F.preserves_dom [OF seq1])
     apply (subst sSet.A.dom_comp [OF seq1])
     apply (subst reverse_equality [OF a_nat.preserves_dom])
    using functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>] apply simp
     apply (subst reverse_equality [OF P.Dom_dom])
    using a_nat.preserves_arr [OF 
          functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>]] apply simp
    using x_in_1 apply simp
    apply (subst inc_eq)
    apply (subst conjunct2 [OF xs_def])
    unfolding reverse_equality [OF conjunct1 [OF xs_def]]
    apply (subst reverse_equality [OF S.apply_d_list_char])
     apply (subst plusone_Id)
    using reverse_equality [OF conjunct1 [OF xs_def]] \<open>0 < fst (the b)\<close> apply simp
     apply (subst conjunct1 [OF xs_def])
     apply (subst reverse_equality [OF Delta.dom_char [OF \<open>sSet.A.arr b\<close>]])
    apply (subst reverse_equality [OF functor.preserves_dom 
                 [OF plusone_functor \<open>sSet.A.arr b\<close>]])
     apply (subst reverse_equality [OF a_nat.preserves_dom])
    using functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>] apply simp
     apply (subst reverse_equality [OF P.Dom_dom])
    using a_nat.preserves_arr [OF 
          functor.preserves_arr [OF plusone_functor \<open>sSet.A.arr b\<close>]] apply simp
    using x_in_1 apply simp
    apply (subst xs_fst_eq)
    unfolding S.simplices_def
    apply (rule_tac P.in_hom_basepoint_eq)
    apply (rule_tac a_nat.preserves_hom)
    apply (subst sSet.A.in_hom_cod [OF Delta.inc_in_hom])
    using k_bound \<open>length ns = length (snd (the b))\<close> apply simp
    apply simp
    unfolding reverse_equality [OF sSet.A.ide_in_hom]
    using Delta.ide_Dn by simp
qed
qed
      


interpretation \<Omega> : curried_functor sSet.comp Delta.comp P.pointed_set_comp
                    \<Omega>_curried.map
  unfolding curried_functor_def
  using \<Omega>_curried.is_functor
  unfolding binary_functor_def functor_category_def currying_def product_category_def
  by (simp add: sSet.is_category Delta.is_category P.is_category)




abbreviation \<Omega> where
  "\<Omega> \<equiv> \<Omega>.map"

lemma \<Omega>_functor : "functor sSet.comp sSet.comp \<Omega>"
  using \<Omega>.is_functor.

lemma \<Omega>_on_obj :
  assumes "sSet.ide c" "sSet.A.ide k"
  shows "sSet.Fun (\<Omega> c) k = Some (P.Id' (\<Omega>_obj (c, k)))"
  apply (subst reverse_equality [OF \<Omega>_curried.on_obj])
  unfolding eval.A_BxA.ide_char
  using assms apply simp
proof-
  have "sSet.arr (\<Omega> c)"
    apply (rule_tac functor.preserves_arr [OF \<Omega>.is_functor])
    using assms by simp
  then show "sSet.Fun (\<Omega> c) k = \<Omega>_curried.map (c, k)"
    unfolding \<Omega>.map_simp [OF sSet.ideD(1) [OF assms(1)]]
    using assms by simp
qed








fun \<Omega>_tothe :: "nat \<Rightarrow> (gamma, 'a P.parr option) sSet.arr
      \<Rightarrow> (gamma, 'a P.parr option) sSet.arr" where
  "\<Omega>_tothe 0 = sSet.map" |
  "\<Omega>_tothe (Suc n) = \<Omega>.map \<circ> (\<Omega>_tothe n)"

lemma \<Omega>_tothe_functor : "functor sSet.comp sSet.comp (\<Omega>_tothe n)"
  apply (induction n)
   apply (simp add: sSet.is_functor)
  unfolding \<Omega>_tothe.simps
  apply (rule_tac functor_comp)
   apply simp
  using \<Omega>.is_functor.



end


locale \<Omega>_obj_theorem =
  X : pointed_simplicial_set X
  for X :: "(nat \<times> nat list) option \<Rightarrow> (('a \<Rightarrow> 'a) \<times> ('a \<times> 'a set) \<times> 'a \<times> 'a set) option"
begin

interpretation Delta: simplex.
interpretation sSet: functor_category Delta.comp P.pointed_set_comp
  unfolding functor_category_def
  by (simp add: Delta.is_category P.is_category)

interpretation \<Omega>X : pointed_simplicial_set "(sSet.Fun (\<Omega> (sSet.mkIde X)))"
proof-
  have "sSet.ide (sSet.mkIde X)"
    apply (rule_tac sSet.ide_mkIde)
    using X.X.functor_axioms.
  then have "sSet.ide (\<Omega> (sSet.mkIde X))"
    using functor.preserves_ide [OF \<Omega>_functor]
    by simp
  then show "pointed_simplicial_set (sSet.Fun (\<Omega> (sSet.mkIde X)))"
    unfolding pointed_simplicial_set_def
    unfolding sSet.ide_char
    by simp
qed

lemma \<Omega>_simplices : "\<Omega>X.simplices k = 
     (fst (X.simplices (Suc k)),
     {x \<in> snd (X.simplices (Suc k)).
      fst (the (X (Delta.d (Suc k) 0))) x = fst (X.simplices k) \<and>
      (\<forall>ns. length ns = Suc k \<longrightarrow> X.apply_d_list ns x = fst (X.simplices 0))})"
  unfolding reverse_equality [OF X.\<Omega>_obj_def]
  unfolding \<Omega>X.simplices_def
  apply (subst \<Omega>_on_obj)
    apply (rule_tac sSet.ide_mkIde)
    apply (rule_tac X.X.functor_axioms)
  using Delta.ide_Dn apply simp
  apply (simp add: P.Id'_def)
  unfolding \<Omega>_obj_def
  apply (simp add: fin_set.Id'_def)
  apply (subst sSet.Fun_mkArr)
   apply simp_all
  using X.X.functor_axioms by simp

  



end



end
