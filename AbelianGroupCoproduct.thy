theory AbelianGroupCoproduct
  imports AbelianGroups
          ColimitFunctoriality
          "Category3.NaturalTransformation"
begin





locale comm_group_hom =
  G: comm_group G +
  H: comm_group H
  for G :: "('a, 'b) monoid_scheme"
  and H :: "('c, 'd) monoid_scheme"
  and f :: "'a \<Rightarrow> 'c" +
assumes f_hom : "f \<in> hom G H"
begin
interpretation F: group_hom G H f
  unfolding group_hom_def
  unfolding group_hom_axioms_def
  by (simp add: f_hom)

lemma is_group_hom : "group_hom G H f"
  using F.group_hom_axioms.


lemma preserves_carrier : "x \<in> carrier G \<Longrightarrow> f x \<in> carrier H"
  using F.hom_closed.


lemma preserves_finset_sum:
  assumes "finite A"
  shows "\<forall>x \<in> A. g x \<in> carrier G \<Longrightarrow> 
         f (G.finset_sum A g) = H.finset_sum A (f \<circ> g)"
proof-
  have "(\<forall>x \<in> A. g x \<in> carrier G) \<longrightarrow>
         f (G.finset_sum A g) = H.finset_sum A (f \<circ> g)"
    apply (rule_tac finite_induct' [OF \<open>finite A\<close>])
    unfolding G.finset_sum_empty H.finset_sum_empty
     apply auto
  proof-
    fix A a
    assume ind: "f (G.finset_sum A g) = H.finset_sum A (\<lambda>a. f (g a))"
    assume "finite A"
    assume ga_G: "g a \<in> carrier G"
    assume gA_G: "\<forall>x\<in>A. g x \<in> carrier G"
    have sum_G : "G.finset_sum A g \<in> carrier G"
      apply (rule_tac G.finset_sum_carrier)
      using \<open>finite A\<close> gA_G.
    assume "a \<notin> A"
    show "f (G.finset_sum (insert a A) g) = 
            H.finset_sum (insert a A) (\<lambda>a. f (g a))"
      apply (subst G.finset_sum_insert')
         apply (simp_all add: \<open>finite A\<close> ga_G gA_G \<open>a \<notin> A\<close>)
      apply (simp add: sum_G ga_G)
      apply (subst H.finset_sum_insert')
         apply (simp_all add: \<open>finite A\<close> ga_G gA_G \<open>a \<notin> A\<close>)
      unfolding ind
      by simp
  qed
  then show "\<forall>x\<in>A. g x \<in> carrier G
       \<Longrightarrow> f (G.finset_sum A g) = H.finset_sum A (f \<circ> g)"
    by simp
qed

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



term "comm_group.finset_sum (coproduct_of_A S)"

lemma coproduct_generated:
  assumes x_in: "x \<in> coproduct_carrier S"
  shows "x = comm_group.finset_sum (coproduct_of_A S) {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>} 
             (\<lambda>s\<in>S. fst (the (coproduct_inclusion S s)) (A_to_obj (x s)))"
proof-
  interpret cS : comm_group "(coproduct_of_A S)"
    using coproduct_comm_group.
  have "\<And>C. finite C \<Longrightarrow>
       \<forall>x. x \<in> coproduct_carrier S \<longrightarrow> {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>} = C \<longrightarrow>
          x = comm_group.finset_sum (coproduct_of_A S) {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>} 
             (\<lambda>s\<in>S. fst (the (coproduct_inclusion S s)) (A_to_obj (x s)))"
  proof-
    fix C :: "'c set"
    assume "finite C"
    show "\<forall>x. x \<in> coproduct_carrier S \<longrightarrow> {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>} = C \<longrightarrow>
          x = comm_group.finset_sum (coproduct_of_A S) {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>} 
             (\<lambda>s\<in>S. fst (the (coproduct_inclusion S s)) (A_to_obj (x s)))"  
      apply (rule_tac finite_induct' [OF \<open>finite C\<close>])
       apply auto
    proof-
      fix x
      assume x_in: "x \<in> coproduct_carrier S"
      assume x_one: "\<forall>xa. xa \<in> S \<longrightarrow> x xa = \<one>\<^bsub>A\<^esub>"
      then have eq: "{s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>} = {}"
        by auto
      show "x =
         cS.finset_sum {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>}
          (\<lambda>a. if a \<in> S then fst (the (coproduct_inclusion S a)) (A_to_obj (x a))
                else undefined)"
        unfolding eq
        unfolding cS.finset_sum_empty
        apply (rule_tac ext)
        unfolding coproduct_of_A_def
        apply auto
        using x_one apply simp
        using x_in
        unfolding coproduct_carrier_def extensional_def
        by simp
    next
      fix D d x
      assume ind: "\<forall>x. x \<in> coproduct_carrier S \<longrightarrow>
           {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>} = D \<longrightarrow>
           x = cS.finset_sum D
            (\<lambda>a. if a \<in> S
            then fst (the (coproduct_inclusion S a)) (A_to_obj (x a))
            else undefined)"
      assume "finite D"
      assume x_in: "x \<in> coproduct_carrier S"
      assume x_D: "{s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>} = insert d D"
      then have "D \<subseteq> S" by auto

      assume "d \<notin> D"
      define y where "y = (\<lambda>s \<in> S. if s = d then \<one>\<^bsub>A\<^esub> else x s)"
      have y_in: "y \<in> coproduct_carrier S"
        using x_in
        unfolding coproduct_carrier_def y_def
        apply auto
      proof-
        assume "finite {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>}"
        have "{s. s \<noteq> d \<and> (s \<noteq> d \<longrightarrow> (s \<in> S \<longrightarrow> x s \<noteq> \<one>\<^bsub>A\<^esub>) \<and> s \<in> S)}
              \<subseteq> {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>}"
          by auto
        then show "finite {s. s \<noteq> d \<and> (s \<noteq> d \<longrightarrow> (s \<in> S \<longrightarrow> x s \<noteq> \<one>\<^bsub>A\<^esub>) \<and> s \<in> S)}"
          using \<open>finite {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>}\<close>
          using finite_subset by blast
      qed
      have y_D: "{s \<in> S. y s \<noteq> \<one>\<^bsub>A\<^esub>} = D"
        using x_D
        unfolding y_def
        using \<open>d \<notin> D\<close> by auto
      have y_ind : "y =
           cS.finset_sum D
            (\<lambda>a. if a \<in> S
                  then fst (the (coproduct_inclusion S a)) (A_to_obj (y a))
                  else undefined)"
        using ind y_in y_D by blast

      have "d \<in> S"
        using x_D by auto
      then have "x d \<in> carrier A"
        using x_in
        unfolding coproduct_carrier_def
        by auto
      have xd_in : "A_to_obj (x d) \<in> coproduct_carrier {SOME y. True}"
        unfolding A_to_obj_def coproduct_carrier_def
        using \<open>x d \<in> carrier A\<close>
        by auto
        
      have x_yd : "x = fst (the (coproduct_inclusion S d)) (A_to_obj (x d))
                       \<otimes>\<^bsub>coproduct_of_A S\<^esub> y"
        unfolding coproduct_inclusion_def
        apply (simp add: xd_in)
        unfolding coproduct_of_A_def y_def A_to_obj_def
        apply auto
        apply (rule_tac ext)
        apply auto
        using \<open>x d \<in> carrier A\<close> apply simp
        using \<open>d \<in> S\<close> apply simp
        apply (rule_tac reverse_equality [OF A.l_one])
        using x_in
        unfolding coproduct_carrier_def extensional_def
        by auto

      have inc_mapsto : "\<And>d. fst (the (coproduct_inclusion S d)) \<in> 
            coproduct_carrier {SOME y. True} \<rightarrow> coproduct_carrier S"
        apply (rule_tac Ab.in_hom_mapsto [OF coproduct_inclusion_in_hom])
        unfolding obj_def coproduct_of_A_def
        by (simp_all add: Ab.Dom'_def Ab.Id'_def)


      show "x =
       cS.finset_sum (insert d D)
        (\<lambda>a. if a \<in> S then fst (the (coproduct_inclusion S a)) (A_to_obj (x a))
              else undefined)"
        apply (subst x_yd)
        apply (subst y_ind)
        apply (subst cS.finset_sum_insert')
        using \<open>finite D\<close> apply simp
        using \<open>d \<in> S\<close> apply (simp add: coproduct_of_A_def)
        using inc_mapsto xd_in apply auto[1]
        using \<open>d \<in> S\<close> \<open>d \<notin> D\<close> \<open>D \<subseteq> S\<close> apply auto
      proof-
        show inc_in: "\<And>s. s \<in> S \<Longrightarrow> fst (the (coproduct_inclusion S s)) (A_to_obj (x s))
         \<in> carrier (coproduct_of_A S)"
        proof-
          fix s
          assume "s \<in> S"
          then have "A_to_obj (x s) \<in> coproduct_carrier {SOME y. True}"
            using x_in
            unfolding A_to_obj_def coproduct_carrier_def
            by auto
          then show "fst (the (coproduct_inclusion S s)) (A_to_obj (x s))
         \<in> carrier (coproduct_of_A S)"
            using inc_mapsto
            unfolding coproduct_of_A_def by auto
        qed
          
        have "cS.finset_sum D
     (\<lambda>a. if a \<in> S then fst (the (coproduct_inclusion S a)) (A_to_obj (y a))
           else undefined) = cS.finset_sum D
     (\<lambda>a. if a \<in> S then fst (the (coproduct_inclusion S a)) (A_to_obj (x a))
           else undefined)"
          apply (rule_tac cS.finset_sum_independence)
          using \<open>finite D\<close> apply simp
          using \<open>D \<subseteq> S\<close> \<open>d \<notin> D\<close> apply auto
          unfolding y_def apply auto
          using inc_in by simp
        then show "fst (the (coproduct_inclusion S d)) (A_to_obj (x d)) \<otimes>\<^bsub>coproduct_of_A S\<^esub>
    cS.finset_sum D
     (\<lambda>a. if a \<in> S then fst (the (coproduct_inclusion S a)) (A_to_obj (y a))
           else undefined) =
    fst (the (coproduct_inclusion S d)) (A_to_obj (x d)) \<otimes>\<^bsub>coproduct_of_A S\<^esub>
    cS.finset_sum D
     (\<lambda>a. if a \<in> S then fst (the (coproduct_inclusion S a)) (A_to_obj (x a))
           else undefined)"
          by simp
      qed
    qed
  qed
  then have rule: "\<And>C x. finite C \<Longrightarrow>
      x \<in> coproduct_carrier S \<Longrightarrow>
      {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>} = C \<Longrightarrow>
      x = cS.finset_sum {s \<in> S. x s \<noteq> \<one>\<^bsub>A\<^esub>}
       (\<lambda>s\<in>S. fst (the (coproduct_inclusion S s)) (A_to_obj (x s)))"
    by simp
  show ?thesis
    apply (rule_tac rule)
    using x_in apply auto
    unfolding coproduct_carrier_def by simp
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


interpretation ColimFun: colimit_functoriality 
       SetCat.comp 
       Ab.comp
       "(\<lambda>S. discrete_category.comp (S.set S))"
       Cocone.discrete_functor 
       Cocone.cocone
       "(\<lambda>c. Some (Ab.Id' (coproduct_of_A (S.set c))))"
       coproduct_inc_nattrafo
       coproduct_UP_map
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

    interpret cin : natural_transformation DC.comp Ab.comp "(Cocone.cocone c)" 
         Const.map  "(coproduct_inc_nattrafo c)"
      using nat.

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

      have \<sigma>_in_hom: "\<And>b. b \<in> S.set c \<Longrightarrow>
          fst (the (\<sigma> (DC.mkIde b))) \<in> hom (Ab.Dom' (the obj))
                                     (Ab.Dom' (the x))"
      proof-
        fix b
        assume "b \<in> S.set c"

        have cod_eq : "x = AbC.cod (\<sigma> (DC.mkIde b))"
          apply (subst \<sigma>.preserves_cod)
          using DC.ide_mkIde [OF \<open>b \<in> S.set c\<close>] apply simp
          apply (subst constant_functor.map_def)
          unfolding constant_functor_def
           apply (simp add: DC.category_axioms AbC.category_axioms)
          unfolding constant_functor_axioms_def
           apply (simp add: ide_x)
          by (simp add: DC.ide_mkIde [OF \<open>b \<in> S.set c\<close>])
        have dom_eq : "obj = AbC.dom (\<sigma> (DC.mkIde b))"
          apply (subst \<sigma>.preserves_dom)
          using DC.ide_mkIde [OF \<open>b \<in> S.set c\<close>] apply simp
          unfolding Cocone.cocone_def
          apply (subst constant_functor.map_def)
          unfolding constant_functor_def
           apply (simp add: discrete_category.is_category 
                              [OF Cocone.is_discrete_category]
                              AbC.category_axioms)
          unfolding constant_functor_axioms_def
          using Cocone.ide_obj apply simp
          unfolding S.ideD(2) [OF ide_c]
          using DC.ide_mkIde [OF \<open>b \<in> S.set c\<close>] by simp

        from \<open>b \<in> S.set c\<close> have "AbC.arr (\<sigma> (DC.mkIde b))"
          apply (rule_tac \<sigma>.preserves_arr)
          by (simp add: DC.ide_mkIde)
        then show "fst (the (\<sigma> (DC.mkIde b)))
         \<in> hom (Ab.Dom' (the obj)) (Ab.Dom' (the x))"
          unfolding cod_eq dom_eq
          unfolding Ab.comp_def
          unfolding AbCC.cod_char AbCC.dom_char
          unfolding AbCC.arr_char
          unfolding Ab.Arr'_def
          by (simp add: Ab.Dom'_def Ab.Id'_def)
      qed

      have in_carrier: "\<And>\<alpha> b.
       \<alpha> \<in> coproduct_carrier (S.set c) \<Longrightarrow>
       b \<in> S.set c \<Longrightarrow>
       fst (the (\<sigma> (DC.mkIde b))) (A_to_obj (\<alpha> b))
       \<in> carrier (Ab.Dom' (the x))"
      proof-
        fix \<alpha> b
        assume \<alpha>_in: "\<alpha> \<in> coproduct_carrier (S.set c)"
        assume "b \<in> S.set c"
        have arr_\<sigma>b: "AbC.arr (\<sigma> (DC.mkIde b))"
          apply (rule_tac \<sigma>.preserves_arr)
          using \<open>b \<in> S.set c\<close>
          by (simp add: DC.ide_mkIde)
        then have \<sigma>b_mapsto: "fst (the (\<sigma> (DC.mkIde b)))
           \<in> carrier (Ab.Dom' (the (\<sigma> (DC.mkIde b)))) \<rightarrow>
          carrier (Ab.Cod' (the (\<sigma> (DC.mkIde b))))"
          unfolding Ab.comp_def
          unfolding AbCC.arr_char
          unfolding Ab.Arr'_def
          unfolding hom_def
          by simp
           (*TODO: Remove a bit of redundancy here. 
           We proved almost the exact same thing about 30 lines ago.*)
        have cod_eq : "x = AbC.cod (\<sigma> (DC.mkIde b))"
          apply (subst \<sigma>.preserves_cod)
          using DC.ide_mkIde [OF \<open>b \<in> S.set c\<close>] apply simp
          apply (subst constant_functor.map_def)
          unfolding constant_functor_def
           apply (simp add: DC.category_axioms AbC.category_axioms)
          unfolding constant_functor_axioms_def
           apply (simp add: ide_x)
          by (simp add: DC.ide_mkIde [OF \<open>b \<in> S.set c\<close>])
        have dom_eq : "obj = AbC.dom (\<sigma> (DC.mkIde b))"
          apply (subst \<sigma>.preserves_dom)
          using DC.ide_mkIde [OF \<open>b \<in> S.set c\<close>] apply simp
          unfolding Cocone.cocone_def
          apply (subst constant_functor.map_def)
          unfolding constant_functor_def
           apply (simp add: discrete_category.is_category 
                              [OF Cocone.is_discrete_category]
                              AbC.category_axioms)
          unfolding constant_functor_axioms_def
          using Cocone.ide_obj apply simp
          unfolding S.ideD(2) [OF ide_c]
          using DC.ide_mkIde [OF \<open>b \<in> S.set c\<close>] by simp

        have "\<alpha> b \<in> carrier A"
          using \<alpha>_in
          unfolding coproduct_carrier_def
          using \<open>b \<in> S.set c\<close>
          by auto
        then have "(A_to_obj (\<alpha> b)) \<in> carrier (coproduct_of_A {SOME y. True})"
          using A_to_obj_in_hom
          unfolding hom_def
          by auto
        then have "(A_to_obj (\<alpha> b)) \<in> carrier (Ab.Dom' (the obj))"
          unfolding obj_def
          by (simp add: Ab.Id'_def Ab.Dom'_def)
        then have "(A_to_obj (\<alpha> b)) \<in> carrier (Ab.Dom' (the (AbC.dom (\<sigma> (DC.mkIde b)))))"
          using dom_eq
          by smt
        then have in_dom : "(A_to_obj (\<alpha> b)) \<in> carrier (Ab.Dom' (the (\<sigma> (DC.mkIde b))))"
          using arr_\<sigma>b
          unfolding Ab.comp_def
          unfolding AbCC.dom_char
          apply simp
          unfolding Ab.Id'_def Ab.Dom'_def
          by simp
        show "fst (the (\<sigma> (DC.mkIde b))) (A_to_obj (\<alpha> b))
       \<in> carrier (Ab.Dom' (the x))"
          apply (subst cod_eq)
          using arr_\<sigma>b
          unfolding Ab.comp_def
          unfolding AbCC.cod_char
          apply simp
          apply (simp add: Ab.Dom'_def Ab.Id'_def)
          using \<sigma>b_mapsto in_dom
          by auto
      qed
      have obj_eq : "Ab.Dom' (the obj) = coproduct_of_A {SOME y. True}"
        unfolding obj_def
        by (simp add: Ab.Dom'_def Ab.Id'_def)


      show UP_in_hom: "
           AbC.in_hom (coproduct_UP_map c x \<sigma>)
            (Some (Ab.Id' (coproduct_of_A (S.set c)))) x"
        apply (rule_tac AbC.in_homI)
      proof-
        interpret CopA : comm_group "coproduct_of_A (S.set c)"
          using coproduct_comm_group.
        have carrier_eq : "carrier (coproduct_of_A (S.set c)) =
                          coproduct_carrier (S.set c)"
          unfolding coproduct_of_A_def
          by simp

        
        show arr_up: "AbC.arr (coproduct_UP_map c x \<sigma>)"
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
          unfolding carrier_eq
          apply simp
          unfolding hom_def
          unfolding carrier_eq
          apply auto
            apply (rule_tac X.finset_sum_carrier)
          using coproduct_carrier_def apply auto[1]
            apply auto
            apply (simp add: in_carrier)
        proof-
          fix \<alpha> \<beta>
          assume \<alpha>_in: "\<alpha> \<in> coproduct_carrier (S.set c)"
          assume \<beta>_in: "\<beta> \<in> coproduct_carrier (S.set c)"

          have \<alpha>\<beta>_in: "\<alpha> \<otimes>\<^bsub>coproduct_of_A (S.set c)\<^esub> \<beta> \<in> coproduct_carrier (S.set c)"
            using \<alpha>_in \<beta>_in
            unfolding reverse_equality [OF carrier_eq]
            by simp
          then show "\<alpha> \<otimes>\<^bsub>coproduct_of_A (S.set c)\<^esub> \<beta> \<notin> coproduct_carrier (S.set c) \<Longrightarrow>
       undefined =
       X.finset_sum {s \<in> S.set c. \<alpha> s \<noteq> \<one>\<^bsub>A\<^esub>}
        (\<lambda>s\<in>S.set c.
            fst (the (\<sigma> (DC.mkIde s))) (A_to_obj (\<alpha> s))) \<otimes>\<^bsub>Ab.Dom' (the x)\<^esub>
       X.finset_sum {s \<in> S.set c. \<beta> s \<noteq> \<one>\<^bsub>A\<^esub>}
        (\<lambda>s\<in>S.set c. fst (the (\<sigma> (DC.mkIde s))) (A_to_obj (\<beta> s)))"
            by simp

          define Sab where "Sab = {s \<in> S.set c. (\<alpha> \<otimes>\<^bsub>coproduct_of_A (S.set c)\<^esub> \<beta>) s \<noteq> \<one>\<^bsub>A\<^esub>}"
          define Sa where "Sa = {s \<in> S.set c. \<alpha> s \<noteq> \<one>\<^bsub>A\<^esub>}"
          define Sb where "Sb = {s \<in> S.set c. \<beta> s \<noteq> \<one>\<^bsub>A\<^esub>}"
          define SauSb where "SauSb = Sa \<union> Sb"

          have "finite Sa"
            unfolding Sa_def
            using \<alpha>_in
            unfolding coproduct_carrier_def
            by simp
          have "finite Sb"
            unfolding Sb_def
            using \<beta>_in
            unfolding coproduct_carrier_def
            by simp

          have "Sa \<subseteq> Sa \<union> Sb" by simp
          have "Sb \<subseteq> Sa \<union> Sb" by simp
          have "Sab \<subseteq> Sa \<union> Sb"
            unfolding Sab_def Sa_def Sb_def
            unfolding coproduct_of_A_def
            by auto



          have b_one : "\<And>b. b \<in> S.set c \<Longrightarrow>
          fst (the (\<sigma> (DC.mkIde b))) (A_to_obj \<one>\<^bsub>A\<^esub>) = \<one>\<^bsub>Ab.Dom' (the x)\<^esub>"
            apply (subst hom_one [OF A_to_obj_in_hom])
              apply simp
            using coproduct_comm_group
            using comm_group_def apply blast
            unfolding reverse_equality [OF obj_eq]
            apply (subst hom_one [OF \<sigma>_in_hom])
               apply auto
            unfolding obj_eq
            using coproduct_comm_group
            using comm_group_def by blast

          show "X.finset_sum {s \<in> S.set c. (\<alpha> \<otimes>\<^bsub>coproduct_of_A (S.set c)\<^esub> \<beta>) s \<noteq> \<one>\<^bsub>A\<^esub>}
        (\<lambda>s\<in>S.set c.
            fst (the (\<sigma> (DC.mkIde s)))
             (A_to_obj ((\<alpha> \<otimes>\<^bsub>coproduct_of_A (S.set c)\<^esub> \<beta>) s))) =
       X.finset_sum {s \<in> S.set c. \<alpha> s \<noteq> \<one>\<^bsub>A\<^esub>}
        (\<lambda>s\<in>S.set c.
            fst (the (\<sigma> (DC.mkIde s))) (A_to_obj (\<alpha> s))) \<otimes>\<^bsub>Ab.Dom' (the x)\<^esub>
       X.finset_sum {s \<in> S.set c. \<beta> s \<noteq> \<one>\<^bsub>A\<^esub>}
        (\<lambda>s\<in>S.set c. fst (the (\<sigma> (DC.mkIde s))) (A_to_obj (\<beta> s)))"
            unfolding reverse_equality [OF Sa_def]
            unfolding reverse_equality [OF Sb_def]
            unfolding reverse_equality [OF Sab_def]
            apply (subst X.finset_sum_expand_domain [OF \<open>Sab \<subseteq> Sa \<union> Sb\<close>])
               apply auto
                    apply (rule_tac in_carrier)
            using \<alpha>\<beta>_in apply simp
            unfolding Sab_def apply auto
            using \<open>finite Sa\<close> apply simp
            using \<open>finite Sb\<close> apply simp
            using b_one apply simp
               apply (simp add: Sa_def)
            using b_one apply simp
             apply (simp add: Sb_def)
            apply (subst X.finset_sum_expand_domain [OF \<open>Sa \<subseteq> Sa \<union> Sb\<close>])
            unfolding Sa_def Sb_def
            apply auto
                apply (rule_tac in_carrier)
                  apply (simp_all add: \<alpha>_in)
            unfolding reverse_equality [OF Sb_def]
            unfolding reverse_equality [OF Sa_def]
               apply (simp_all add: \<open>finite Sa\<close> \<open>finite Sb\<close>)
            using b_one apply simp
            apply (subst X.finset_sum_expand_domain [OF \<open>Sb \<subseteq> Sa \<union> Sb\<close>])
            unfolding Sa_def Sb_def
               apply auto
                apply (rule_tac in_carrier)
                  apply (simp_all add: \<beta>_in)
            unfolding reverse_equality [OF Sb_def]
            unfolding reverse_equality [OF Sa_def]
               apply (simp_all add: \<open>finite Sa\<close> \<open>finite Sb\<close>)
            using b_one apply simp
            apply (subst reverse_equality [OF X.finset_sum_binary_sum])
            using \<open>finite Sa\<close> \<open>finite Sb\<close> apply simp
              apply auto
                    apply (rule_tac in_carrier)
                     apply (simp_all add: \<alpha>_in \<beta>_in Sa_def Sb_def)
               apply (rule_tac in_carrier)
                apply (simp_all add: \<alpha>_in)
              apply (rule_tac in_carrier)
               apply (simp_all add: \<beta>_in)
             apply (rule_tac in_carrier)
              apply (simp_all add: \<beta>_in)
            apply (rule_tac X.finset_sum_independence)
            using \<open>finite Sa\<close> \<open>finite Sb\<close>
              apply (simp add: Sa_def Sb_def)
             apply auto
               apply (rule_tac in_carrier)
            using \<alpha>\<beta>_in apply simp_all
              apply (rule_tac in_carrier)
               apply simp_all
          proof-
            fix b
            assume b_in: "b \<in> S.set c"
            from b_in have \<alpha>b_in: "\<alpha> b \<in> carrier A"
              using \<alpha>_in
              unfolding coproduct_carrier_def by auto[1]
            then have A\<alpha>b_in : " A_to_obj (\<alpha> b) \<in> carrier (Ab.Dom' (the obj))"
              unfolding obj_eq
              using A_to_obj_in_hom
              unfolding hom_def
              by auto
            from b_in have \<beta>b_in: "\<beta> b \<in> carrier A"
              using \<beta>_in
              unfolding coproduct_carrier_def by auto[1]
            then have A\<beta>b_in : " A_to_obj (\<beta> b) \<in> carrier (Ab.Dom' (the obj))"
              unfolding obj_eq
              using A_to_obj_in_hom
              unfolding hom_def
              by auto
            show "b \<in> S.set c \<Longrightarrow>
          fst (the (\<sigma> (DC.mkIde b)))
           (A_to_obj ((\<alpha> \<otimes>\<^bsub>coproduct_of_A (S.set c)\<^esub> \<beta>) b)) =
          fst (the (\<sigma> (DC.mkIde b))) (A_to_obj (\<alpha> b)) \<otimes>\<^bsub>Ab.Dom' (the x)\<^esub>
          fst (the (\<sigma> (DC.mkIde b))) (A_to_obj (\<beta> b))"
              unfolding coproduct_of_A_def
              apply simp
              apply (subst hom_mult [OF A_to_obj_in_hom])
              using \<alpha>b_in \<beta>b_in apply auto[2]
              unfolding reverse_equality [OF obj_eq]
              apply (subst hom_mult [OF \<sigma>_in_hom])
              using A\<alpha>b_in A\<beta>b_in by auto
            then show "b \<in> S.set c \<Longrightarrow>
          fst (the (\<sigma> (DC.mkIde b)))
           (A_to_obj ((\<alpha> \<otimes>\<^bsub>coproduct_of_A (S.set c)\<^esub> \<beta>) b)) =
          fst (the (\<sigma> (DC.mkIde b))) (A_to_obj (\<alpha> b)) \<otimes>\<^bsub>Ab.Dom' (the x)\<^esub>
          fst (the (\<sigma> (DC.mkIde b))) (A_to_obj (\<beta> b))"
              by simp
          qed
        qed
        show "AbC.dom (coproduct_UP_map c x \<sigma>) =
           Some (Ab.Id' (coproduct_of_A (S.set c)))"
          using arr_up
          unfolding Ab.comp_def
          unfolding AbCC.dom_char
          by (simp add: Ab.Dom'_def coproduct_UP_map_def)
        show "AbC.cod (coproduct_UP_map c x \<sigma>) = x"
          using arr_up ide_x
          unfolding Ab.comp_def
          unfolding AbCC.cod_char AbCC.ide_char
          by (simp add: Ab.Cod'_def coproduct_UP_map_def)
      qed
      show \<sigma>UP_eq: "\<And>b.
       cocone DC.comp Ab.comp (Cocone.cocone c) x \<sigma> \<Longrightarrow>
       AbC.ide x \<Longrightarrow>
       DC.ide b \<Longrightarrow>
       \<sigma> b = Ab.comp (coproduct_UP_map c x \<sigma>) (coproduct_inc_nattrafo c b)"
      proof-
        fix b
        assume ide_b: "DC.ide b"
        then have arr_b: "DC.arr b" by simp

        have b_eq : "(DC.mkIde (DC.toObj b)) = b"
          using DC.mkIde_toObj arr_b by blast

          

        have const_x: "constant_functor DC.comp Ab.comp x"
          unfolding constant_functor_def
          apply (simp add: DC.is_category Ab.is_category)
          unfolding constant_functor_axioms_def
          using ide_x.


        show "\<sigma> b = Ab.comp (coproduct_UP_map c x \<sigma>) (coproduct_inc_nattrafo c b)"
          apply (rule_tac Ab.comp_eqI)
          unfolding reverse_equality [OF Ab.comp_def]
                apply (rule_tac \<sigma>.preserves_arr [OF arr_b])
          using UP_in_hom apply blast
              apply (rule_tac cin.preserves_arr [OF arr_b])
          unfolding \<sigma>.preserves_dom [OF arr_b]
          unfolding cin.preserves_dom [OF arr_b] apply simp
          unfolding \<sigma>.preserves_cod [OF arr_b]
          unfolding AbC.in_hom_cod [OF UP_in_hom]
            apply (subst constant_functor.map_def)
          unfolding DC.ideD(3) [OF ide_b]
             apply (simp add: const_x)
            apply (simp add: arr_b)
          unfolding cin.preserves_cod [OF arr_b]
          unfolding AbC.in_hom_dom [OF UP_in_hom]
          unfolding Const.map_def
           apply (simp add: arr_b)
        proof-
          fix y
          assume y_in_\<sigma> : "y \<in> carrier (Ab.Dom' (the (\<sigma> b)))"
          assume "y \<in> carrier (Ab.Dom' (the (coproduct_inc_nattrafo c b)))"
          then have y_in_cin : "y \<in> coproduct_carrier {SOME y. True}"
            unfolding coproduct_inc_nattrafo_def Ab.Dom'_def
            apply (simp add: arr_b)
            unfolding coproduct_inclusion_def coproduct_of_A_def
            by simp
          
          assume "fst (the (coproduct_inc_nattrafo c b)) y
          \<in> carrier (Ab.Dom' (the (coproduct_UP_map c x \<sigma>)))"
          then have ciny_in_up : "fst (the (coproduct_inc_nattrafo c b)) y 
               \<in> coproduct_carrier (S.set c)"
            unfolding coproduct_UP_map_def Ab.Dom'_def coproduct_of_A_def
            by simp


          define S where "S = {s \<in> S.set c. fst (the (coproduct_inc_nattrafo c b)) y s \<noteq> \<one>\<^bsub>A\<^esub>}"
          have set_eq : "S \<subseteq> {DC.toObj b}"
            unfolding S_def
            unfolding coproduct_inc_nattrafo_def
            apply (simp add: arr_b)
            unfolding coproduct_inclusion_def
            apply (simp add: y_in_cin)
            by auto
          then have "S = {} \<or> S = {DC.toObj b}" by auto
          show "fst (the (\<sigma> b)) y =
          fst (the (coproduct_UP_map c x \<sigma>))
           (fst (the (coproduct_inc_nattrafo c b)) y)"
            unfolding coproduct_UP_map_def
            apply (simp add: ciny_in_up)
            unfolding reverse_equality [OF S_def]
            using \<open>S = {} \<or> S = {DC.toObj b}\<close>
          proof
            show "S = {DC.toObj b} \<Longrightarrow>
    fst (the (\<sigma> b)) y = X.finset_sum S
     (\<lambda>s\<in>S.set c. fst (the (\<sigma> (DC.mkIde s)))
          (A_to_obj (fst (the (coproduct_inc_nattrafo c b)) y s)))"
              apply simp
              apply (subst X.finset_sum_singleton)
               apply (simp add: DC.toObj_in_Obj [OF arr_b])
               apply (rule_tac in_carrier)
              using ciny_in_up apply simp
              using DC.toObj_in_Obj [OF arr_b] apply simp_all
            proof-
              have eq2 : "(A_to_obj (fst (the (coproduct_inc_nattrafo c b)) 
                          y (DC.toObj b))) = y"
                unfolding coproduct_inc_nattrafo_def
                apply (simp add: arr_b)
                unfolding coproduct_inclusion_def
                apply (simp add: DC.toObj_in_Obj [OF arr_b] y_in_cin)
                unfolding A_to_obj_def
                apply (rule_tac ext)
                apply simp
                using y_in_cin
                unfolding coproduct_carrier_def
                unfolding extensional_def
                by auto
              show "fst (the (\<sigma> b)) y =
    fst (the (\<sigma> (DC.mkIde (DC.toObj b))))
     (A_to_obj (fst (the (coproduct_inc_nattrafo c b)) y (DC.toObj b)))"
                unfolding b_eq eq2 by simp
            qed

            show "S = {} \<Longrightarrow>
    fst (the (\<sigma> b)) y =  X.finset_sum S
     (\<lambda>s\<in>S.set c. fst (the (\<sigma> (DC.mkIde s)))
          (A_to_obj (fst (the (coproduct_inc_nattrafo c b)) y s)))"
              apply simp
              unfolding X.finset_sum_empty
            proof-
              assume "S = {}"
              then have "y = \<one>\<^bsub>coproduct_of_A {SOME y. True}\<^esub>"
                unfolding coproduct_of_A_def
                apply (rule_tac ext)
                apply auto
              proof-
                show "\<And>x. x \<noteq> (SOME y. True) \<Longrightarrow> y x = undefined"
                  using y_in_cin
                  unfolding coproduct_carrier_def extensional_def
                  by simp
                show "S = {} \<Longrightarrow> y (SOME y. True) = \<one>\<^bsub>A\<^esub>"
                  unfolding S_def
                  unfolding coproduct_inc_nattrafo_def
                  apply (simp add: arr_b)
                  unfolding coproduct_inclusion_def
                  apply (simp add: y_in_cin)
                proof-
                  assume "\<forall>x. x \<in> S.set c \<longrightarrow>
        (if x = DC.toObj b then y (SOME y. True) else \<one>\<^bsub>A\<^esub>) = \<one>\<^bsub>A\<^esub>"
                  then have "(if DC.toObj b = DC.toObj b then y (SOME y. True) 
                              else \<one>\<^bsub>A\<^esub>) = \<one>\<^bsub>A\<^esub>"
                    using DC.toObj_in_Obj [OF arr_b] by blast
                  then show "y (SOME y. True) = \<one>\<^bsub>A\<^esub>"
                    by simp
                qed
              qed
              then show "fst (the (\<sigma> b)) y = \<one>\<^bsub>Ab.Dom' (the x)\<^esub>"
                apply simp
                apply (subst reverse_equality [OF b_eq])
                unfolding reverse_equality [OF obj_eq]
                apply (subst hom_one [OF \<sigma>_in_hom])
                using DC.toObj_in_Obj [OF arr_b] apply simp_all
                unfolding obj_eq
                using coproduct_comm_group
                using comm_group_def by blast
            qed
          qed
        qed
      qed
      fix f
      assume f_in_hom : "AbC.in_hom f (Some (Ab.Id' (coproduct_of_A (S.set c)))) x"

      interpret fstf : comm_group_hom "coproduct_of_A (S.set c)" "Ab.Dom' (the x)" "(fst (the f))"
        unfolding comm_group_hom_def
        unfolding comm_group_hom_axioms_def
        apply (simp add: coproduct_comm_group X.comm_group_axioms)
      proof-
        have "fst (the f) \<in> hom (Ab.Dom' (the f)) (Ab.Cod' (the f)) \<and>
       Ab.Dom' (the f) = Ab.Dom' (the (Some (Ab.Id' (coproduct_of_A (S.set c))))) \<and>
       Ab.Cod' (the f) = Ab.Dom' (the x)"
          using f_in_hom
          unfolding Ab.comp_def AbCC.in_hom_char AbCC.In_Hom_def Ab.Arr'_def
          by auto
        then show "fst (the f) \<in> hom (coproduct_of_A (S.set c)) (Ab.Dom' (the x))"
          apply (simp add: Ab.Id'_def Ab.Dom'_def)
          by auto
      qed

      interpret fstup : comm_group_hom "coproduct_of_A (S.set c)" "Ab.Dom' (the x)" 
               "(fst (the (coproduct_UP_map c x \<sigma>)))"
        unfolding comm_group_hom_def
        unfolding comm_group_hom_axioms_def
        apply (simp add: coproduct_comm_group X.comm_group_axioms)
      proof-
        have "fst (the(coproduct_UP_map c x \<sigma>)) \<in> hom (Ab.Dom' (the(coproduct_UP_map c x \<sigma>))) (Ab.Cod' (the(coproduct_UP_map c x \<sigma>))) \<and>
       Ab.Dom' (the(coproduct_UP_map c x \<sigma>)) = Ab.Dom' (the (Some (Ab.Id' (coproduct_of_A (S.set c))))) \<and>
       Ab.Cod' (the(coproduct_UP_map c x \<sigma>)) = Ab.Dom' (the x)"
          using UP_in_hom
          unfolding Ab.comp_def AbCC.in_hom_char AbCC.In_Hom_def Ab.Arr'_def
          by auto
        then show "fst (the(coproduct_UP_map c x \<sigma>)) \<in> hom (coproduct_of_A (S.set c)) (Ab.Dom' (the x))"
          apply (simp add: Ab.Id'_def Ab.Dom'_def)
          by auto
      qed

      assume f_cocone : "\<forall>b. DC.ide b \<longrightarrow> \<sigma> b = Ab.comp f (coproduct_inc_nattrafo c b)"
      show "f = coproduct_UP_map c x \<sigma>"
        apply (rule_tac Ab.fun_eqI)
        unfolding reverse_equality [OF Ab.comp_def]
        using f_in_hom apply blast
        using UP_in_hom apply blast
        unfolding AbC.in_hom_dom [OF f_in_hom]
        unfolding AbC.in_hom_dom [OF UP_in_hom] apply simp
        unfolding AbC.in_hom_cod [OF f_in_hom]
        unfolding AbC.in_hom_cod [OF UP_in_hom] apply simp
      proof-
        fix y
        assume "y \<in> carrier (Ab.Dom' (the f))"
        assume "y \<in> carrier (Ab.Dom' (the (coproduct_UP_map c x \<sigma>)))"
        then have y_in : "y \<in> carrier (coproduct_of_A (S.set c))"
          unfolding coproduct_UP_map_def Ab.Dom'_def
          by simp
        then have y_in' : "y \<in> coproduct_carrier (S.set c)"
          unfolding coproduct_of_A_def by simp

      have inc_mapsto : "\<And>d. fst (the (coproduct_inclusion (S.set c) d)) \<in> 
            coproduct_carrier {SOME y. True} \<rightarrow> coproduct_carrier (S.set c)"
        apply (rule_tac Ab.in_hom_mapsto [OF coproduct_inclusion_in_hom])
        unfolding obj_def coproduct_of_A_def
        by (simp_all add: Ab.Dom'_def Ab.Id'_def)

      have inc_in: "\<And>s. s \<in> (S.set c) \<Longrightarrow> fst (the (coproduct_inclusion (S.set c) s)) (A_to_obj (y s))
         \<in> carrier (coproduct_of_A (S.set c))"
      proof-
        fix s
        assume "s \<in> (S.set c)"
        then have "A_to_obj (y s) \<in> coproduct_carrier {SOME y. True}"
          using y_in'
          unfolding A_to_obj_def coproduct_carrier_def
          by auto
        then show "fst (the (coproduct_inclusion (S.set c) s)) (A_to_obj (y s))
         \<in> carrier (coproduct_of_A (S.set c))"
          using inc_mapsto
          unfolding coproduct_of_A_def by auto
      qed

      show "fst (the f) y = fst (the (coproduct_UP_map c x \<sigma>)) y"
        apply (subst coproduct_generated [OF y_in'])
        apply (rule_tac reverse_equality)
        apply (subst coproduct_generated [OF y_in'])
        apply (subst fstf.preserves_finset_sum)
        using y_in'
          apply (simp add: coproduct_carrier_def)
         apply auto[1]
        using inc_in apply simp
        apply (subst fstup.preserves_finset_sum)
        using y_in'
          apply (simp add: coproduct_carrier_def)
         apply auto[1]
        using inc_in apply simp
        apply (rule_tac X.finset_sum_independence)
        using y_in'
          apply (simp add: coproduct_carrier_def)
         apply auto
      proof-
        fix s
        assume "s \<in> S.set c"
        then have ide_s: "DC.ide (DC.mkIde s)"
          using DC.ide_mkIde by blast
        then have arr_s : "DC.arr (DC.mkIde s)"
          by simp

        have "y s \<in> carrier A"
          using y_in'
          unfolding coproduct_carrier_def
          using \<open>s \<in> S.set c\<close> by auto

        have ys_in: "A_to_obj (y s)
     \<in> carrier (Ab.Dom' (the (coproduct_inc_nattrafo c (DC.mkIde s))))"
          unfolding coproduct_inc_nattrafo_def
          apply (simp add: arr_s)
          unfolding coproduct_inclusion_def
          apply (simp add: Ab.Dom'_def)
          unfolding A_to_obj_def coproduct_of_A_def coproduct_carrier_def
          apply simp
          using \<open>y s \<in> carrier A\<close>
          by simp

        from ide_s have f_eq: "\<sigma> (DC.mkIde s) = Ab.comp f (coproduct_inc_nattrafo c (DC.mkIde s))"
          using f_cocone by simp
        have up_eq: "\<sigma> (DC.mkIde s) = Ab.comp (coproduct_UP_map c x \<sigma>) (coproduct_inc_nattrafo c (DC.mkIde s))"
          apply (rule_tac \<sigma>UP_eq)
          using \<sigma>.natural_transformation_axioms
            apply (simp add: cocone_def)
           apply (simp add: ide_x)
          using ide_s.



        have f_seq : "AbC.seq f (coproduct_inc_nattrafo c (DC.mkIde s))"
          apply (rule_tac AbC.seqI)
            apply (rule_tac cin.preserves_arr [OF arr_s])
          using f_in_hom apply blast
          unfolding AbC.in_hom_dom [OF f_in_hom]
          apply (subst cin.preserves_cod [OF arr_s])
          unfolding Const.map_def
          by (simp add: arr_s)
        have f_comp_char : "Ab.comp f (coproduct_inc_nattrafo c (DC.mkIde s))  = 
              Some (Ab.Comp' (the f) (the (coproduct_inc_nattrafo c (DC.mkIde s))))"
          unfolding Ab.comp_def
          apply (subst AbCC.comp_simp)
          using AbCC.not_arr_null
          using f_seq
          unfolding Ab.comp_def by auto
        have f_y_eq : "fst (the f)
           (fst (the (coproduct_inclusion (S.set c) s)) (A_to_obj (y s))) =
           fst (the (\<sigma> (DC.mkIde s))) (A_to_obj (y s))"
          unfolding f_eq
          unfolding f_comp_char
          unfolding Ab.Comp'_def
          apply (simp add: ys_in)
          unfolding coproduct_inc_nattrafo_def
          apply (simp add: arr_s)
          using DC.toObj_mkIde [OF \<open>s \<in> S.set c\<close>]
          by simp

        have up_seq : "AbC.seq (coproduct_UP_map c x \<sigma>) (coproduct_inc_nattrafo c (DC.mkIde s))"
          apply (rule_tac AbC.seqI)
            apply (rule_tac cin.preserves_arr [OF arr_s])
          using UP_in_hom apply blast
          unfolding AbC.in_hom_dom [OF UP_in_hom]
          apply (subst cin.preserves_cod [OF arr_s])
          unfolding Const.map_def
          by (simp add: arr_s)
        have up_comp_char : "Ab.comp (coproduct_UP_map c x \<sigma>) (coproduct_inc_nattrafo c (DC.mkIde s))  = 
              Some (Ab.Comp' (the (coproduct_UP_map c x \<sigma>)) (the (coproduct_inc_nattrafo c (DC.mkIde s))))"
          unfolding Ab.comp_def
          apply (subst AbCC.comp_simp)
          using AbCC.not_arr_null
          using up_seq
          unfolding Ab.comp_def by auto
        have up_y_eq : "fst (the (coproduct_UP_map c x \<sigma>))
           (fst (the (coproduct_inclusion (S.set c) s)) (A_to_obj (y s))) =
           fst (the (\<sigma> (DC.mkIde s))) (A_to_obj (y s))"
          unfolding up_eq
          unfolding up_comp_char
          unfolding Ab.Comp'_def
          apply (simp add: ys_in)
          unfolding coproduct_inc_nattrafo_def
          apply (simp add: arr_s)
          using DC.toObj_mkIde [OF \<open>s \<in> S.set c\<close>]
          by simp

        show "fst (the (coproduct_UP_map c x \<sigma>))
           (fst (the (coproduct_inclusion (S.set c) s)) (A_to_obj (y s)))
          \<in> carrier (Ab.Dom' (the x))"
          unfolding up_y_eq
          apply (rule_tac in_carrier)
          using y_in' \<open>s \<in> S.set c\<close>.

        show "fst (the (coproduct_UP_map c x \<sigma>))
           (fst (the (coproduct_inclusion (S.set c) s)) (A_to_obj (y s))) =
          fst (the f)
           (fst (the (coproduct_inclusion (S.set c) s)) (A_to_obj (y s)))"
          unfolding up_y_eq f_y_eq
          by simp
      qed
    qed
  qed
qed
qed    


lemma colimit_functoriality : "colimit_functoriality 
       SetCat.comp 
       Ab.comp
       (\<lambda>S. discrete_category.comp (S.set S))
       Cocone.discrete_functor 
       Cocone.cocone
       (\<lambda>c. Some (Ab.Id' (coproduct_of_A (S.set c))))
       coproduct_inc_nattrafo
       coproduct_UP_map"
  using ColimFun.colimit_functoriality_axioms.




definition map where
  "map = ColimFun.colim_functor"


lemma is_functor : "functor SetCat.comp Ab.comp map"
  unfolding map_def
  using ColimFun.is_functor.

(*This is just a trivial unimportant lemma, that happens to be convenient in a moment.*)
lemma finset_sum_eqI : "f = g \<Longrightarrow>
      comm_group.finset_sum Z S f = comm_group.finset_sum Z S g"
  by simp

lemma fst_map_simp :
  assumes "S.arr f" "x \<in> coproduct_carrier (S.Dom f)"
  shows "fst (the (map f)) x = 
      comm_group.finset_sum 
     (coproduct_of_A (S.Cod f))
     {s \<in> S.Dom f. x s \<noteq> \<one>\<^bsub>A\<^esub>} 
     (\<lambda>s \<in> S.Dom f. fst (the (coproduct_inclusion (S.Cod f) 
     ((S.Fun f) s))) (A_to_obj (x s)))"
  unfolding map_def
  unfolding ColimFun.colim_functor_def
  apply (simp add: assms)
  unfolding coproduct_UP_map_def
  apply (simp add: assms Ab.Dom'_def Ab.Id'_def)
  apply (subst vertical_composite.map_def)
   apply (rule_tac ColimFun.vert_comp)
   apply (simp add: assms)
  apply (rule_tac finset_sum_eqI)
  apply (rule_tac ext)
  apply auto
proof-
  fix s
  assume "s \<in> S.Dom f"
  interpret Dom : discrete_category "(S.Dom f)"
    using Cocone.is_discrete_category.
  interpret Cod : discrete_category "(S.Cod f)"
    using Cocone.is_discrete_category.
  have arr_s: "Dom.arr (Dom.mkIde s)"
    by (simp add:  \<open>s \<in> S.Dom f\<close> Dom.ide_mkIde)
  then show "\<not> Dom.arr (Dom.mkIde s) \<Longrightarrow>
          fst (the Cocone.C.null) (A_to_obj (x s)) =
          fst (the (coproduct_inclusion (S.Cod f) (S.Fun f s)))
           (A_to_obj (x s))"
    by simp

  have "S.ide (S.cod f)"
    using assms by simp

  interpret Const : constant_functor Dom.comp Ab.comp obj
    apply (rule_tac Cocone.const_fun)
    by (simp add: assms)
  interpret ColimCod : colimit 
   Cod.comp Ab.comp "(Cocone.cocone (S.cod f))"
   "(coproduct_inc_nattrafo (S.cod f))"
   "(Some (Ab.Id' (coproduct_of_A (S.Cod f))))"
   "(coproduct_UP_map (S.cod f))"
    using ColimFun.colimit_existence [OF \<open>S.ide (S.cod f)\<close>].
    
  have arr_disc : "Cod.arr (Cocone.discrete_functor f (Dom.cod (Dom.mkIde s)))"
    apply (rule_tac functor.preserves_arr [OF 
          functor_to_cat.Ffun [OF 
          Cocone.is_functor_to_cat]])
     apply (simp add: assms)
    using \<open>s \<in> S.Dom f\<close> Dom.ide_mkIde by simp

  have "(Ab.comp (coproduct_inc_nattrafo (S.cod f)
        (Cocone.discrete_functor f (Dom.cod (Dom.mkIde s))))
         (Cocone.cocone f (Dom.mkIde s))) =
        (coproduct_inclusion (S.Cod f) (S.Fun f s))"
    unfolding Ab.comp_def
    apply (subst AbCC.comp_arr_ide)
    unfolding reverse_equality [OF Ab.comp_def]
    unfolding Cocone.cocone_def
      apply (rule_tac Const.preserves_ide)
      apply (simp add:  \<open>s \<in> S.Dom f\<close> Dom.ide_mkIde)
     apply (rule_tac Cocone.C.seqI)
    using Const.preserves_arr [OF arr_s] apply blast
      apply (rule_tac ColimCod.\<tau>.preserves_arr)
      apply (simp add: arr_disc)
     apply (subst ColimCod.\<tau>.preserves_dom)
      apply (simp add: arr_disc)
     apply (subst Const.preserves_cod)
      apply (simp add:  \<open>s \<in> S.Dom f\<close> Dom.ide_mkIde)
    unfolding Cocone.cocone_def
     apply (subst S.dom_cod)
      apply (simp add: assms)
     apply (subst constant_functor.map_def)
      apply (subst constant_functor_def)
      apply (simp add: Cod.category_axioms Ab.is_category)
    unfolding constant_functor_axioms_def
    using Cocone.ide_obj apply simp
    unfolding Const.map_def
    using Dom.arr_cod [OF arr_s]
          Cod.arr_dom [OF arr_disc] apply simp
    unfolding coproduct_inc_nattrafo_def apply (simp add: arr_disc)
    unfolding Cocone.discrete_functor_def
    apply (simp add: arr_s)
    unfolding Dom.toObj_mkIde [OF \<open>s \<in> S.Dom f\<close>]
    apply (subst Cod.toObj_mkIde)
    using S.Fun_mapsto [OF \<open>S.arr f\<close>] \<open>s \<in> S.Dom f\<close>
    by auto
  then show "fst (the (Ab.comp (coproduct_inc_nattrafo (S.cod f)
             (Cocone.discrete_functor f (Dom.cod (Dom.mkIde s))))
            (Cocone.cocone f (Dom.mkIde s)))) (A_to_obj (x s)) =
          fst (the (coproduct_inclusion (S.Cod f) (S.Fun f s))) (A_to_obj (x s))"
    by simp
qed


    
    






end





end
