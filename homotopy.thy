theory homotopy
  imports Main
          simplicialSet
          "Category3.FunctorCategory"
          smashProduct
begin

lemma (in curried_functor')
  map_simp':
  assumes "A2.arr f2"
  shows "map f2 = A1_B.Abs_arr (Some (\<lambda>f1. F (f1, f2), \<lambda>f1. F (f1, A2.dom f2), \<lambda>f1. F (f1, A2.cod f2)))"
  unfolding map_simp [OF \<open>A2.arr f2\<close>]
  unfolding A1_B.mkArr_def
  using F.fixing_arr_gives_natural_transformation_2 [OF \<open>A2.arr f2\<close>]
  by simp



context begin



interpretation Delta : simplex.
interpretation sSet : functor_category Delta.comp pointed_set.pointed_set_comp
  unfolding functor_category_def
  by (simp add: Delta.is_category pointed_set.is_category)


interpretation eval : evaluation_functor Delta.comp pointed_set.pointed_set_comp
  unfolding evaluation_functor_def
  unfolding functor_category_def product_category_def
  by (simp add: sSet.is_category Delta.is_category pointed_set.is_category)


interpretation eval_cur : curried_functor' 
     sSet.comp Delta.comp pointed_set.pointed_set_comp
     eval.map
  unfolding curried_functor'_def
  unfolding currying_def binary_functor_def functor_category_def
            product_category_def
  apply (simp add: sSet.is_category Delta.is_category pointed_set.is_category)
  using eval.is_functor.

definition D0 where
  "D0 = Some (1, [0])"

lemma ide_D0: "sSet.A.ide D0"
  unfolding D0_def
  using Delta.ide_D0.

lemma arr_D0: "sSet.A.arr D0"
  using ide_D0 by simp

lemma ide_D0I : "(Some (fin_set.Id' (Suc 0))) = D0"
  unfolding D0_def fin_set.Id'_def by simp

definition ev_0_arr where
  "ev_0_arr = eval_cur.map D0"


interpretation sSet_set : functor_category sSet.comp pointed_set.pointed_set_comp
  unfolding functor_category_def
  by (simp add: sSet.is_category pointed_set.is_category)


lemma ide_ev_0: "sSet_set.ide (eval_cur.map D0)"
  apply (rule_tac functor.preserves_ide [OF eval_cur.is_functor])
  using ide_D0.


definition ev_0_functor where
  "ev_0_functor = sSet_set.Fun (eval_cur.map D0)"

lemma ev_0_functor: "functor sSet.comp pointed_set.pointed_set_comp ev_0_functor"
  unfolding ev_0_functor_def
  using ide_ev_0
  unfolding sSet_set.ide_char
  by blast






lemma ev_0_functor_simp: assumes arr_c: "sSet.arr c"
  shows "(ev_0_functor c) = (sSet.Fun c D0)"
  unfolding ev_0_functor_def
  unfolding eval_cur.map_simp' [OF arr_D0]
  unfolding sSet_set.Fun_def
  apply (subst sSet_set.Abs_arr_inverse)
   apply simp_all
  apply (subst eval.map_simp)
   apply (simp add: arr_c ide_D0)
  by simp


lemma sSet_arr_dom_eq:
  assumes arr_f : "sSet.arr f"
  and arr_x : "sSet.A.arr x"
shows "fst (snd (the (sSet.Dom f x))) = fst (snd (the (sSet.Fun f x)))"
proof-
  interpret nat_f : natural_transformation Delta.comp pointed_set.pointed_set_comp
       "sSet.Dom f" "sSet.Cod f" "sSet.Fun f"
    using arr_f
    unfolding sSet.arr_char by simp
  have "sSet.B.dom (sSet.Dom f x) = sSet.B.dom (sSet.Fun f x)"
    unfolding nat_f.preserves_dom [OF arr_x]
    unfolding nat_f.F.preserves_dom [OF arr_x]
    by simp
  then show "fst (snd (the (sSet.Dom f x))) = fst (snd (the (sSet.Fun f x)))"
    unfolding P.dom_char [OF nat_f.F.preserves_arr [OF arr_x]]
    unfolding P.dom_char [OF nat_f.preserves_arr [OF arr_x]]
    by (simp add: P.Id'_def)
qed


lemma sSet_arr_cod_eq:
  assumes arr_f : "sSet.arr f"
  and ide_x : "sSet.A.ide x"
shows "fst (snd (the (sSet.Cod f x))) = snd (snd (the (sSet.Fun f x)))"
proof-
  have arr_x : "sSet.A.arr x"
    using ide_x by simp
  interpret nat_f : natural_transformation Delta.comp pointed_set.pointed_set_comp
       "sSet.Dom f" "sSet.Cod f" "sSet.Fun f"
    using arr_f
    unfolding sSet.arr_char by simp
  have "sSet.A.dom x = sSet.A.cod x"
    using ide_x by simp
  then have "sSet.B.dom (sSet.Cod f x) = sSet.B.cod (sSet.Fun f x)"
    unfolding nat_f.preserves_cod [OF arr_x]
    unfolding nat_f.G.preserves_dom [OF arr_x]
    by simp
  then show cod_eq : "fst (snd (the (sSet.Cod f x))) = snd (snd (the (sSet.Fun f x)))"
    unfolding P.dom_char [OF nat_f.G.preserves_arr [OF arr_x]]
    unfolding P.cod_char [OF nat_f.preserves_arr [OF arr_x]]
    by (simp add: P.Id'_def)
qed



lemma pi0_restrict : 
  assumes arr_f : "sSet.arr f"
  and x_in_dom: "x \<in> snd (fst (snd (the (ev_0_functor f))))"
  and y_in_dom: "y \<in> snd (fst (snd (the (ev_0_functor f))))"
  and Rxy: "pointed_simplicial_set.pi0prerelation (sSet.Fun (sSet.dom f)) x y"
  shows "pointed_simplicial_set.pi0prerelation (sSet.Fun (sSet.cod f)) (fst (the (ev_0_functor f)) x)
        (fst (the (ev_0_functor f)) y)" 
  unfolding sSet.Fun_dom [OF arr_f]
  unfolding sSet.Fun_cod [OF arr_f]
proof-
  interpret nat_f : natural_transformation Delta.comp pointed_set.pointed_set_comp
       "sSet.Dom f" "sSet.Cod f" "sSet.Fun f"
    using arr_f
    unfolding sSet.arr_char by simp
  interpret Dom: pointed_simplicial_set "sSet.Dom f"
    unfolding pointed_simplicial_set_def
    using nat_f.F.functor_axioms.
  interpret Cod: pointed_simplicial_set "sSet.Cod f"
    unfolding pointed_simplicial_set_def
    using nat_f.G.functor_axioms.
  show "Cod.pi0prerelation (fst (the (ev_0_functor f)) x) (fst (the (ev_0_functor f)) y)"
    unfolding Cod.pi0prerelation_def
    apply safe
  proof-
    show "fst (the (ev_0_functor f)) x \<in> snd (Cod.simplices 0)"
      unfolding ev_0_functor_simp [OF arr_f]
      apply (simp add: Cod.simplices_def ide_D0I)
      unfolding sSet_arr_cod_eq [OF arr_f ide_D0]
      apply (rule_tac P.arr_x_in_dom)
       apply (rule_tac nat_f.preserves_arr [OF arr_D0])
      using x_in_dom
      unfolding ev_0_functor_simp [OF arr_f].
    show "fst (the (ev_0_functor f)) y \<in> snd (Cod.simplices 0)"
      unfolding ev_0_functor_simp [OF arr_f]
      apply (simp add: Cod.simplices_def ide_D0I)
      unfolding sSet_arr_cod_eq [OF arr_f ide_D0]
      apply (rule_tac P.arr_x_in_dom)
       apply (rule_tac nat_f.preserves_arr [OF arr_D0])
      using y_in_dom
      unfolding ev_0_functor_simp [OF arr_f].

    from Rxy have "(\<exists>z\<in>snd (Dom.simplices 1).
      fst (the (sSet.Dom f (Delta.d 1 0))) z = x \<and> fst (the (sSet.Dom f (Delta.d 1 1))) z = y)"
      unfolding sSet.Fun_dom [OF arr_f]
      unfolding Dom.pi0prerelation_def by simp
    then obtain z where z_def: "z\<in>snd (Dom.simplices 1) \<and>
      fst (the (sSet.Dom f (Delta.d 1 0))) z = x \<and> fst (the (sSet.Dom f (Delta.d 1 1))) z = y"
      by auto
    from z_def have xz_eq : "x = fst (the (sSet.Dom f (Delta.d 1 0))) z" by simp
    from z_def have yz_eq : "y = fst (the (sSet.Dom f (Delta.d 1 1))) z" by simp
    show "\<exists>z\<in>snd (Cod.simplices 1).
       fst (the (sSet.Cod f (Delta.d 1 0))) z = fst (the (ev_0_functor f)) x \<and>
       fst (the (sSet.Cod f (Delta.d 1 1))) z = fst (the (ev_0_functor f)) y"
    proof
      define D1 where "D1 = Some (fin_set.Id' (Suc (Suc 0)))"
      have ide_D1 : "sSet.A.ide D1"
        unfolding D1_def 
        apply (rule_tac Delta.ide_Dn)
        by simp

      define fz where "fz = fst (the (sSet.Fun f D1)) z"
      show "fz \<in> snd (Cod.simplices 1)"
        unfolding fz_def
        apply (simp add: Cod.simplices_def)
        unfolding reverse_equality [OF D1_def]
        unfolding sSet_arr_cod_eq [OF arr_f ide_D1]
        apply (rule_tac P.arr_x_in_dom)
         apply (rule_tac nat_f.preserves_arr)
        using ide_D1 apply simp
        using z_def
        unfolding Dom.simplices_def
        using sSet_arr_dom_eq [OF arr_f sSet.A.ideD(1) [OF ide_D1]]
        unfolding D1_def by simp

      have dom_eq0 : "(Some (fin_set.Id' (Suc (Suc 0)))) =
                      sSet.A.dom (Delta.d 1 0)"
        apply (subst sSet.A.in_hom_dom [OF Delta.d_in_hom])
        by simp_all
      have dom_eq1 : "(Some (fin_set.Id' (Suc (Suc 0)))) =
                      sSet.A.dom (Delta.d 1 1)"
        apply (subst sSet.A.in_hom_dom [OF Delta.d_in_hom])
        by simp_all

      have cod_eq0 : "D0 = sSet.A.cod (Delta.d 1 0)"
        unfolding D0_def
        apply (subst sSet.A.in_hom_cod [OF Delta.d_in_hom])
        by (simp_all add: fin_set.Id'_def)
      have cod_eq1 : "D0 = sSet.A.cod (Delta.d 1 1)"
        unfolding D0_def
        apply (subst sSet.A.in_hom_cod [OF Delta.d_in_hom])
        by (simp_all add: fin_set.Id'_def)

      have "1 = Suc 0" by simp
      have "0 < Suc 0" by simp
      have arr_d0 : "sSet.A.arr (Delta.d 1 0)"
        apply (rule_tac sSet.A.in_homE [OF Delta.d_in_hom [OF \<open>0 < Suc 0\<close>]])
        unfolding \<open>1 = Suc 0\<close> by blast        
      have arr_d1 : "sSet.A.arr (Delta.d 1 1)"
        apply (rule_tac sSet.A.in_homE [OF Delta.d_in_hom [OF \<open>0 < Suc 0\<close>]])
        unfolding \<open>1 = Suc 0\<close> by blast    

      have seq0 : "sSet.B.seq (sSet.Cod f (Delta.d 1 0)) (sSet.Fun f (sSet.A.dom (Delta.d 1 0)))"
        apply (rule_tac sSet.B.seqI')
         apply (rule_tac nat_f.preserves_hom)
        using sSet.A.ide_dom [OF arr_d0]
        unfolding sSet.A.ide_in_hom apply blast
        apply (rule_tac nat_f.G.preserves_hom)
        apply (rule_tac sSet.A.in_homI [OF arr_d0])
        by simp_all

      have seq1 : "sSet.B.seq (sSet.Cod f (Delta.d 1 1)) (sSet.Fun f (sSet.A.dom (Delta.d 1 1)))"
        apply (rule_tac sSet.B.seqI')
         apply (rule_tac nat_f.preserves_hom)
        using sSet.A.ide_dom [OF arr_d1]
        unfolding sSet.A.ide_in_hom apply blast
        apply (rule_tac nat_f.G.preserves_hom)
        apply (rule_tac sSet.A.in_homI [OF arr_d1])
        by simp_all

      have seq0' :"sSet.B.seq (sSet.Fun f (sSet.A.cod (Delta.d 1 0))) (sSet.Dom f (Delta.d 1 0))"
        apply (rule_tac sSet.B.seqI')
         apply (rule_tac nat_f.F.preserves_hom)
         apply (rule_tac Delta.d_in_hom)
         apply simp
        apply (rule_tac nat_f.preserves_hom)
        apply (subst reverse_equality [OF sSet.A.in_hom_cod [OF Delta.d_in_hom]])
         apply simp
        apply (subst reverse_equality [OF sSet.A.ide_in_hom])
        by (rule_tac sSet.A.ide_cod [OF arr_d0])
      have seq1' :"sSet.B.seq (sSet.Fun f (sSet.A.cod (Delta.d 1 1))) (sSet.Dom f (Delta.d 1 1))"
        apply (rule_tac sSet.B.seqI')
         apply (rule_tac nat_f.F.preserves_hom)
         apply (rule_tac Delta.d_in_hom)
         apply simp
        apply (rule_tac nat_f.preserves_hom)
        apply (subst reverse_equality [OF sSet.A.in_hom_cod [OF Delta.d_in_hom]])
         apply simp
        apply (subst reverse_equality [OF sSet.A.ide_in_hom])
        by (rule_tac sSet.A.ide_cod [OF arr_d1])



      have z_in_dom0 : "z \<in> snd (fst (snd (the (sSet.Fun f (sSet.A.dom (Delta.d 1 0))))))"
        apply (subst reverse_equality [OF sSet_arr_dom_eq [OF arr_f]])
        using sSet.A.ide_dom [OF arr_d0] apply simp
        apply (subst sSet.A.in_hom_dom [OF Delta.d_in_hom])
        apply simp
        using z_def by (simp add: Dom.simplices_def)

      have z_in_dom1 : "z \<in> snd (fst (snd (the (sSet.Fun f (sSet.A.dom (Delta.d 1 1))))))"
        apply (subst reverse_equality [OF sSet_arr_dom_eq [OF arr_f]])
        using sSet.A.ide_dom [OF arr_d1] apply simp
        apply (subst sSet.A.in_hom_dom [OF Delta.d_in_hom])
        apply simp
        using z_def by (simp add: Dom.simplices_def)

      have "z \<in> snd (fst (snd (the (sSet.B.dom (sSet.Dom f (Delta.d 1 0))))))"
        unfolding nat_f.F.preserves_dom [OF arr_d0]
        apply (subst sSet.A.in_hom_dom [OF Delta.d_in_hom])
         apply simp
        using z_def by (simp add: Dom.simplices_def)
      then have z_in_dom0' : "z \<in> snd (fst (snd (the (sSet.Dom f (Delta.d 1 0)))))"
        unfolding P.dom_char [OF nat_f.F.preserves_arr [OF arr_d0]]
        by (simp add: pointed_set.Id'_def)

      have "z \<in> snd (fst (snd (the (sSet.B.dom (sSet.Dom f (Delta.d 1 1))))))"
        unfolding nat_f.F.preserves_dom [OF arr_d1]
        apply (subst sSet.A.in_hom_dom [OF Delta.d_in_hom])
         apply simp
        using z_def by (simp add: Dom.simplices_def)
      then have z_in_dom1' : "z \<in> snd (fst (snd (the (sSet.Dom f (Delta.d 1 1)))))"
        unfolding P.dom_char [OF nat_f.F.preserves_arr [OF arr_d1]]
        by (simp add: pointed_set.Id'_def)

      show "fst (the (sSet.Cod f (Delta.d 1 0)))
     (fst (the (sSet.Fun f (Some (fin_set.Id' (Suc (Suc 0)))))) z) =
    fst (the (ev_0_functor f)) x \<and>
    fst (the (sSet.Cod f (Delta.d 1 1)))
     (fst (the (sSet.Fun f (Some (fin_set.Id' (Suc (Suc 0)))))) z) =
    fst (the (ev_0_functor f)) y"
      proof
        show "fst (the (sSet.Cod f (Delta.d 1 0)))
     (fst (the (sSet.Fun f (Some (fin_set.Id' (Suc (Suc 0)))))) z) =
    fst (the (ev_0_functor f)) x"
          unfolding ev_0_functor_simp [OF arr_f]
          unfolding xz_eq
          apply (subst dom_eq0)
          apply (subst cod_eq0)
          apply (subst reverse_equality [OF pointed_set.fst_comp_char])
          using seq0 apply simp
          using z_in_dom0 apply simp
          apply (subst reverse_equality [OF nat_f.naturality [OF arr_d0]])
          apply (subst pointed_set.fst_comp_char)
          using seq0' apply simp
          using z_in_dom0' apply simp
          by simp
        show "fst (the (sSet.Cod f (Delta.d 1 1)))
     (fst (the (sSet.Fun f (Some (fin_set.Id' (Suc (Suc 0)))))) z) =
    fst (the (ev_0_functor f)) y"
          unfolding ev_0_functor_simp [OF arr_f]
          unfolding yz_eq
          apply (subst dom_eq1)
          apply (subst cod_eq1)
          apply (subst reverse_equality [OF pointed_set.fst_comp_char])
          using seq1 apply simp
          using z_in_dom1 apply simp
          apply (subst reverse_equality [OF nat_f.naturality [OF arr_d1]])
          apply (subst pointed_set.fst_comp_char)
          using seq1' apply simp
          using z_in_dom1' apply simp
          by simp
      qed
    qed
  qed
qed

        


interpretation pi0: quotient_functor sSet.comp ev_0_functor
       "(\<lambda>X. pointed_simplicial_set.pi0relation (sSet.Fun X))"
  unfolding quotient_functor_def
  apply (simp add: ev_0_functor)
  unfolding quotient_functor_axioms_def
  apply safe
proof-
  fix c :: "((nat \<times> nat list) option,
       (('a pointed_set.parr) option)) sSet_set.arr"
  assume c_nn: "c \<noteq> sSet.null"
  assume functor_c: "functor Delta.comp pointed_set.pointed_set_comp (sSet.Fun c)"
  assume dom_c: "sSet.Dom c = sSet.Fun c"
  assume cod_c: "sSet.Cod c = sSet.Fun c"
  from functor_c interpret C: pointed_simplicial_set "(sSet.Fun c)"
    unfolding pointed_simplicial_set_def.

  have "sSet.ide c"
    unfolding sSet.ide_char
    by (simp add: c_nn functor_c dom_c cod_c)

  have obj_eq: "(fst (snd (the (ev_0_functor c)))) = C.simplices 0"
    unfolding C.simplices_def
    apply (subst ev_0_functor_simp)
    using \<open>sSet.ide c\<close> apply simp
    unfolding D0_def fin_set.Id'_def
    by simp

  show "equiv (snd (fst (snd (the (ev_0_functor c))))) {(x, y). C.pi0relation x y}"
    unfolding C.pi0relation_def
    unfolding obj_eq
    apply (rule_tac generated_equiv_rel_equiv)
    unfolding C.pi0prerelation_def
    by auto
next
  fix f :: "((nat \<times> nat list) option,
       (('a \<Rightarrow> 'a) \<times> ('a \<times> 'a set) \<times> 'a \<times> 'a set) option) sSet_set.arr" 
  fix x y
  assume arr_f: "sSet.arr f"
  then interpret f_nat: natural_transformation Delta.comp pointed_set.pointed_set_comp 
           "(sSet.Dom f)" "(sSet.Cod f)" "(sSet.Fun f)"
    unfolding sSet.arr_char by simp

  assume x_in_dom : "x \<in> snd (fst (snd (the (ev_0_functor f))))"
  assume y_in_dom : "y \<in> snd (fst (snd (the (ev_0_functor f))))"

  have arr_f0 : "sSet.B.arr (sSet.Fun f (Some (fin_set.Id' 1)))"
    unfolding f_nat.preserves_reflects_arr
    unfolding fin_set.Id'_def
    using Delta.ide_D0 by simp

  interpret Dom : pointed_simplicial_set "sSet.Fun (sSet.dom f)"
    unfolding pointed_simplicial_set_def
    using sSet.ide_dom [OF arr_f]
    unfolding sSet.ide_char
    by simp
  interpret Cod : pointed_simplicial_set "sSet.Fun (sSet.cod f)"
    unfolding pointed_simplicial_set_def
    using sSet.ide_cod [OF arr_f]
    unfolding sSet.ide_char
    by simp
  assume Rxy: "Dom.pi0relation x y"
  show "Cod.pi0relation (fst (the (ev_0_functor f)) x)
                        (fst (the (ev_0_functor f)) y)"
    unfolding Cod.pi0relation_def
    unfolding generated_equiv_rel_def Cod.simplices_def
    apply auto
  proof-
    fix Q
    assume Q_equiv : "equiv (snd (fst (snd (the (sSet.Fun (sSet.cod f) (Some (fin_set.Id' (Suc 0))))))))
          {(x, y). Q x y}"
    assume RQ : "\<forall>x y. Cod.pi0prerelation x y \<longrightarrow> Q x y"
    then have RQ_rule : "\<And>x y. Cod.pi0prerelation x y \<Longrightarrow> Q x y" by simp
    define dom where "dom = (snd (fst (snd (the (sSet.Fun (sSet.dom f) (Some (fin_set.Id' (Suc 0))))))))"


    have arr_dom_f0 : "sSet.B.arr (sSet.Fun (sSet.dom f) (Some (fin_set.Id' 1)))"
      unfolding sSet.Fun_dom [OF arr_f]
      apply (rule_tac f_nat.F.preserves_arr)
      using Delta.ide_D0 by (simp add: fin_set.Id'_def)
    have "sSet.B.dom (sSet.Fun f (Some (fin_set.Id' 1))) =
          sSet.B.dom (sSet.Fun (sSet.dom f) (Some (fin_set.Id' 1)))"
      using Delta.ide_D0 apply (simp add: fin_set.Id'_def)
      unfolding sSet.dom_char
      apply (simp add: arr_f)
      unfolding sSet.mkArr_def
      apply (simp add: functor_is_transformation [OF f_nat.F.functor_axioms])
      unfolding sSet.Fun_def
      by (simp add: sSet.Abs_arr_inverse)
    then have dom_eq : "fst (snd (the (sSet.Fun f (Some (fin_set.Id' 1))))) =
                   fst (snd (the (sSet.Fun (sSet.dom f) (Some (fin_set.Id' (Suc 0))))))" 
      unfolding P.dom_char [OF arr_f0]
      unfolding P.dom_char [OF arr_dom_f0]
      by (simp add: pointed_set.Id'_def)
    have arr_cod_f0 : "sSet.B.arr (sSet.Fun (sSet.cod f) (Some (fin_set.Id' (Suc 0))))"
      unfolding sSet.Fun_cod [OF arr_f]
      apply (rule_tac f_nat.G.preserves_arr)
      using Delta.ide_D0 by (simp add: fin_set.Id'_def)

    have "sSet.A.cod (Some (fin_set.Id' 1)) = sSet.A.dom (Some (fin_set.Id' 1))"
      using Delta.ide_D0
      by (simp add: fin_set.Id'_def)
    then have "sSet.B.cod (sSet.Fun f (Some (fin_set.Id' 1))) =
          sSet.B.dom (sSet.Fun (sSet.cod f) (Some (fin_set.Id' (Suc 0))))"
      unfolding sSet.Fun_cod [OF arr_f]
      apply (subst f_nat.preserves_cod)
      using Delta.ide_D0 apply (simp add: fin_set.Id'_def)
      apply (subst f_nat.G.preserves_dom)
      using Delta.ide_D0 apply (simp add: fin_set.Id'_def)
      by simp
    then have cod_eq : "(snd (snd (the (sSet.Fun f (Some (fin_set.Id' 1)))))) = 
               (fst (snd (the (sSet.Fun (sSet.cod f) (Some (fin_set.Id' (Suc 0)))))))"
      unfolding P.cod_char [OF arr_f0]
      using P.dom_char [OF arr_cod_f0]
      by (simp add: pointed_set.Id'_def)

    define fQ where "fQ = (\<lambda>x y. x \<in> dom \<and> y \<in> dom \<and> Q (fst (the (ev_0_functor f)) x) (fst (the (ev_0_functor f)) y))"
    have fQ_equiv : "equiv dom {(x, y). fQ x y}"
      unfolding fQ_def
      apply (rule_tac equiv_preimage)
      using Q_equiv apply simp
      unfolding dom_def apply auto
      unfolding ev_0_functor_simp [OF arr_f]
      using P.arr_x_in_dom [OF arr_f0]
      unfolding dom_eq cod_eq
      unfolding D0_def fin_set.Id'_def by simp

    have RfQ : "\<forall>x y. Dom.pi0prerelation x y \<longrightarrow> fQ x y"
      unfolding fQ_def apply auto
    proof-
      fix x y
      assume Rxy: "Dom.pi0prerelation x y"
      from Rxy have xy_in_0: "x \<in> snd (Dom.simplices 0) \<and>
                 y \<in> snd (Dom.simplices 0)"
        unfolding Dom.pi0prerelation_def by simp
      show "x \<in> dom"
        using xy_in_0
        unfolding dom_def Dom.simplices_def by simp
      show "y \<in> dom"
        using xy_in_0
        unfolding dom_def Dom.simplices_def by simp
      show "Q (fst (the (ev_0_functor f)) x) (fst (the (ev_0_functor f)) y)"
        apply (rule_tac RQ_rule)
        apply (rule_tac pi0_restrict)
        using arr_f apply simp
        unfolding ev_0_functor_simp [OF arr_f]
        using dom_eq \<open>x \<in> dom\<close>
        unfolding dom_def D0_def fin_set.Id'_def
          apply simp
        using dom_eq \<open>y \<in> dom\<close>
        unfolding dom_def D0_def fin_set.Id'_def
         apply simp
        using Rxy.
    qed

    have "equiv (snd (Dom.simplices 0)) {(x, y). fQ x y} \<longrightarrow> (\<forall>x y. Dom.pi0prerelation x y \<longrightarrow> fQ x y) \<longrightarrow> fQ x y"
      using Rxy
      unfolding Dom.pi0relation_def generated_equiv_rel_def by blast
    then have "fQ x y"
      using fQ_equiv RfQ  unfolding dom_def
      by (simp add: Dom.simplices_def)

    show "Q (fst (the (ev_0_functor f)) x) (fst (the (ev_0_functor f)) y)"
      using \<open>fQ x y\<close>
      unfolding fQ_def by simp
  qed
qed



definition pi0 where
  "pi0 = pi0.quotient_functor"

lemma pi0_functor : "functor sSet.comp pointed_set.pointed_set_comp pi0"
  unfolding pi0_def
  using pi0.is_functor.




end



end

