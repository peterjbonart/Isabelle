theory SmashProduct
  imports Main
         PointedSet
          "Category3.NaturalTransformation"
          "Category3.ProductCategory"
          ColimitFunctoriality
          SimplicialSet
begin




interpretation P: pointed_set.






locale quotient_functor =
  F: "functor" FA P.pointed_set_comp F
  for FA :: "'c comp"
  and F :: "'c \<Rightarrow> 'a P.parr option"
  and R :: "'c \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" +
assumes R_equiv : "\<And>c. F.A.ide c \<Longrightarrow> equiv (snd (P.Dom' (the (F c)))) {(x,y). R c x y}"
 and    R_restrict : "\<And>f x y. F.A.arr f \<Longrightarrow> x \<in> snd (P.Dom' (the (F f))) \<Longrightarrow> y \<in> snd (P.Dom' (the (F f)))
                      \<Longrightarrow> R (F.A.dom f) x y \<Longrightarrow> R (F.A.cod f) (fst (the (F f)) x) (fst (the (F f)) y)"
begin



lemma quotient_cocone_translation : 
  assumes cocone : "F.B.in_hom g (Some (P.Id' A)) Z \<and> (\<forall>x y. Q x y \<longrightarrow> fst (the g) x = fst (the g) y)"
 shows "P.Arr' (the g) \<and>
    fst (snd (the g)) = A \<and>
    snd (snd (the g)) = fst (snd (the Z)) \<and> (\<forall>x y. Q x y \<longrightarrow> fst (the g) x = fst (the g) y)"
  apply (rule_tac F.B.in_homE [OF conjunct1 [OF cocone]])
  apply safe
proof-
  assume "F.B.arr g"
  then show "P.Arr' (the g)" 
    unfolding P.arr_char 
    by simp
  assume "F.B.dom g = Some (P.Id' A)"
  then show "P.Dom' (the g) = A"
    unfolding P.dom_char [OF \<open>F.B.arr g\<close>]
    by (simp add: P.Id'_def)
  show "snd (snd (the g)) = fst (snd (the (F.B.cod g)))"
    unfolding P.cod_char [OF \<open>F.B.arr g\<close>]
    by (simp add: P.Id'_def)
  fix x y
  assume "Q x y"
  then show "fst (the g) x = fst (the g) y"
    using cocone by simp
qed

lemma quotient_section_in_hom : assumes equiv: "equiv (snd A) {(x,y). Q x y}"
  and "P.Obj' A"
  shows "F.B.in_hom (Some (P.quotient_section A Q)) (Some (P.Id' (P.quotient_by_equiv_rel A Q))) (Some (P.Id' A))"
  apply (rule_tac F.B.in_homI)
proof-
  show arr_s: "F.B.arr (Some (P.quotient_section A Q))"
    unfolding P.arr_char
    using P.quot_sec_arr [OF equiv \<open>P.Obj' A\<close>]
    by simp
  show "F.B.dom (Some (P.quotient_section A Q)) = Some (P.Id' (P.quotient_by_equiv_rel A Q))"
    unfolding P.dom_char [OF arr_s]
    by simp
  show "F.B.cod (Some (P.quotient_section A Q)) = Some (P.Id' A)"
    unfolding P.cod_char [OF arr_s]
    by simp
qed

lemma quotient_UP_existence2 : assumes equiv: "equiv (snd A) {(x,y). Q x y}"
   and  cocone : "F.B.in_hom g (Some (P.Id' A)) Z \<and> (\<forall>x y. Q x y \<longrightarrow> fst (the g) x = fst (the g) y)"
  shows "F.B.in_hom (P.pointed_set_comp g (Some(P.quotient_section A Q))) (Some (P.Id' (P.quotient_by_equiv_rel A Q))) Z \<and>
         P.pointed_set_comp (P.pointed_set_comp g (Some(P.quotient_section A Q))) (Some (P.quotient_proj A Q)) = g"
proof
  have "P.Obj' A"
    apply (rule_tac F.B.in_homE [OF conjunct1 [OF cocone]])
  proof-
    assume "F.B.arr g"
    assume "F.B.dom g = Some (P.Id' A)"
    then have "P.Dom' (the g) = A"
      unfolding P.dom_char [OF \<open>F.B.arr g\<close>]
      by (simp add: P.Id'_def)
    then show "P.Obj' A"
      using \<open>F.B.arr g\<close>
      unfolding P.arr_char P.Arr'_def
      by simp
  qed

  show "F.B.in_hom (P.pointed_set_comp g (Some (P.quotient_section A Q))) (Some (P.Id' (P.quotient_by_equiv_rel A Q))) Z"
    apply (rule_tac F.B.comp_in_homI)
     apply (rule_tac quotient_section_in_hom [OF equiv \<open>P.Obj' A\<close>])
    using cocone by simp


  have UP_ex: "P.Arr' ((the g) \<cdot> P.quotient_section A Q) \<and>
  fst (snd ((the g) \<cdot> P.quotient_section A Q)) = P.quotient_by_equiv_rel A Q \<and>
  snd (snd ((the g) \<cdot> P.quotient_section A Q)) = (P.Dom' (the Z)) \<and>
  ((the g) \<cdot> P.quotient_section A Q) \<cdot> P.quotient_proj A Q = (the g)"
    apply (rule_tac P.quotient_UP_existence [OF equiv])
     apply (rule_tac quotient_cocone_translation)
     apply (rule_tac cocone)
    using \<open>P.Obj' A\<close>.
  then have UP_ex_eq : "((the g) \<cdot> P.quotient_section A Q) \<cdot> P.quotient_proj A Q = (the g)"
    by simp
  have "F.B.arr g"
    using conjunct1 [OF cocone] by blast


  define h where "h = P.pointed_set_comp g (Some (P.quotient_section A Q))"

  show "P.pointed_set_comp (P.pointed_set_comp g (Some (P.quotient_section A Q))) (Some (P.quotient_proj A Q)) = g"
    unfolding reverse_equality [OF h_def]
    apply (subst P.comp_char)
    unfolding h_def
  proof-
    show arr_proj: "F.B.arr (Some (P.quotient_proj A Q))"
      unfolding P.arr_char
      using P.quot_proj_arr [OF \<open>P.Obj' A\<close>] by simp
    show seq_gs: "F.B.seq g (Some (P.quotient_section A Q))"
      apply (rule_tac F.B.seqI')
      using quotient_section_in_hom [OF equiv \<open>P.Obj' A\<close>] apply simp
      using conjunct1 [OF cocone].
    show "F.B.dom (P.pointed_set_comp g (Some (P.quotient_section A Q))) = F.B.cod (Some (P.quotient_proj A Q))"
      apply (subst F.B.dom_comp [OF seq_gs])
      apply (subst P.dom_char)
       apply (rule_tac F.B.in_homE [OF quotient_section_in_hom [OF equiv \<open>P.Obj' A\<close>]])
       apply blast
      apply (subst P.cod_char [OF arr_proj])
      by simp

    show "Some (the (P.pointed_set_comp g (Some (P.quotient_section A Q))) \<cdot> the (Some (P.quotient_proj A Q))) = g"
      apply (subst P.comp_char)
         apply (rule_tac F.B.seqE [OF seq_gs])
         apply blast
        apply (rule_tac F.B.seqE [OF seq_gs])
        apply blast
       apply (rule_tac F.B.seqE [OF seq_gs])
       apply blast
      using UP_ex_eq apply simp
      using \<open>F.B.arr g\<close>
      unfolding P.arr_char by simp
  qed
qed




lemma quotient_UP_uniqueness2 : assumes equiv: "equiv (snd A) {(x,y). Q x y}"
   and  cocone : "F.B.in_hom g (Some (P.Id' A)) Z \<and> (\<forall>x y. Q x y \<longrightarrow> fst (the g) x = fst (the g) y)"
  shows "F.B.in_hom h (Some (P.Id' (P.quotient_by_equiv_rel A Q))) Z \<and>
         P.pointed_set_comp h (Some (P.quotient_proj A Q)) = g \<Longrightarrow>
         h = P.pointed_set_comp g (Some (P.quotient_section A Q))"
proof-
  have "P.Obj' A"
    apply (rule_tac F.B.in_homE [OF conjunct1 [OF cocone]])
  proof-
    assume "F.B.arr g"
    assume "F.B.dom g = Some (P.Id' A)"
    then have "P.Dom' (the g) = A"
      unfolding P.dom_char [OF \<open>F.B.arr g\<close>]
      by (simp add: P.Id'_def)
    then show "P.Obj' A"
      using \<open>F.B.arr g\<close>
      unfolding P.arr_char P.Arr'_def
      by simp
  qed
  have "F.B.arr g"
    using cocone by blast
  assume h_prop : "F.B.in_hom h (Some (P.Id' (P.quotient_by_equiv_rel A Q))) Z \<and>
                   P.pointed_set_comp h (Some (P.quotient_proj A Q)) = g"
  show "h = P.pointed_set_comp g (Some (P.quotient_section A Q))"
    apply (subst P.comp_char)
       apply (rule_tac F.B.in_homE [OF quotient_section_in_hom [OF equiv \<open>P.Obj' A\<close>]])
       apply blast
      apply (rule_tac F.B.in_homE [OF conjunct1 [OF cocone]])
      apply blast
     apply (rule_tac F.B.in_homE [OF quotient_section_in_hom [OF equiv \<open>P.Obj' A\<close>]])
     apply (rule_tac F.B.in_homE [OF conjunct1 [OF cocone]])
     apply auto[1]
    apply (subst Option.option.sel)
    apply (subst reverse_equality [OF P.quotient_UP_uniqueness])
    using equiv apply simp
       apply (rule_tac quotient_cocone_translation)
    using cocone apply blast
    using \<open>P.Obj' A\<close> apply simp
    apply safe
  proof-
    have "F.B.arr h"
      apply (rule_tac F.B.in_homE [OF conjunct1 [OF h_prop]])
      by simp
    show "P.Arr' (the h)"
      using \<open>F.B.arr h\<close>
      unfolding P.arr_char
      by simp
    then show "h = Some (the h)"
      using \<open>F.B.arr h\<close>
      unfolding P.arr_char
      by simp
    show "fst (snd (the h)) = P.quotient_by_equiv_rel A Q"
      apply (rule_tac F.B.in_homE [OF conjunct1 [OF h_prop]])   
      unfolding P.dom_char [OF \<open>F.B.arr h\<close>]
      by (simp add: P.Id'_def)
    show "snd (snd (the h)) = fst (snd (the Z))"
      apply (rule_tac F.B.in_homE [OF conjunct1 [OF h_prop]])
      unfolding P.cod_char [OF \<open>F.B.arr h\<close>]
      using P.Id'_def apply auto
      by (simp add: P.Id'_def)
    have arr_proj: "F.B.arr (Some (P.quotient_proj A Q))"
      unfolding P.arr_char
      using P.quot_proj_arr [OF \<open>P.Obj' A\<close>]
      by simp
    have seq: "F.B.dom h = F.B.cod (Some (P.quotient_proj A Q))"
      unfolding P.cod_char [OF arr_proj]
      apply (rule_tac F.B.in_homE [OF conjunct1 [OF h_prop]])
      by simp
    show "the h \<cdot> P.quotient_proj A Q = the g"
      using reverse_equality [OF conjunct2 [OF h_prop]]
      unfolding P.comp_char [OF arr_proj \<open>F.B.arr h\<close> seq]
      by simp
  qed
qed


definition quotient_proj2 where
  "quotient_proj2 = P.quotient_proj"

definition quotient_section2 where
  "quotient_section2 = P.quotient_section"


definition quotient_functor where
  "quotient_functor = MkFunctor FA P.pointed_set_comp
                      (\<lambda>f. P.pointed_set_comp (Some (quotient_proj2 (P.Cod' (the (F f))) (R (F.A.cod f))))
                           (P.pointed_set_comp (F f) 
                           (Some (quotient_section2 (P.Dom' (the (F f))) (R (F.A.dom f))))))"

lemma is_functor: "functor FA P.pointed_set_comp quotient_functor"
  unfolding functor_def
  apply (simp add: F.A.category_axioms P.is_category)
  unfolding functor_axioms_def
  apply safe
proof-
  fix f
  show "\<not> F.A.arr f \<Longrightarrow> quotient_functor f = F.B.null"
    unfolding quotient_functor_def by simp
  assume arr_f : "F.A.arr f"
  have arr_Ff: "F.B.arr (F f)"
    using F.preserves_arr [OF arr_f].
  have eq1: "\<And>f. F.A.arr f \<Longrightarrow> fst (snd (the (F f))) = fst (snd (the (F (F.A.dom f))))"
    unfolding reverse_equality [OF F.preserves_dom]
    unfolding P.dom_char [OF F.preserves_arr]
    by (simp add: P.Id'_def)
  have arr_qs_rule : "\<And>f. F.A.arr f \<Longrightarrow> F.B.arr (Some (quotient_section2 (fst (snd (the (F f)))) (R (F.A.dom f))))"
    unfolding P.arr_char
    apply simp
    apply (subst eq1)
    apply simp
    unfolding quotient_section2_def
    apply (rule_tac P.quot_sec_arr)
    using R_equiv apply simp
  proof-
    fix f
    assume "F.A.arr f"
    then have "F.B.arr (F (F.A.dom f))"
      using F.preserves_arr [OF F.A.ideD(1) [OF F.A.ide_dom]] by simp
    then show "P.Obj' (fst (snd (the (F (F.A.dom f)))))"
      unfolding P.arr_char P.Arr'_def by simp
  qed
  have arr_qs: "F.B.arr (Some (quotient_section2 (fst (snd (the (F f)))) (R (F.A.dom f))))"
    using arr_qs_rule [OF arr_f].

  have arr_qp_rule : "\<And>f. F.A.arr f \<Longrightarrow> F.B.arr (Some (quotient_proj2 (snd (snd (the (F f)))) (R (F.A.cod f))))"
    unfolding P.arr_char
    apply simp
    unfolding quotient_proj2_def
    apply (rule_tac P.quot_proj_arr)
    using F.preserves_arr
    unfolding P.arr_char P.Arr'_def by simp
  have arr_qp : "F.B.arr (Some (quotient_proj2 (snd (snd (the (F f)))) (R (F.A.cod f))))"
    using arr_qp_rule [OF arr_f].


  have seq1: "F.B.seq (F f) (Some (quotient_section2 (fst (snd (the (F f)))) (R (F.A.dom f))))"
    apply (rule_tac F.B.seqI)
      apply (simp add: arr_qs)
    using arr_Ff apply simp
    unfolding P.dom_char [OF arr_Ff]
    unfolding P.cod_char [OF arr_qs]
    unfolding quotient_section2_def
    by simp
    

  have seq2: "F.B.seq (Some (quotient_proj2 (snd (snd (the (F f)))) (R (F.A.cod f))))
     (P.pointed_set_comp (F f) (Some (quotient_section2 (fst (snd (the (F f)))) (R (F.A.dom f)))))"
    apply (rule_tac F.B.seqI)
    using seq1 apply simp
    using arr_qp apply simp
    apply (subst F.B.cod_comp [OF seq1])
    unfolding P.dom_char [OF arr_qp]
    unfolding P.cod_char [OF arr_Ff]
    unfolding quotient_proj2_def
    by simp


  show "F.B.arr (quotient_functor f)"
    unfolding quotient_functor_def
    apply (simp add: arr_f)
    using seq2.



  have arr_qs: "F.B.arr (Some (quotient_section2 (fst (snd (the (F.B.dom (F f))))) (R (F.A.dom f))))"
    using arr_qs_rule [OF F.A.ideD(1) [OF F.A.ide_dom [OF arr_f]]]
    unfolding F.preserves_dom [OF arr_f]
    unfolding F.A.dom_dom [OF arr_f] 
    by simp
  have arr_qp : "F.B.arr (Some (quotient_proj2 (snd (snd (the (F.B.dom (F f))))) (R (F.A.dom f))))"
    using arr_qp_rule [OF F.A.ideD(1) [OF F.A.ide_dom [OF arr_f]]]
    unfolding F.preserves_dom [OF arr_f]
    unfolding F.A.cod_dom [OF arr_f] 
    by simp
 
    
  show "F.B.dom (quotient_functor f) = quotient_functor (F.A.dom f)"
    unfolding quotient_functor_def
    apply (simp add: arr_f)
    apply (subst F.B.dom_comp [OF seq2])
    apply (subst F.B.dom_comp [OF seq1])
    unfolding reverse_equality [OF F.preserves_dom [OF arr_f]]
    apply (subst F.B.comp_ide_arr [OF F.B.ide_dom [OF arr_Ff]])
     apply (rule_tac F.B.seq_ide_arr [OF F.B.ide_dom [OF arr_Ff] arr_qs])
     apply (subst P.cod_char [OF arr_qs])
     apply (simp add: quotient_section2_def)
    using F.B.ide_dom [OF arr_Ff]
    unfolding P.ide_char apply simp
  proof-
    have dom_cod_eq : "snd (snd (the (F.B.dom (F f)))) = fst (snd (the (F.B.dom (F f))))"
      unfolding P.dom_char [OF arr_Ff]
      by (simp add: P.Id'_def)

    have comp_char: "P.pointed_set_comp (Some (quotient_proj2 (snd (snd (the (F.B.dom (F f))))) (R (F.A.dom f))))
     (Some (quotient_section2 (fst (snd (the (F.B.dom (F f))))) (R (F.A.dom f)))) = 
         Some (quotient_proj2 (snd (snd (the (F.B.dom (F f))))) (R (F.A.dom f)) \<cdot> 
               (quotient_section2 (fst (snd (the (F.B.dom (F f))))) (R (F.A.dom f))))"
      apply (subst P.comp_char [OF arr_qs arr_qp])
      unfolding P.dom_char [OF arr_qp]
                P.cod_char [OF arr_qs]
       apply (subst quotient_proj2_def)
      apply simp
       apply (subst quotient_section2_def)
       apply (simp add: dom_cod_eq)
      by simp
    have eq1: "fst (snd (the (F f))) = fst (snd (the (F.B.dom (F f))))"
      unfolding P.dom_char [OF arr_Ff]
      by (simp add: P.Id'_def)

    show "F.B.dom (Some (quotient_section2 (fst (snd (the (F f)))) (R (F.A.dom f)))) =
    P.pointed_set_comp (Some (quotient_proj2 (snd (snd (the (F.B.dom (F f))))) (R (F.A.dom f))))
     (Some (quotient_section2 (fst (snd (the (F.B.dom (F f))))) (R (F.A.dom f))))"
      apply (subst comp_char)
      apply (rule_tac reverse_equality)
      apply (subst dom_cod_eq)
      apply (subst quotient_proj2_def)
      apply (subst quotient_section2_def)
      apply (subst P.proj_sec_id)
      using R_equiv [OF F.A.ide_dom [OF arr_f]]
      unfolding F.preserves_dom [OF arr_f] apply simp
       apply (rule_tac classical_category.Obj_Dom [OF P.ccpf])
      using F.B.ideD(1) [OF F.B.ide_dom [OF arr_Ff]]
      unfolding F.preserves_dom [OF arr_f]
       apply (simp add: P.arr_char)
      apply (rule_tac reverse_equality)
      apply (subst P.dom_char)
      unfolding eq1
      apply (simp add: arr_qs)
      unfolding F.preserves_dom [OF arr_f]
      unfolding quotient_section2_def
      by simp
  qed
  have arr_qs: "F.B.arr (Some (quotient_section2 (fst (snd (the (F.B.cod (F f))))) (R (F.A.cod f))))"
    using arr_qs_rule [OF F.A.ideD(1) [OF F.A.ide_cod [OF arr_f]]]
    unfolding F.preserves_cod [OF arr_f]
    unfolding F.A.dom_cod [OF arr_f] 
    by simp
  have arr_qp : "F.B.arr (Some (quotient_proj2 (snd (snd (the (F.B.cod (F f))))) (R (F.A.cod f))))"
    using arr_qp_rule [OF F.A.ideD(1) [OF F.A.ide_cod [OF arr_f]]]
    unfolding F.preserves_cod [OF arr_f]
    unfolding F.A.cod_cod [OF arr_f] 
    by simp
 
    
  show "F.B.cod (quotient_functor f) = quotient_functor (F.A.cod f)"
    unfolding quotient_functor_def
    apply (simp add: arr_f)
    apply (subst F.B.cod_comp [OF seq2])
    unfolding reverse_equality [OF F.preserves_cod [OF arr_f]]
    apply (subst F.B.comp_ide_arr [OF F.B.ide_cod [OF arr_Ff]])
     apply (rule_tac F.B.seq_ide_arr [OF F.B.ide_cod [OF arr_Ff] arr_qs])
     apply (subst P.cod_char [OF arr_qs])
     apply (simp add: quotient_section2_def)
    using F.B.ide_cod [OF arr_Ff]
    unfolding P.ide_char apply simp
  proof-
    have cod_cod_eq : "snd (snd (the (F.B.cod (F f)))) = fst (snd (the (F.B.cod (F f))))"
      unfolding P.cod_char [OF arr_Ff]
      by (simp add: P.Id'_def)

    have comp_char: "P.pointed_set_comp (Some (quotient_proj2 (snd (snd (the (F.B.cod (F f))))) (R (F.A.cod f))))
     (Some (quotient_section2 (fst (snd (the (F.B.cod (F f))))) (R (F.A.cod f)))) = 
         Some (quotient_proj2 (snd (snd (the (F.B.cod (F f))))) (R (F.A.cod f)) \<cdot> 
               (quotient_section2 (fst (snd (the (F.B.cod (F f))))) (R (F.A.cod f))))"
      apply (subst P.comp_char [OF arr_qs arr_qp])
      unfolding P.dom_char [OF arr_qp]
                P.cod_char [OF arr_qs]
       apply (subst quotient_proj2_def)
      apply simp
       apply (subst quotient_section2_def)
       apply (simp add: cod_cod_eq)
      by simp
    have eq1: "snd (snd (the (F f))) = snd (snd (the (F.B.cod (F f))))"
      unfolding P.cod_char [OF arr_Ff]
      by (simp add: P.Id'_def)
    have eq2: "snd (snd (the (F (F.A.cod f)))) = fst (snd (the (F (F.A.cod f))))"
      unfolding reverse_equality [OF F.preserves_cod [OF arr_f]]
      unfolding P.cod_char [OF arr_Ff]
      by (simp add: P.Id'_def)

    show "F.B.cod (Some (quotient_proj2 (snd (snd (the (F f)))) (R (F.A.cod f)))) =
    P.pointed_set_comp (Some (quotient_proj2 (snd (snd (the (F.B.cod (F f))))) (R (F.A.cod f))))
     (Some (quotient_section2 (fst (snd (the (F.B.cod (F f))))) (R (F.A.cod f))))"
      apply (subst comp_char)
      apply (rule_tac reverse_equality)
      apply (subst cod_cod_eq)
      apply (subst quotient_proj2_def)
      apply (subst quotient_section2_def)
      apply (subst P.proj_sec_id)
      using R_equiv [OF F.A.ide_cod [OF arr_f]]
      unfolding F.preserves_cod [OF arr_f] apply simp
       apply (rule_tac classical_category.Obj_Dom [OF P.ccpf])
      using F.B.ideD(1) [OF F.B.ide_cod [OF arr_Ff]]
      unfolding F.preserves_cod [OF arr_f]
       apply (simp add: P.arr_char)
      apply (rule_tac reverse_equality)
      apply (subst P.cod_char)
      unfolding eq1
      apply (simp add: arr_qp)
      unfolding F.preserves_cod [OF arr_f]
      unfolding quotient_proj2_def
      using eq2
      by simp
  qed
next
  fix g f
  assume arr_gf: "F.A.seq g f"
  from arr_gf have arr_f: "F.A.arr f"
    by blast
  from arr_gf have arr_g: "F.A.arr g"
    by blast
  from arr_gf have "F.A.dom g = F.A.cod f" 
    by blast
  have arr_Fgf : "F.B.seq (F g) (F f)"
    using F.preserves_arr [OF arr_gf]
    unfolding F.preserves_comp [OF arr_gf].

  have seq1: "fst (snd (the (F g))) = snd (snd (the (F f)))"
    apply (rule_tac F.B.seqE [OF arr_Fgf])
    using P.dom_char [OF F.preserves_arr [OF arr_g]] 
          P.cod_char [OF F.preserves_arr [OF arr_f]]
    unfolding P.Id'_def
    by simp

  define pi_f where "pi_f = (Some (quotient_proj2 (snd (snd (the (F f)))) (R (F.A.cod f))))"
  define pi_g where "pi_g = (Some (quotient_proj2 (snd (snd (the (F g)))) (R (F.A.cod g))))"
  define pi_gf where "pi_gf = (Some (quotient_proj2 (snd (snd (the (P.pointed_set_comp (F g) (F f))))) (R (F.A.cod g))))"
  define s_f where "s_f = (Some (quotient_section2 (fst (snd (the (F f)))) (R (F.A.dom f))))"
  define s_g where "s_g = (Some (quotient_section2 (fst (snd (the (F g)))) (R (F.A.cod f))))"
  define s_gf where "s_gf = (Some (quotient_section2 (fst (snd (the (P.pointed_set_comp (F g) (F f))))) (R (F.A.dom f))))"

  define g_UP_map where "g_UP_map = (P.pointed_set_comp pi_g (F g))"

  define R_f where "R_f = R (F.A.cod f)"


  have "P.Obj' (P.Cod' (the (F g)))"
    apply (rule_tac classical_category.Obj_Cod [OF P.ccpf])
    using F.preserves_arr [OF arr_g]
    unfolding P.arr_char by simp


  have EQ: "P.pointed_set_comp (P.pointed_set_comp g_UP_map s_g) pi_f
        = g_UP_map"
    unfolding s_g_def pi_f_def
    unfolding quotient_section2_def
              quotient_proj2_def
              seq1
    unfolding reverse_equality [OF R_f_def]
    apply (subst quotient_UP_existence2)
      apply (subst R_f_def)
    using R_equiv [OF F.A.ide_cod [OF arr_f]]
    unfolding reverse_equality [OF F.preserves_cod [OF arr_f]]
    unfolding P.cod_char [OF F.preserves_arr [OF arr_f]]
    apply (simp add: P.Id'_def)
     apply auto
  proof-
    show g_UP_in_hom: "F.B.in_hom g_UP_map (Some (P.Id' (snd (snd (the (F f)))))) (F.B.cod pi_g)"
      unfolding g_UP_map_def
      apply (rule_tac F.B.comp_in_homI)
       apply (subst reverse_equality [OF seq1])
       apply (subst reverse_equality [OF P.dom_char [OF F.preserves_arr [OF arr_g]]])
      using F.B.in_homI [OF F.preserves_arr [OF arr_g]] apply blast
      apply (rule_tac F.B.in_homI)
    proof-
      show "F.B.arr pi_g"
        unfolding pi_g_def
        unfolding quotient_proj2_def
        unfolding P.arr_char
        using P.quot_proj_arr [OF \<open>P.Obj' (P.Cod' (the (F g)))\<close>]
        unfolding Option.option.sel
        by blast
      show "F.B.dom pi_g = F.B.cod (F g)"
        unfolding P.dom_char [OF \<open>F.B.arr pi_g\<close>]
        unfolding P.cod_char [OF F.preserves_arr [OF arr_g]]
        unfolding pi_g_def quotient_proj2_def
        by simp
      show "F.B.cod pi_g = F.B.cod pi_g"
        by simp
    qed
    then have "F.B.arr g_UP_map"
      by blast
    then have seq_pig_fg: "F.B.seq pi_g (F g)"
      unfolding g_UP_map_def.


    have dom_eq : "fst (snd (the (F (F.A.cod f)))) = fst (snd (the (F g)))"
      unfolding seq1
      unfolding reverse_equality [OF F.preserves_cod [OF arr_f]]
      unfolding P.cod_char [OF F.preserves_arr [OF arr_f]]
      by (simp add: P.Id'_def)

    fix x y
    assume "R_f x y"
    then have "x \<in> snd (fst (snd (the (F (F.A.cod f)))))"
      unfolding R_f_def
      using R_equiv [OF F.A.ide_cod [OF arr_f]]
      unfolding equiv_def refl_on_def by auto
    then have x_in_dom : "x \<in> snd (fst (snd (the (F g))))"
      unfolding dom_eq.

    from \<open>R_f x y\<close> have "y \<in> snd (fst (snd (the (F (F.A.cod f)))))"
      unfolding R_f_def
      using R_equiv [OF F.A.ide_cod [OF arr_f]]
      unfolding equiv_def refl_on_def by auto
    then have y_in_dom : "y \<in> snd (fst (snd (the (F g))))"
      unfolding dom_eq.

    show "fst (the g_UP_map) x = fst (the g_UP_map) y"
      unfolding g_UP_map_def
      apply (subst P.fst_comp_char [OF seq_pig_fg x_in_dom])
      apply (subst P.fst_comp_char [OF seq_pig_fg y_in_dom])
      unfolding pi_g_def quotient_proj2_def
      unfolding Option.option.sel
      apply (rule_tac P.R_implies_quot_eq)
      using R_equiv [OF F.A.ide_cod [OF arr_g]]
      unfolding reverse_equality [OF F.preserves_cod [OF arr_g]]
      unfolding P.cod_char [OF F.preserves_arr [OF arr_g]]
      unfolding P.Id'_def
         apply simp
        apply (rule_tac R_restrict [OF arr_g])
      using x_in_dom apply simp
      using y_in_dom apply simp
      using \<open>R_f x y\<close>
      unfolding R_f_def
      unfolding \<open>F.A.dom g = F.A.cod f\<close>
      apply simp
    proof-
      show fx_in: "fst (the (F g)) x \<in> snd (snd (snd (the (F g))))"
        apply (rule_tac P.arr_x_in_dom)
         apply (rule_tac F.preserves_arr [OF arr_g])
        using x_in_dom.
      show fy_in: "fst (the (F g)) y \<in> snd (snd (snd (the (F g))))"
        apply (rule_tac P.arr_x_in_dom)
         apply (rule_tac F.preserves_arr [OF arr_g])
        using y_in_dom.
    qed
  qed
  have "F.B.cod (F g) = F.B.cod (P.pointed_set_comp (F g) (F f))"
    apply (subst F.B.cod_comp [OF arr_Fgf])
    by simp
  then have "snd (snd (the (F g))) = (snd (snd (the (P.pointed_set_comp (F g) (F f)))))"
    unfolding P.cod_char [OF F.preserves_arr [OF arr_g]]
    unfolding P.cod_char [OF arr_Fgf]
    by (simp add: P.Id'_def)
  then have pig_pigf : "pi_g = pi_gf"
    unfolding pi_g_def pi_gf_def by simp

  have "F.B.dom (F f) = F.B.dom (P.pointed_set_comp (F g) (F f))"
    apply (subst F.B.dom_comp [OF arr_Fgf])
    by simp
  then have "fst (snd (the (F f))) = (fst (snd (the (P.pointed_set_comp (F g) (F f)))))" 
    unfolding P.dom_char [OF F.preserves_arr [OF arr_f]]
    unfolding P.dom_char [OF arr_Fgf]
    by (simp add: P.Id'_def)
  then have sf_sgf : "s_f = s_gf"
    unfolding s_f_def s_gf_def by simp

  have assoc: "P.pointed_set_comp (P.pointed_set_comp pi_g (P.pointed_set_comp (F g) s_g))
     (P.pointed_set_comp pi_f (P.pointed_set_comp (F f) s_f)) = 
      P.pointed_set_comp (P.pointed_set_comp (P.pointed_set_comp (P.pointed_set_comp pi_g (F g)) s_g)
      pi_f) (P.pointed_set_comp (F f) s_f)"
    unfolding F.B.comp_assoc by simp

  show "quotient_functor (FA g f) = P.pointed_set_comp (quotient_functor g) (quotient_functor f)"
    unfolding quotient_functor_def
    apply (rule_tac F.A.seqE [OF arr_gf])
    apply (simp add: arr_gf)
    unfolding reverse_equality [OF pi_f_def]
    unfolding reverse_equality [OF pi_g_def]
    unfolding reverse_equality [OF pi_gf_def]
    unfolding reverse_equality [OF s_f_def]
    unfolding reverse_equality [OF s_g_def]
    unfolding reverse_equality [OF s_gf_def]
    apply (subst assoc)
    unfolding reverse_equality [OF g_UP_map_def]
    apply (subst EQ)
    unfolding g_UP_map_def
    unfolding F.B.comp_assoc
    apply (subst pig_pigf)
    apply (subst sf_sgf)
    by simp
qed



end

locale pointed_set_product_functor
begin

interpretation S: category P.pointed_set_comp
  using P.is_category.

definition product where
  "product A B = Some (P.Id' (P.pointed_product [P.Dom' (the A),P.Dom' (the B)]))"

definition projection1 where
  "projection1 A B = Some (P.prod_proj [P.Dom' (the A),P.Dom' (the B)] 0)"

definition projection2 where
  "projection2 A B = Some (P.prod_proj [P.Dom' (the A),P.Dom' (the B)] 1)"

definition product_UP_map where
  "product_UP_map f g = Some (P.prod_UP_map [the f, the g] (P.Dom' (the f)))"



lemma pointed_set_cat_with_products_axioms123 : 
 "\<And>a b. S.ide a \<Longrightarrow> S.ide b \<Longrightarrow> S.ide (product a b)
   \<and> S.in_hom (projection1 a b) (product a b) a
   \<and> S.in_hom (projection2 a b) (product a b) b" 
  apply safe
proof-
  fix a :: "'a P.LC P.parr option" 
  fix b :: "'a P.LC P.parr option"
  assume "S.ide a"
  then have obj_a: "P.Obj' (fst (snd (the a)))"
    unfolding P.ide_char P.Arr'_def by simp
  assume "S.ide b"
  then have obj_b: "P.Obj' (fst (snd (the b)))"
    unfolding P.ide_char P.Arr'_def by simp

  have ab_obj : "\<forall>n<length [fst (snd (the a)), fst (snd (the b))]. P.Obj' (get [fst (snd (the a)), fst (snd (the b))] n)"
    apply auto
  proof-
    fix n
    assume "n < Suc (Suc 0)"
    then have "n = 0 \<or> n = 1" by auto
    then show "P.Obj' (get [fst (snd (the a)), fst (snd (the b))] n)"
    proof
      show "n = 0 \<Longrightarrow> P.Obj' (get [fst (snd (the a)), fst (snd (the b))] n)"
        by (simp add: obj_a)
      show "n = 1 \<Longrightarrow> P.Obj' (get [fst (snd (the a)), fst (snd (the b))] n)"
        by (simp add: obj_b)
    qed
  qed

  show "S.ide (product a b)"
    unfolding product_def P.ide_char
    apply (rule_tac conjI)
    unfolding Option.option.sel
     apply (rule_tac classical_category.Arr_Id [OF P.ccpf])
     apply (rule_tac P.pointed_product_obj [OF ab_obj])
    unfolding P.Id'_def by simp
  show "S.in_hom (projection1 a b) (product a b) a"
    apply (rule_tac S.in_homI)
  proof-
    show arr_proj: "S.arr (projection1 a b)"
      unfolding projection1_def P.arr_char
      using P.prod_proj_arr [OF ab_obj] by simp
    show "S.dom (projection1 a b) = product a b"
      unfolding P.dom_char [OF arr_proj]
      unfolding projection1_def P.prod_proj_def
                product_def
      by simp
    show "S.cod (projection1 a b) = a"
      unfolding P.cod_char [OF arr_proj]
      unfolding projection1_def P.prod_proj_def
      apply simp
      using \<open>S.ide a\<close>
      unfolding P.ide_char by simp
  qed
  show "S.in_hom (projection2 a b) (product a b) b"
    apply (rule_tac S.in_homI)
  proof-
    show arr_proj: "S.arr (projection2 a b)"
      unfolding projection2_def P.arr_char
      using P.prod_proj_arr [OF ab_obj] by simp
    show "S.dom (projection2 a b) = product a b"
      unfolding P.dom_char [OF arr_proj]
      unfolding projection2_def P.prod_proj_def
                product_def
      by simp
    show "S.cod (projection2 a b) = b"
      unfolding P.cod_char [OF arr_proj]
      unfolding projection2_def P.prod_proj_def
      apply simp
      using \<open>S.ide b\<close>
      unfolding P.ide_char by simp
  qed
qed

interpretation Cat_with_products: category_with_products 
       P.pointed_set_comp 
       product
       projection1
       projection2
       product_UP_map
  unfolding category_with_products_def
  unfolding category_with_products_axioms_def binary_product_def
  apply (simp add: P.is_category)
  unfolding binary_product_axioms_def
  apply (simp add: pointed_set_cat_with_products_axioms123)
  apply safe
proof-
  fix f :: "'a P.LC P.parr option" 
  fix g :: "'a P.LC P.parr option"
  assume arr_f: "S.arr f"
  assume arr_g: "S.arr g"
  assume "S.dom f = S.dom g"
  then have dom_eq : "fst (snd (the f)) = fst (snd (the g))"
    unfolding P.dom_char [OF arr_f]
    unfolding P.dom_char [OF arr_g]
    by (simp add: P.Id'_def)

  from arr_f have obj_dom: "P.Obj' (fst (snd (the f)))"
    unfolding P.arr_char P.Arr'_def by blast
 
  have cocone: "\<forall>k<length [the f, the g]. P.Arr' (get [the f, the g] k) \<and>
                     fst (snd (get [the f, the g] k)) = P.Dom' (the f) \<and>
                     snd (snd (get [the f, the g] k)) = get [P.Cod' (the f), P.Cod' (the g)] k"
    apply (rule_tac allI)
  proof
    fix k
    assume "k < length [the f, the g]"
    then have "k = 0 \<or> k = 1" by auto
    then show "P.Arr' (get [the f, the g] k) \<and>
         fst (snd (get [the f, the g] k)) = fst (snd (the f)) \<and>
         snd (snd (get [the f, the g] k)) = get [snd (snd (the f)), snd (snd (the g))] k"
    proof
      show "k = 0 \<Longrightarrow>
    P.Arr' (get [the f, the g] k) \<and>
    fst (snd (get [the f, the g] k)) = fst (snd (the f)) \<and>
    snd (snd (get [the f, the g] k)) = get [snd (snd (the f)), snd (snd (the g))] k"
        using arr_f unfolding P.arr_char by simp
      show "k = 1 \<Longrightarrow>
    P.Arr' (get [the f, the g] k) \<and>
    fst (snd (get [the f, the g] k)) = fst (snd (the f)) \<and>
    snd (snd (get [the f, the g] k)) = get [snd (snd (the f)), snd (snd (the g))] k"
        using arr_g dom_eq unfolding P.arr_char by simp
    qed
  qed

  show up_in_hom: "S.in_hom (product_UP_map f g) (S.dom g) (product (S.cod f) (S.cod g))"
    apply (rule_tac S.in_homI)
  proof-
    show arr_up: "S.arr (product_UP_map f g)"
      unfolding product_UP_map_def P.arr_char
      using P.prod_UP_map_arr [OF cocone obj_dom]
      by simp
    show "S.dom (product_UP_map f g) = S.dom g"
      unfolding reverse_equality [OF \<open>S.dom f = S.dom g\<close>]
      unfolding P.dom_char [OF arr_up] P.dom_char [OF arr_f]
      unfolding product_UP_map_def P.prod_UP_map_def
      by simp
    show "S.cod (product_UP_map f g) = product (S.cod f) (S.cod g)"
      unfolding P.cod_char [OF arr_up] P.cod_char [OF arr_f] P.cod_char [OF arr_g]
      unfolding product_UP_map_def P.prod_UP_map_def product_def
      by (simp add: P.Id'_def)
  qed
  show "P.pointed_set_comp (projection1 (S.cod f) (S.cod g)) (product_UP_map f g) = f"
    apply (rule_tac P.comp_eq_char2)
        apply (rule_tac S.seqI')
    using up_in_hom apply simp
    using pointed_set_cat_with_products_axioms123
          [OF S.ide_cod [OF arr_f] S.ide_cod [OF arr_g]] apply blast
    using arr_f apply simp
    using S.in_hom_dom [OF up_in_hom] \<open>S.dom f = S.dom g\<close> apply simp
    using pointed_set_cat_with_products_axioms123
          [OF S.ide_cod [OF arr_f] S.ide_cod [OF arr_g]]
          S.in_hom_cod apply blast
    unfolding product_UP_map_def projection1_def P.prod_UP_map_def P.prod_proj_def
    by simp
  show "P.pointed_set_comp (projection2 (S.cod f) (S.cod g)) (product_UP_map f g) = g"
    apply (rule_tac P.comp_eq_char2)
        apply (rule_tac S.seqI')
    using up_in_hom apply simp
    using pointed_set_cat_with_products_axioms123
          [OF S.ide_cod [OF arr_f] S.ide_cod [OF arr_g]] apply blast
    using arr_g apply simp
    using S.in_hom_dom [OF up_in_hom] \<open>S.dom f = S.dom g\<close> apply simp
    using pointed_set_cat_with_products_axioms123
          [OF S.ide_cod [OF arr_f] S.ide_cod [OF arr_g]]
          S.in_hom_cod apply blast
    unfolding product_UP_map_def projection2_def P.prod_UP_map_def P.prod_proj_def
    by simp
  fix h
  assume h_in_hom: "S.in_hom h (S.dom g) (product (S.cod f) (S.cod g))" 
  assume h_prop1: "P.pointed_set_comp (projection1 (S.cod f) (S.cod g)) h = f"
  assume h_prop2: "P.pointed_set_comp (projection2 (S.cod f) (S.cod g)) h = g"

  have "S.arr h"
    using h_in_hom by blast


  have EQ: "the h = the (product_UP_map f g)"
    unfolding product_UP_map_def
    apply simp
    apply (rule_tac P.productUP_uniqueness)
    using cocone apply blast
    using obj_dom apply simp
     apply simp
    apply safe
  proof-
    from \<open>S.arr h\<close> show "P.Arr' (the h)"
      unfolding P.arr_char by simp
    have "Some (P.Id' (P.Dom' (the h))) = Some (P.Id' (P.Dom' (the f)))"
      apply (rule_tac S.in_homE [OF h_in_hom])
      using \<open>S.dom f = S.dom g\<close>
      unfolding P.dom_char [OF arr_f] P.dom_char
      by simp
    then show "fst (snd (the h)) = fst (snd (the f))"
      by (simp add: P.Id'_def)
    have "Some (P.Id' (P.Cod' (the h))) = Some (P.Id' (P.pointed_product [snd (snd (the f)), snd (snd (the g))]))"
      apply (rule_tac S.in_homE [OF h_in_hom])
      unfolding P.cod_char product_def
      unfolding P.cod_char [OF arr_f] P.cod_char [OF arr_g]
      by (simp add: P.Id'_def)
    then show "snd (snd (the h)) = P.pointed_product [snd (snd (the f)), snd (snd (the g))]"
      by (simp add: P.Id'_def)
    fix k
    assume "k < length [the f, the g]"
    then have "k = 0 \<or> k = 1" by auto
    then show "P.prod_proj [snd (snd (the f)), snd (snd (the g))] k \<cdot> the h = get [the f, the g] k"
    proof

      assume "k = 0"
      have p1_in_hom : "S.in_hom (projection1 (S.cod f) (S.cod g)) (product (S.cod f) (S.cod g)) (S.cod f)"
        using pointed_set_cat_with_products_axioms123 
              [OF S.ide_cod [OF arr_f] S.ide_cod [OF arr_g]]
        by simp
      then have arr_p1: "S.arr (projection1 (S.cod f) (S.cod g))"
        by blast
      have seq1: "S.dom (projection1 (S.cod f) (S.cod g)) = S.cod h"
        apply (rule_tac S.in_homE [OF p1_in_hom])
        apply (rule_tac S.in_homE [OF h_in_hom])
        by simp
      from \<open>k = 0\<close> show "P.prod_proj [snd (snd (the f)), snd (snd (the g))] k \<cdot> the h = get [the f, the g] k"
        apply simp
        apply (rule_tac reverse_equality)
        apply (subst reverse_equality [OF h_prop1])
        unfolding P.comp_char [OF \<open>S.arr h\<close> arr_p1 seq1]
        unfolding projection1_def
        unfolding P.cod_char [OF arr_f]
        unfolding P.cod_char [OF arr_g]
        unfolding P.Id'_def
        by simp
    next
      assume "k = 1"
      have p2_in_hom : "S.in_hom (projection2 (S.cod f) (S.cod g)) (product (S.cod f) (S.cod g)) (S.cod g)"
        using pointed_set_cat_with_products_axioms123 
              [OF S.ide_cod [OF arr_f] S.ide_cod [OF arr_g]]
        by simp
      then have arr_p2: "S.arr (projection2 (S.cod f) (S.cod g))"
        by blast
      have seq2: "S.dom (projection2 (S.cod f) (S.cod g)) = S.cod h"
        apply (rule_tac S.in_homE [OF p2_in_hom])
        apply (rule_tac S.in_homE [OF h_in_hom])
        by simp
      from \<open>k = 1\<close> show "P.prod_proj [snd (snd (the f)), snd (snd (the g))] k \<cdot> the h = get [the f, the g] k"
        apply simp
        apply (rule_tac reverse_equality)
        apply (subst reverse_equality [OF h_prop2])
        unfolding P.comp_char [OF \<open>S.arr h\<close> arr_p2 seq2]
        unfolding projection2_def
        unfolding P.cod_char [OF arr_f]
        unfolding P.cod_char [OF arr_g]
        unfolding P.Id'_def
        by simp
    qed
  qed
  show "h = product_UP_map f g"
    using reverse_equality [OF EQ]
    unfolding product_UP_map_def
    unfolding Option.option.sel
    apply simp
    using \<open>S.arr h\<close>
    unfolding P.arr_char by simp
qed
        
definition product_functor where
  "product_functor = Cat_with_products.prod_functor"

lemma product_functor : "functor 
                    (product_category.comp P.pointed_set_comp P.pointed_set_comp) 
                    P.pointed_set_comp 
                    product_functor"
  unfolding product_functor_def
  using Cat_with_products.prod_functor.



definition wedge_product :: "'a P.LC pointed_set list \<Rightarrow> 'a P.LC pointed_set" where 
  "wedge_product X = (P.Join (rev_get (length X) (\<lambda>n. fst (get X n))) ,
                      {x. \<exists>xs. x = P.Join xs \<and> length xs = length X \<and>
                       (\<exists>n < length X. get xs n \<in> snd (get X n) \<and> 
                       (\<forall>m< length X. m \<noteq> n \<longrightarrow> get xs m = fst (get X m)))})"

lemma wedge_subseteq_product : 
  assumes X_obj : "\<forall>k < length X. P.Obj' (get X k)"
  shows "snd (wedge_product X) \<subseteq> snd (P.pointed_product X)"
  unfolding wedge_product_def
  apply auto
proof-
  fix xs n m
  assume n_in_X: "get xs n \<in> snd (get X n)"
  assume m_fst_X: "\<forall>m<length X. m \<noteq> n \<longrightarrow> get xs m = fst (get X m)"
  assume "m < length X"
  have "n = m \<or> n \<noteq> m" by simp
  then show "get xs m \<in> snd (get X m)"
  proof
    show "n = m \<Longrightarrow> get xs m \<in> snd (get X m)"
      using n_in_X by simp
    assume "n \<noteq> m"
    then have "get xs m = fst (get X m)"
      using m_fst_X \<open>m < length X\<close> by simp
    then show "get xs m \<in> snd (get X m)"
      using X_obj \<open>m < length X\<close>
      unfolding P.Obj'_def by simp
  qed
qed


definition quotient_wedge_relation :: "('a P.LC P.parr option \<times> 'a P.LC P.parr option
                                         \<Rightarrow> 'a P.LC \<Rightarrow> 'a P.LC \<Rightarrow> bool)"  where
  "quotient_wedge_relation p = P.cur_rel (P.subset_eq_relation 
            (snd (P.pointed_product [P.Dom' (the (fst p)), P.Dom' (the (snd p))])) 
            (snd (wedge_product [P.Dom' (the (fst p)), P.Dom' (the (snd p))])) )"

interpretation SxS: product_category P.pointed_set_comp P.pointed_set_comp
  unfolding product_category_def
  by (simp add: S.category_axioms)

lemma prod_functor_wedge_restrict :
  assumes arr_a: "S.arr a" and arr_b: "S.arr b"
  shows "\<And>x. x \<in> snd (wedge_product [fst (snd (the (S.dom a))), fst (snd (the (S.dom b)))]) \<Longrightarrow>
              fst (the (local.product_functor (a, b))) x
     \<in> snd (wedge_product [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))])" 
proof-
  define ab_dom where "ab_dom = [fst (snd (the (S.dom a))), fst (snd (the (S.dom b)))]"
  have ab_dom_length: "length ab_dom = Suc (Suc 0)"
    unfolding ab_dom_def by simp
  have ab_dom_obj : "\<forall>k<length ab_dom. P.Obj' (get ab_dom k)"
    unfolding ab_dom_def
    apply auto
  proof-
    fix k
    assume "k < Suc (Suc 0)"
    then have "k = 0 \<or> k = 1" by auto
    then show "P.Obj' (get [fst (snd (the (S.dom a))), fst (snd (the (S.dom b)))] k)"
    proof
      show "k = 0 \<Longrightarrow> P.Obj' (get [fst (snd (the (S.dom a))), fst (snd (the (S.dom b)))] k)"
        apply simp
        apply (rule_tac classical_category.Obj_Dom [OF P.ccpf])
        using S.ideD(1) [OF S.ide_dom [OF arr_a]]
        unfolding P.arr_char by simp
      show "k = 1 \<Longrightarrow> P.Obj' (get [fst (snd (the (S.dom a))), fst (snd (the (S.dom b)))] k)"
        apply simp
        apply (rule_tac classical_category.Obj_Dom [OF P.ccpf])
        using S.ideD(1) [OF S.ide_dom [OF arr_b]]
        unfolding P.arr_char by simp
    qed
  qed

  fix x
  assume "x \<in> snd (wedge_product [fst (snd (the (S.dom a))), fst (snd (the (S.dom b)))])"
  then have x_in_wedge : "x \<in> snd (wedge_product ab_dom)"
    unfolding ab_dom_def.
  then obtain xs where xs_def: "x = P.Join xs \<and>
         length xs = Suc (Suc 0) \<and>
         (\<exists>n<Suc (Suc 0).
             get xs n \<in> snd (get ab_dom n) \<and>
             (\<forall>m<Suc (Suc 0).
                 m \<noteq> n \<longrightarrow> get xs m = fst (get ab_dom m)))"
    unfolding wedge_product_def ab_dom_length by auto
  then obtain n where n_def : "n < Suc (Suc 0) \<and>
             (get xs n \<in> snd (get ab_dom n) \<and>
             (\<forall>m<Suc (Suc 0).
                 m \<noteq> n \<longrightarrow> get xs m = fst (get ab_dom m)))"
    by auto

  have all_in_snd: "(\<forall>k<Suc (Suc 0). get xs k \<in> snd (get ab_dom k))"
    apply auto
  proof-
    fix k
    assume "k < Suc (Suc 0)"
    have "n = k \<or> n \<noteq> k" by simp
    then show "get xs k \<in> snd (get ab_dom k)"
    proof
      show "n = k \<Longrightarrow> get xs k \<in> snd (get ab_dom k)"
        using n_def by simp
      show "n \<noteq> k \<Longrightarrow> get xs k \<in> snd (get ab_dom k)"
        using n_def \<open>k < (Suc (Suc 0))\<close> apply simp
        using ab_dom_obj unfolding P.Obj'_def
        unfolding ab_dom_length by simp
    qed
  qed

  have seq : "S.seq a (projection1 (S.dom a) (S.dom b))"
     apply (rule_tac S.seqI')
    using Cat_with_products.proj1_in_hom 
          [OF S.ide_dom [OF arr_a] S.ide_dom [OF arr_b]]
      apply simp
    using S.in_homI [OF arr_a] by blast
  have seq_b : "S.seq b (projection2 (S.dom a) (S.dom b))"
     apply (rule_tac S.seqI')
    using Cat_with_products.proj2_in_hom 
          [OF S.ide_dom [OF arr_a] S.ide_dom [OF arr_b]]
      apply simp
    using S.in_homI [OF arr_b] by blast

  have "S.dom (P.pointed_set_comp a (projection1 (S.dom a) (S.dom b))) = Some (P.Id' (P.pointed_product ab_dom))"
    apply (subst S.dom_comp)
    using seq apply simp
    unfolding S.in_hom_dom [OF 
          Cat_with_products.proj1_in_hom 
          [OF S.ide_dom [OF arr_a] S.ide_dom [OF arr_b]]]
    unfolding product_def ab_dom_def by simp
  then have dom_eq : "(fst (snd (the (P.pointed_set_comp a (projection1 (S.dom a) (S.dom b)))))) =
                 P.pointed_product ab_dom"
    unfolding P.dom_char [OF seq]
    by (simp add: P.Id'_def)
  have "S.dom (P.pointed_set_comp b (projection2 (S.dom a) (S.dom b))) = Some (P.Id' (P.pointed_product ab_dom))"
    apply (subst S.dom_comp)
    using seq_b apply simp
    unfolding S.in_hom_dom [OF 
          Cat_with_products.proj2_in_hom 
          [OF S.ide_dom [OF arr_a] S.ide_dom [OF arr_b]]]
    unfolding product_def ab_dom_def by simp
  then have dom_eq_b : "(fst (snd (the (P.pointed_set_comp b (projection2 (S.dom a) (S.dom b)))))) =
                 P.pointed_product ab_dom"
    unfolding P.dom_char [OF seq_b]
    by (simp add: P.Id'_def)


  from x_in_wedge have x_in_prod : "x \<in> snd (P.pointed_product ab_dom)"
    using wedge_subseteq_product [OF ab_dom_obj] by auto
  then have x_in_dom : "x \<in> snd (fst (snd (the (P.pointed_set_comp a (projection1 (S.dom a) (S.dom b))))))"
    unfolding dom_eq.
  from x_in_prod have x_in_dom_b : "x \<in> snd (fst (snd (the (P.pointed_set_comp b (projection2 (S.dom a) (S.dom b))))))"
    unfolding dom_eq_b.

  define abx_cod where "abx_cod = [fst (the (P.pointed_set_comp a (projection1 (S.dom a) (S.dom b)))) x,
            fst (the (P.pointed_set_comp b (projection2 (S.dom a) (S.dom b)))) x]"

  show "fst (the (local.product_functor (a, b))) x
         \<in> snd (wedge_product [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))])"
    unfolding product_functor_def Cat_with_products.prod_functor_def
    apply (simp add: arr_a arr_b)
    unfolding product_UP_map_def apply simp
    unfolding P.prod_UP_map_def apply (simp add: x_in_dom)
    unfolding wedge_product_def apply simp
    unfolding reverse_equality [OF abx_cod_def]
    apply (rule_tac exI)
    apply safe
  proof-
    show "n < Suc (Suc 0)"
      using n_def by simp
    then have "n = 0 \<or> n = 1" by auto
    then show "get abx_cod n \<in> snd (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] n)"
    proof
      have "(S.cod a) = S.cod (P.pointed_set_comp a (projection1 (S.dom a) (S.dom b)))" 
        apply (subst S.cod_comp)
        using seq by simp_all
      then have cod_eq_a : "fst (snd (the (S.cod a))) =
            snd (snd (the (P.pointed_set_comp a (projection1 (S.dom a) (S.dom b)))))"
        apply simp
        apply (subst P.cod_char [OF seq])
        by (simp add: P.Id'_def)
      have "(S.cod b) = S.cod (P.pointed_set_comp b (projection2 (S.dom a) (S.dom b)))" 
        apply (subst S.cod_comp)
        using seq_b by simp_all
      then have cod_eq_b : "fst (snd (the (S.cod b))) =
            snd (snd (the (P.pointed_set_comp b (projection2 (S.dom a) (S.dom b)))))"
        apply simp
        apply (subst P.cod_char [OF seq_b])
        by (simp add: P.Id'_def)

      show "n = 0 \<Longrightarrow> get abx_cod n \<in> snd (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] n)"
        unfolding abx_cod_def apply simp
        unfolding cod_eq_a
        apply (rule_tac P.arr_x_in_dom [OF seq])
        using x_in_dom.
      show "n = 1 \<Longrightarrow> get abx_cod n \<in> snd (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] n)"
        unfolding abx_cod_def apply simp
        unfolding cod_eq_b
        apply (rule_tac P.arr_x_in_dom [OF seq_b])
        using x_in_dom_b.
    qed
    fix m
    assume "m < Suc (Suc 0)"
    assume "m \<noteq> n"
    then have m_eq: "get xs m = fst (get ab_dom m)"
      using n_def \<open>m < Suc (Suc 0)\<close> by blast

    from \<open>m < Suc (Suc 0)\<close>
    have "m = 0 \<or> m = 1" by auto
    then show "get abx_cod m = fst (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] m)"
    proof
      assume "m = 0"
      then have eq1: "fst (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] m) = 
                 fst (the a) (get xs 0)"
        apply simp
        unfolding P.cod_char [OF arr_a]
        using m_eq unfolding ab_dom_def
        unfolding P.dom_char [OF arr_a] 
        apply (simp add: P.Id'_def)
        using arr_a unfolding P.arr_char P.Arr'_def
        by simp

      have arr_p1: "S.arr (projection1 (S.dom a) (S.dom b))"
        using Cat_with_products.proj1_in_hom 
          [OF S.ide_dom [OF arr_a] S.ide_dom [OF arr_b]]
        by blast

      show "m = 0 \<Longrightarrow> get abx_cod m = fst (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] m)"
        unfolding eq1
        unfolding abx_cod_def apply simp
        apply (subst P.fst_comp_char [OF seq])
        using x_in_dom
        using S.dom_comp [OF seq]
        unfolding P.dom_char [OF seq]
        unfolding P.dom_char [OF arr_p1]
        unfolding P.Id'_def apply simp
        unfolding projection1_def apply simp
        unfolding P.prod_proj_def apply (simp add: xs_def ab_dom_def)
        using all_in_snd
        unfolding ab_dom_def by auto
    next
      assume "m = 1"
      then have eq1: "fst (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] m) = 
                 fst (the b) (get xs 1)"
        apply simp
        unfolding P.cod_char [OF arr_b]
        using m_eq unfolding ab_dom_def
        unfolding P.dom_char [OF arr_b] 
        apply (simp add: P.Id'_def)
        using arr_b unfolding P.arr_char P.Arr'_def
        by simp

      have arr_p2: "S.arr (projection2 (S.dom a) (S.dom b))"
        using Cat_with_products.proj2_in_hom 
          [OF S.ide_dom [OF arr_a] S.ide_dom [OF arr_b]]
        by blast

      show "m = 1 \<Longrightarrow> get abx_cod m = fst (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] m)"
        unfolding eq1
        unfolding abx_cod_def apply simp
        apply (subst P.fst_comp_char [OF seq_b])
        using x_in_dom_b
        using S.dom_comp [OF seq_b]
        unfolding P.dom_char [OF seq_b]
        unfolding P.dom_char [OF arr_p2]
        unfolding P.Id'_def apply simp
        unfolding projection2_def apply simp
        unfolding P.prod_proj_def apply (simp add: xs_def ab_dom_def)
        using all_in_snd
        unfolding ab_dom_def by auto
    qed
  qed
qed

        
        




interpretation Quot_fun: quotient_functor "(product_category.comp P.pointed_set_comp P.pointed_set_comp)"
       product_functor quotient_wedge_relation
  unfolding quotient_functor_def
  apply (simp add: product_functor)
  unfolding quotient_functor_axioms_def
  apply auto
proof-
  fix a :: "'a P.LC P.parr option" 
  fix b :: "'a P.LC P.parr option"

  assume "S.ide a" 
  assume "S.ide b"
  have obj_eq: "(P.Dom' (the (local.product_functor (a, b)))) = 
        (P.pointed_product [fst (snd (the (fst (a, b)))), fst (snd (the (snd (a, b))))])"
    unfolding product_functor_def 
    unfolding Cat_with_products.prod_functor_obj [OF \<open>S.ide a\<close> \<open>S.ide b\<close>]
    unfolding product_def
    by (simp add: P.Id'_def)
  have set_eq: "\<And>X. {(x, y). (x, y) \<in> X}  = X" by simp
  show "equiv (snd (fst (snd (the (local.product_functor (a, b))))))
            {(x, y). quotient_wedge_relation (a, b) x y}"
    unfolding quotient_wedge_relation_def
    unfolding P.cur_rel.simps
    unfolding obj_eq
    unfolding set_eq
    using P.subset_eq_rel_equiv.
next
  fix a :: "'a P.LC P.parr option"
  fix b :: "'a P.LC P.parr option"
  fix x y
  assume arr_a : "S.arr a"
  assume arr_b : "S.arr b"
  assume x_in_dom: "x \<in> snd (P.Dom' (the (product_functor (a, b))))"
  assume y_in_dom: "y \<in> snd (P.Dom' (the (product_functor (a, b))))"

  have arr_pab: "S.arr (local.product_functor (a, b))"
    apply (rule_tac functor.preserves_arr [OF product_functor])
    by (simp add: arr_a arr_b)

  have "S.cod (product_functor (a, b)) = product (S.cod a) (S.cod b)"
    apply (subst functor.preserves_cod [OF product_functor])
     apply (simp add: arr_a arr_b)
    apply (simp add: arr_a arr_b)
    unfolding product_functor_def
    using Cat_with_products.prod_functor_obj [OF S.ide_cod [OF arr_a] S.ide_cod [OF arr_b]].
  then have cod_eq : "(P.Cod' (the (product_functor (a, b)))) = (P.pointed_product
              [P.Dom' (the (S.cod a)), P.Dom' (the (S.cod b))])"
    unfolding product_def
    unfolding P.cod_char [OF arr_pab]
    by (simp add: P.Id'_def)

  have py_in_cod : "fst (the (product_functor (a, b))) y \<in> snd (P.Cod' (the (product_functor (a, b))))"
    apply (rule_tac P.arr_x_in_dom)
     apply (rule_tac functor.preserves_arr [OF product_functor])
     apply (simp add: arr_a arr_b)
    using y_in_dom.
  then have py_in_prod : "fst (the (product_functor (a, b))) y \<in> (snd (P.pointed_product
              [P.Dom' (the (S.cod a)), P.Dom' (the (S.cod b))]))"
    unfolding cod_eq.

  assume "quotient_wedge_relation (S.dom a, S.dom b) x y"
  then have R: "x \<in> snd (P.pointed_product [P.Dom' (the (S.dom a)), P.Dom' (the (S.dom b))]) \<and>
             y \<in> snd (P.pointed_product [P.Dom' (the (S.dom a)), P.Dom' (the (S.dom b))]) \<and>
    (x = y \<or>
     x \<in> snd (wedge_product [P.Dom' (the (S.dom a)), P.Dom' (the (S.dom b))]) \<and>
     y \<in> snd (wedge_product [P.Dom' (the (S.dom a)), P.Dom' (the (S.dom b))]))"
    unfolding quotient_wedge_relation_def
    by simp
  then have or: "(x = y \<or>
     x \<in> snd (wedge_product [P.Dom' (the (S.dom a)), P.Dom' (the (S.dom b))]) \<and>
     y \<in> snd (wedge_product [P.Dom' (the (S.dom a)), P.Dom' (the (S.dom b))]))" by simp

  from or show "quotient_wedge_relation (S.cod a, S.cod b) (fst (the (local.product_functor (a, b))) x)
        (fst (the (local.product_functor (a, b))) y)"
  proof
    show "x = y \<Longrightarrow>
    quotient_wedge_relation (S.cod a, S.cod b) (fst (the (local.product_functor (a, b))) x)
     (fst (the (local.product_functor (a, b))) y)"
      unfolding quotient_wedge_relation_def
      using py_in_prod
      by simp
    have R_restrict: "\<And>x. x \<in> snd (wedge_product [fst (snd (the (S.dom a))), fst (snd (the (S.dom b)))]) \<Longrightarrow>
              fst (the (local.product_functor (a, b))) x
     \<in> snd (wedge_product [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))])"
      using prod_functor_wedge_restrict [OF arr_a arr_b].

    define pointed_product_nosimp :: "('a P.LC \<times> 'a P.LC set) list \<Rightarrow> 'a P.LC \<times> 'a P.LC set"
      where "pointed_product_nosimp = P.pointed_product"
    have subseteq : "snd (wedge_product [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))])
                 \<subseteq> snd (pointed_product_nosimp [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))])"
      unfolding pointed_product_nosimp_def
      apply (rule_tac wedge_subseteq_product)
      apply auto
    proof-
      fix k
      assume "k < Suc (Suc 0)"
      then have "k = 0 \<or> k = 1" by auto
      then show "P.Obj' (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] k)"
      proof
        show "k = 0 \<Longrightarrow> P.Obj' (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] k)"
          apply simp
          apply (rule_tac classical_category.Obj_Dom [OF P.ccpf])
          using S.ideD(1) [OF S.ide_cod [OF arr_a]] unfolding P.arr_char by simp
        show "k = 1 \<Longrightarrow> P.Obj' (get [fst (snd (the (S.cod a))), fst (snd (the (S.cod b)))] k)"
          apply simp
          apply (rule_tac classical_category.Obj_Dom [OF P.ccpf])
          using S.ideD(1) [OF S.ide_cod [OF arr_b]] unfolding P.arr_char by simp
      qed
    qed

    show "x \<in> snd (wedge_product [fst (snd (the (S.dom a))), fst (snd (the (S.dom b)))]) \<and>
    y \<in> snd (wedge_product [fst (snd (the (S.dom a))), fst (snd (the (S.dom b)))]) \<Longrightarrow>
    quotient_wedge_relation (S.cod a, S.cod b) (fst (the (local.product_functor (a, b))) x)
     (fst (the (local.product_functor (a, b))) y)"
      unfolding quotient_wedge_relation_def
      unfolding reverse_equality [OF pointed_product_nosimp_def]
      using R_restrict subseteq by auto
  qed
qed

definition smash_functor where
  "smash_functor = Quot_fun.quotient_functor"


lemma smash_is_functor: "functor
       (product_category.comp P.pointed_set_comp P.pointed_set_comp)
       P.pointed_set_comp
       smash_functor"
  unfolding smash_functor_def
  using Quot_fun.is_functor.


end


definition smash_functor where
  "smash_functor = pointed_set_product_functor.smash_functor"



lemma smash_functor: "functor
       (product_category.comp P.pointed_set_comp P.pointed_set_comp)
       P.pointed_set_comp
       smash_functor"
  unfolding smash_functor_def
  using pointed_set_product_functor.smash_is_functor.












end
