theory ColimitFunctoriality
  imports Main
          PointedSet
         "Category3.FreeCategory"
begin

locale functor_to_cat =
  C : category C
  for C :: "'c comp"
  and F_ob :: "'c \<Rightarrow> ('d comp)"
  and F_arr :: "'c \<Rightarrow> ('d \<Rightarrow> 'd)" +
assumes Fcat : "\<And>c. C.ide c \<Longrightarrow> category (F_ob c)"
    and Ffun : "\<And>c. C.arr c \<Longrightarrow> functor (F_ob (C.dom c))
                                        (F_ob (C.cod c))
                                        (F_arr c)" 
    and Ffun_id : "\<And>c. C.ide c \<Longrightarrow> F_arr c = identity_functor.map (F_ob c)"
    and Ffun_comp : "\<And>g f. C.seq g f \<Longrightarrow> (F_arr (C g f)) =
                                         (F_arr g) \<circ> (F_arr f)"
begin
end


lemma (in vertical_composite) precompose_horizontally : 
  assumes "functor D A I"
  shows "vertical_composite D B (F \<circ> I) (G \<circ> I) (H \<circ> I) (\<sigma> \<circ> I) (\<tau> \<circ> I)"
  unfolding vertical_composite_def
proof-
  have Inat : "natural_transformation D A I I I"
    using functor_is_transformation [OF \<open>functor D A I\<close>].
  have I\<sigma>nat: "natural_transformation D B (F \<circ> I) (G \<circ> I) (\<sigma> \<circ> I)"
    apply (rule_tac horizontal_composite.is_natural_transformation)
    unfolding horizontal_composite_def
    using \<sigma>.natural_transformation_axioms Inat
    unfolding natural_transformation_def
    by auto
  have I\<tau>nat: "natural_transformation D B (G \<circ> I) (H \<circ> I) (\<tau> \<circ> I)"
    apply (rule_tac horizontal_composite.is_natural_transformation)
    unfolding horizontal_composite_def
    using \<tau>.natural_transformation_axioms Inat
    unfolding natural_transformation_def
    by auto
  show "(category D \<and> category (\<cdot>\<^sub>B) \<and> functor D (\<cdot>\<^sub>B) (F \<circ> I)) \<and>
    (functor D (\<cdot>\<^sub>B) (G \<circ> I) \<and> functor D (\<cdot>\<^sub>B) (H \<circ> I)) \<and>
    natural_transformation D (\<cdot>\<^sub>B) (F \<circ> I) (G \<circ> I) (\<sigma> \<circ> I) \<and>
    natural_transformation D (\<cdot>\<^sub>B) (G \<circ> I) (H \<circ> I) (\<tau> \<circ> I)"
    using I\<sigma>nat I\<tau>nat
    unfolding natural_transformation_def
    by auto
qed

lemma (in vertical_composite) postcompose_horizontally : 
  assumes "functor B C I"
  shows "vertical_composite A C (I \<circ> F) (I \<circ> G) (I \<circ> H) (I \<circ> \<sigma>) (I \<circ> \<tau>)"
  unfolding vertical_composite_def
proof-
  have Inat : "natural_transformation B C I I I"
    using functor_is_transformation [OF \<open>functor B C I\<close>].
  have I\<sigma>nat: "natural_transformation (\<cdot>\<^sub>A) C (I \<circ> F) (I \<circ> G) (I \<circ> \<sigma>)"
    apply (rule_tac horizontal_composite.is_natural_transformation)
    unfolding horizontal_composite_def
    using \<sigma>.natural_transformation_axioms Inat
    unfolding natural_transformation_def
    by auto
  have I\<tau>nat: "natural_transformation (\<cdot>\<^sub>A) C (I \<circ> G) (I \<circ> H) (I \<circ> \<tau>)"
    apply (rule_tac horizontal_composite.is_natural_transformation)
    unfolding horizontal_composite_def
    using \<tau>.natural_transformation_axioms Inat
    unfolding natural_transformation_def
    by auto
  show "(category (\<cdot>\<^sub>A) \<and> category C \<and> functor (\<cdot>\<^sub>A) C (I \<circ> F)) \<and>
    (functor (\<cdot>\<^sub>A) C (I \<circ> G) \<and> functor (\<cdot>\<^sub>A) C (I \<circ> H)) \<and>
    natural_transformation (\<cdot>\<^sub>A) C (I \<circ> F) (I \<circ> G) (I \<circ> \<sigma>) \<and>
    natural_transformation (\<cdot>\<^sub>A) C (I \<circ> G) (I \<circ> H) (I \<circ> \<tau>)"
    using I\<sigma>nat I\<tau>nat
    unfolding natural_transformation_def
    by auto
qed

locale functor_to_cat_overX =
  F : functor_to_cat C F_ob F_arr + 
  S : category S
  for C :: "'c comp"
  and S :: "'s comp"
  and F_ob :: "'c \<Rightarrow> ('d comp)"
  and F_arr :: "'c \<Rightarrow> ('d \<Rightarrow> 'd)"
  and \<tau> :: "'c \<Rightarrow> ('d \<Rightarrow> 's)" +
assumes \<tau>fun : "\<And>c. F.C.ide c \<Longrightarrow> functor (F_ob c) S (\<tau> c)"
    and \<tau>nat : "\<And>c. F.C.arr c \<Longrightarrow>
          natural_transformation (F_ob (F.C.dom c)) S 
            (\<tau> (F.C.dom c)) (\<tau> (F.C.cod c) \<circ> (F_arr c)) (\<tau> c)"
    and \<tau>comp : "\<And>g f. F.C.seq g f \<Longrightarrow>
                 \<tau> (C g f) = vertical_composite.map (F_ob (F.C.dom f)) S
             (\<tau> f)  (\<tau> g \<circ> F_arr f)"
begin


lemma conj_comm: "A \<and> B \<Longrightarrow> B \<and> A" 
  by simp

lemma extend_by_functor : 
  assumes "functor S T G"
  shows "functor_to_cat_overX C T F_ob F_arr (\<lambda>c. G \<circ> (\<tau> c))"
  unfolding functor_to_cat_overX_def
  apply safe
    apply (rule_tac F.functor_to_cat_axioms)
  using \<open>functor S T G\<close>
  unfolding functor_def apply simp
  unfolding functor_to_cat_overX_axioms_def
  apply safe
proof-
  fix c
  show "F.C.ide c \<Longrightarrow> functor (F_ob c) T (G \<circ> \<tau> c)"
    apply (rule_tac functor_comp)
    using \<tau>fun apply blast
    using \<open>functor S T G\<close> by simp
  assume "F.C.arr c"
  show "natural_transformation (F_ob (F.C.dom c)) T (G \<circ> \<tau> (F.C.dom c))
          (G \<circ> \<tau> (F.C.cod c) \<circ> F_arr c) (G \<circ> \<tau> c)"
    apply (subst comp_assoc)
    apply (rule_tac horizontal_composite.is_natural_transformation)
    unfolding horizontal_composite_def
    using \<open>functor S T G\<close> functor_def apply auto
  proof-
    show "category (F_ob (F.C.dom c))"
      using F.Fcat [OF F.C.ide_dom [OF \<open>F.C.arr c\<close>]].
    show "functor (F_ob (F.C.dom c)) S (\<tau> (F.C.dom c))"
      using \<tau>fun [OF F.C.ide_dom [OF \<open>F.C.arr c\<close>]].
    show "functor (F_ob (F.C.dom c)) S (\<tau> (F.C.cod c) \<circ> F_arr c)"
      apply (rule_tac functor_comp)
      using F.Ffun [OF \<open>F.C.arr c\<close>] apply simp
      using \<tau>fun [OF F.C.ide_cod [OF \<open>F.C.arr c\<close>]].
    show "natural_transformation (F_ob (F.C.dom c)) S (\<tau> (F.C.dom c))
     (\<tau> (F.C.cod c) \<circ> F_arr c) (\<tau> c)"
      using \<tau>nat [OF \<open>F.C.arr c\<close>].
  qed
next
  fix g f
  assume arr_gf : "F.C.seq g f"
  from arr_gf have arr_f : "F.C.arr f" by blast
  from arr_gf have arr_g : "F.C.arr g" by blast
  from arr_gf have seq : "F.C.dom g = F.C.cod f" by blast

  have fnat : "natural_transformation (F_ob (F.C.dom f)) S (\<tau> (F.C.dom g) \<circ> F_arr f)
     (\<tau> (F.C.cod g) \<circ> F_arr g \<circ> F_arr f) (\<tau> g \<circ> F_arr f)"
    apply (rule_tac horizontal_composite.is_natural_transformation)
    unfolding horizontal_composite_def
    using functor_is_transformation [OF F.Ffun [OF arr_f]]
          \<tau>nat [OF arr_g]
    unfolding natural_transformation_def
    apply (rule_tac conj_comm)
    using seq by auto

  have vert_comp1 : "vertical_composite (F_ob (F.C.dom f)) S 
                     (\<tau> (F.C.dom f)) 
                     (\<tau> (F.C.dom g) \<circ> F_arr f)
                     (\<tau> (F.C.cod g) \<circ> F_arr g \<circ> F_arr f)
                     (\<tau> f) (\<tau> g \<circ> F_arr f)"
    unfolding vertical_composite_def
    using \<tau>nat [OF arr_f]
          fnat
    unfolding natural_transformation_def
    using seq by auto


  show "G \<circ> \<tau> (C g f) =
           vertical_composite.map (F_ob (F.C.dom f)) T (G \<circ> \<tau> f)
            (G \<circ> \<tau> g \<circ> F_arr f)"
    apply (subst \<tau>comp [OF arr_gf])
    unfolding vertical_composite.map_def [OF vert_comp1]
    apply (subst comp_assoc)
    unfolding vertical_composite.map_def 
          [OF vertical_composite.postcompose_horizontally 
          [OF vert_comp1 \<open>functor S T G\<close>]]
  proof
    fix fa
    show "(G \<circ> (\<lambda>fa. if partial_magma.arr (F_ob (F.C.dom f)) fa
                     then S ((\<tau> g \<circ> F_arr f)
                              (partial_magma.cod (F_ob (F.C.dom f)) fa))
                           (\<tau> f fa)
                     else S.null))
           fa =
          (if partial_magma.arr (F_ob (F.C.dom f)) fa
           then T ((G \<circ> (\<tau> g \<circ> F_arr f))
                    (partial_magma.cod (F_ob (F.C.dom f)) fa))
                 ((G \<circ> \<tau> f) fa)
           else partial_magma.null T)"
      apply auto
    proof-
      show "\<not> partial_magma.arr (F_ob (F.C.dom f)) fa \<Longrightarrow>
    G S.null = partial_magma.null T" 
        apply (subst functor.is_extensional [OF \<open>functor S T G\<close>])
        using S.not_arr_null apply blast
        by simp
      assume arr_fa : "partial_magma.arr (F_ob (F.C.dom f)) fa"

      have arr_cod : "partial_magma.arr (F_ob (F.C.dom f))
                       (partial_magma.cod (F_ob (F.C.dom f)) fa)"
        using category.ide_cod [OF F.Fcat [OF F.C.ide_dom [OF arr_f]] arr_fa]
        unfolding category.ide_char [OF F.Fcat [OF F.C.ide_dom [OF arr_f]]]
        by simp


      show "G (S (\<tau> g (F_arr f (partial_magma.cod (F_ob (F.C.dom f)) fa))) (\<tau> f fa)) =
    T (G (\<tau> g (F_arr f (partial_magma.cod (F_ob (F.C.dom f)) fa))))
     (G (\<tau> f fa))"
        apply (rule_tac functor.preserves_comp [OF \<open>functor S T G\<close>])
        apply (rule_tac S.seqI)
          apply (subst natural_transformation.preserves_reflects_arr 
                 [OF \<tau>nat [OF arr_f]])
        using arr_fa apply simp
         apply (subst natural_transformation.preserves_reflects_arr 
                 [OF \<tau>nat [OF arr_g]])
         apply (subst seq)
         apply (rule_tac functor.preserves_arr [OF F.Ffun [OF arr_f]])
        using category.ide_cod [OF F.Fcat [OF F.C.ide_dom [OF arr_f]] arr_fa]
        unfolding category.ide_char [OF F.Fcat [OF F.C.ide_dom [OF arr_f]]]
         apply simp
      proof-
        define a where "a = partial_magma.dom (F_ob (F.C.dom f)) fa"
        define b where "b = partial_magma.cod (F_ob (F.C.dom f)) fa"

        have in_hom1: "S.in_hom (\<tau> f fa) (\<tau> (F.C.dom f) a) ((\<tau> (F.C.cod f) \<circ> F_arr f) b)"
          apply (rule_tac natural_transformation.preserves_hom 
                 [OF \<tau>nat [OF arr_f]])
          unfolding a_def b_def
          using arr_fa
          by (simp add: F.Fcat arr_f category.in_homI)

        define c where "c = (F_arr f (partial_magma.cod (F_ob (F.C.dom f)) fa))"

        have in_hom2 : "S.in_hom (\<tau> g c) (\<tau> (F.C.dom g) c) ((\<tau> (F.C.cod g) \<circ> F_arr g) c)"
          apply (rule_tac natural_transformation.preserves_hom [OF \<tau>nat [OF arr_g]])
          apply (rule_tac category.in_homI 
                [OF F.Fcat [OF F.C.ide_dom [OF arr_g]]])
          unfolding c_def seq
            apply (rule_tac functor.preserves_arr [OF F.Ffun [OF arr_f]])
          using arr_cod apply simp
           apply (subst functor.preserves_dom [OF F.Ffun [OF arr_f]])
          using arr_cod apply simp
           apply (subst category.ideD(2) [OF F.Fcat [OF F.C.ide_dom [OF arr_f]]])
          using category.ide_cod [OF F.Fcat [OF F.C.ide_dom [OF arr_f]]] arr_fa apply simp
           apply simp
           apply (subst functor.preserves_cod [OF F.Ffun [OF arr_f]])
          using arr_cod apply simp
          apply (subst category.ideD(3) [OF F.Fcat [OF F.C.ide_dom [OF arr_f]]])
          using category.ide_cod [OF F.Fcat [OF F.C.ide_dom [OF arr_f]]] arr_fa apply simp
          by simp

        show "S.dom (\<tau> g (F_arr f (partial_magma.cod (F_ob (F.C.dom f)) fa))) =
    S.cod (\<tau> f fa)"
          apply (rule_tac S.in_homE [OF in_hom1])
          apply (rule_tac S.in_homE [OF in_hom2])
          unfolding c_def b_def
          by (simp add: seq)
      qed
    qed
  qed
qed

end


definition cocone where
  "cocone C D F x \<tau> = natural_transformation C D F (constant_functor.map C D x) \<tau>"

locale colimit =
  C: category C +
  D: category D +
  F: "functor" C D F +
  \<tau>: natural_transformation C D F "(constant_functor.map C D d)" \<tau>
  for C :: "'c comp" 
  and D :: "'d comp"
  and F :: "'c \<Rightarrow> 'd"
  and \<tau> :: "'c \<Rightarrow> 'd" 
  and d :: "'d"
  and UP_map :: "'d \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> 'd" +
assumes d_obj : "D.ide d"
  and cocone : "cocone C D F d \<tau>"
  and UP_existence : "\<And> \<sigma> x. cocone C D F x \<sigma> \<Longrightarrow> D.ide x \<Longrightarrow>
                    D.in_hom (UP_map x \<sigma>) d x \<and>
              (\<forall>c. C.ide c \<longrightarrow> \<sigma> c = D (UP_map x \<sigma>) (\<tau> c))"
  and UP_uniqueness : "\<And>f \<sigma> x. cocone C D F x \<sigma> \<Longrightarrow> D.ide x \<Longrightarrow>
                  ( D.in_hom f d x \<and>
              (\<forall>c. C.ide c \<longrightarrow> \<sigma> c = D f (\<tau> c))) \<Longrightarrow>
                   f = (UP_map x \<sigma>)" 
begin

lemma cocone_id : "d = (UP_map d \<tau>)"
  apply (rule_tac UP_uniqueness)
   apply (rule_tac cocone)
  apply safe
  using D.ide_in_hom d_obj apply blast
proof-
  show "D.in_hom d d d"
    using \<open>D.ide d\<close>
  by (simp add: D.ide_in_hom)
  fix c
  assume "C.ide c"
  have d_in_hom: "D.in_hom (UP_map d \<tau>) d d"
    using UP_existence [OF cocone \<open>D.ide d\<close>] by simp
  have eq: "\<tau> c = D (UP_map d \<tau>) (\<tau> c)"
    using UP_existence [OF cocone \<open>D.ide d\<close>] \<open>C.ide c\<close> by simp
  show "\<tau> c = D d (\<tau> c)"
    by (metis D.comp_assoc D.comp_cod_arr D.in_homE d_in_hom eq)
qed

end




locale colimit_functoriality =
  F : functor_to_cat_overX C S F_ob F_arr \<tau>
  for C :: "'c comp"
  and S :: "'s comp"
  and F_ob :: "'c \<Rightarrow> ('d comp)"
  and F_arr :: "'c \<Rightarrow> ('d \<Rightarrow> 'd)"
  and \<tau> :: "'c \<Rightarrow> ('d \<Rightarrow> 's)"
  and colim :: "'c \<Rightarrow> 's"
  and cocone_map :: "'c \<Rightarrow> ('d \<Rightarrow> 's)"
  and colim_UP_map :: "'c \<Rightarrow> 's \<Rightarrow> ('d \<Rightarrow> 's) \<Rightarrow> 's" +
assumes
  colimit_existence : "\<And>c. F.F.C.ide c \<Longrightarrow>
                       colimit (F_ob c) S (\<tau> c) 
                       (cocone_map c) (colim c) (colim_UP_map c)"
begin

definition colim_functor :: "'c \<Rightarrow> 's" where
  "colim_functor  = MkFunctor C S
                    (\<lambda>f. colim_UP_map (F.F.C.dom f) (colim (F.F.C.cod f))
                         (vertical_composite.map (F_ob (F.F.C.dom f)) S 
                            (\<tau> f) ((cocone_map (F.F.C.cod f)) \<circ> F_arr f)))"


lemma colim_UP_map_in_hom :
  assumes "F.F.C.ide c" 
  and "cocone (F_ob c) S (\<tau> c) x \<sigma>" and "F.S.ide x"
shows "F.S.in_hom (colim_UP_map c x \<sigma>) (colim c) x"
proof-
  have "colimit_axioms (F_ob c) S (\<tau> c) (cocone_map c) (colim c)
   (colim_UP_map c)" 
    using colimit_existence [OF \<open>F.F.C.ide c\<close>]
    unfolding colimit_def by simp
  then have "(\<forall>\<sigma> x. cocone (F_ob c) S (\<tau> c) x \<sigma> \<longrightarrow> F.S.ide x \<longrightarrow>
         F.S.in_hom (colim_UP_map c x \<sigma>) (colim c) x \<and>
         (\<forall>ca. partial_magma.ide (F_ob c) ca \<longrightarrow>
               \<sigma> ca = S (colim_UP_map c x \<sigma>) (cocone_map c ca)))"
    unfolding colimit_axioms_def by simp
  then show "F.S.in_hom (colim_UP_map c x \<sigma>) (colim c) x"
    by (simp add: \<open>cocone (F_ob c) S (\<tau> c) x \<sigma>\<close> \<open>F.S.ide x\<close>)
qed
lemma colim_UP_map_arr :
  assumes "F.F.C.ide c" 
  and "cocone (F_ob c) S (\<tau> c) x \<sigma>" \<open>F.S.ide x\<close>
shows "F.S.arr (colim_UP_map c x \<sigma>)"
  using colim_UP_map_in_hom [OF \<open>F.F.C.ide c\<close> 
        \<open>cocone (F_ob c) S (\<tau> c) x \<sigma>\<close> \<open>F.S.ide x\<close>]
  by auto


lemma vert_comp: assumes arr_f : "F.F.C.arr f"
  shows "vertical_composite (F_ob (F.F.C.dom f)) S (\<tau> (F.F.C.dom f)) 
     (\<tau> (F.F.C.cod f) \<circ> F_arr f)
     (constant_functor.map (F_ob (F.F.C.dom f)) S (colim (F.F.C.cod f))) (\<tau> f)
     (cocone_map (F.F.C.cod f) \<circ> F_arr f)"
proof-
  have ide_dom : "F.F.C.ide (F.F.C.dom f)"
    using F.F.C.ide_dom [OF arr_f].
  have ide_cod : "F.F.C.ide (F.F.C.cod f)"
    using F.F.C.ide_cod [OF arr_f].

  have ide_colim : "F.S.ide (colim (F.F.C.cod f))"
    using colimit.d_obj [OF colimit_existence [OF ide_cod]].

  have const_functor_dom : "constant_functor (F_ob (F.F.C.dom f)) S (colim (F.F.C.cod f))"
    unfolding constant_functor_def
    apply safe
      apply (rule_tac F.F.Fcat [OF ide_dom])
     apply (rule_tac F.S.category_axioms)
    unfolding constant_functor_axioms_def
    using ide_colim by simp
  have const_functor_cod : "constant_functor (F_ob (F.F.C.cod f)) S (colim (F.F.C.cod f))"
    unfolding constant_functor_def
    apply safe
      apply (rule_tac F.F.Fcat [OF ide_cod])
     apply (rule_tac F.S.category_axioms)
    unfolding constant_functor_axioms_def
    using ide_colim by simp

  have const_eq: "constant_functor.map (F_ob (F.F.C.dom f)) S (colim (F.F.C.cod f)) =
        constant_functor.map (F_ob (F.F.C.cod f)) S (colim (F.F.C.cod f)) \<circ> F_arr f"
  proof
    fix x
    have not_arr_null: "\<not> partial_magma.arr (F_ob (F.F.C.cod f))
     (partial_magma.null (F_ob (F.F.C.cod f)))"
      using F.F.Fcat [OF ide_cod]
      using category_def partial_magma.not_arr_null by blast

    show "constant_functor.map (F_ob (F.F.C.dom f)) S (colim (F.F.C.cod f)) x =
         (constant_functor.map (F_ob (F.F.C.cod f)) S (colim (F.F.C.cod f)) \<circ>
          F_arr f)
          x"
      unfolding constant_functor.map_def [OF const_functor_dom]
                constant_functor.map_def [OF const_functor_cod]
      by (simp add: functor.preserves_arr [OF F.F.Ffun [OF arr_f]]
                       functor.is_extensional [OF F.F.Ffun [OF arr_f]]
                       not_arr_null)
  qed
  have hori_comp : "horizontal_composite (F_ob (F.F.C.dom f)) (F_ob (F.F.C.cod f)) S (F_arr f) (F_arr f)
     (\<tau> (F.F.C.cod f))
     (constant_functor.map (F_ob (F.F.C.cod f)) S (colim (F.F.C.cod f)))
     (F_arr f) (cocone_map (F.F.C.cod f))"
    unfolding horizontal_composite_def
    using colimit.cocone[OF colimit_existence [OF ide_cod]]
    unfolding cocone_def
    using functor_is_transformation [OF F.F.Ffun [OF arr_f]]
    unfolding natural_transformation_def
    by auto
  show "vertical_composite (F_ob (F.F.C.dom f)) S (\<tau> (F.F.C.dom f)) 
     (\<tau> (F.F.C.cod f) \<circ> F_arr f)
     (constant_functor.map (F_ob (F.F.C.dom f)) S (colim (F.F.C.cod f))) (\<tau> f)
     (cocone_map (F.F.C.cod f) \<circ> F_arr f)" 
    unfolding vertical_composite_def
    using horizontal_composite.is_natural_transformation [OF hori_comp]
          F.\<tau>nat [OF arr_f]
    unfolding natural_transformation_def
    using const_eq by auto
qed

lemma colim_functor_ide : assumes ide_f : "F.F.C.ide f"
  shows "F.S.ide (colim_functor f)"
proof-

  have EQ1: "(vertical_composite.map (F_ob f) S (\<tau> f) (cocone_map f \<circ> F_arr f)) =
        cocone_map f" 
    apply (subst F.F.Ffun_id [OF ide_f])
    apply (subst hcomp_ide_dom)
    using colimit.cocone [OF colimit_existence [OF ide_f]]
    unfolding cocone_def apply simp
    apply (rule_tac vcomp_ide_dom)
    using colimit.cocone [OF colimit_existence [OF ide_f]]
    unfolding cocone_def.

  have EQ2: "colim f = colim_UP_map f (colim f) (cocone_map f)"
    using colimit.cocone_id [OF colimit_existence [OF ide_f]].

  show "F.S.ide (colim_functor f)"
    unfolding colim_functor_def apply (simp add: ide_f)
    apply (subst EQ1)
    apply (subst reverse_equality [OF EQ2])
    using colimit.d_obj [OF colimit_existence [OF ide_f]].
qed

lemma colim_functor_dom : assumes arr_f: "F.F.C.arr f"
  shows "F.S.dom (colim_functor f) = colim (F.F.C.dom f)"
  unfolding colim_functor_def apply (simp add: arr_f)
  using colim_UP_map_in_hom [OF F.F.C.ide_dom [OF arr_f]
      colimit.cocone [OF colimit_existence [OF F.F.C.ide_dom [OF arr_f]]]]
  by (meson F.F.C.ide_cod F.F.C.ide_dom F.S.in_homE assms 
             cocone_def colim_UP_map_in_hom colimit.d_obj 
                              colimit_existence vert_comp 
            vertical_composite.is_natural_transformation)

lemma colim_functor_cod : assumes arr_f: "F.F.C.arr f"
  shows "F.S.cod (colim_functor f) = colim (F.F.C.cod f)"
  unfolding colim_functor_def apply (simp add: arr_f)
  using colim_UP_map_in_hom [OF F.F.C.ide_cod [OF arr_f]
      colimit.cocone [OF colimit_existence [OF F.F.C.ide_cod [OF arr_f]]]]
  by (meson F.F.C.ide_cod F.F.C.ide_dom F.S.in_homE assms 
             cocone_def colim_UP_map_in_hom colimit.d_obj 
                              colimit_existence vert_comp 
            vertical_composite.is_natural_transformation)


lemma colim_ide :
  assumes "F.F.C.ide c"
  shows "F.S.ide (colim c)"
  using colimit_existence [OF \<open>F.F.C.ide c\<close>]
  unfolding colimit_def
  unfolding colimit_axioms_def
  by simp


lemma is_functor: "functor C S colim_functor"
  unfolding functor_def
  apply (simp add: F.F.C.category_axioms F.S.category_axioms)
  unfolding functor_axioms_def
  apply safe
proof-
  fix f
  show "\<not> F.F.C.arr f \<Longrightarrow> colim_functor f = F.S.null"
    unfolding colim_functor_def by simp
  assume arr_f : "F.F.C.arr f"
  have ide_dom : "F.F.C.ide (F.F.C.dom f)"
    using F.F.C.ide_dom [OF arr_f].
  have ide_cod : "F.F.C.ide (F.F.C.cod f)"
    using F.F.C.ide_cod [OF arr_f].

  show "F.S.arr (colim_functor f)"
    unfolding colim_functor_def apply (simp add: arr_f)
    apply (rule_tac colim_UP_map_arr)
    using F.F.C.ide_dom [OF arr_f] apply simp
    unfolding cocone_def
    apply (rule_tac vertical_composite.is_natural_transformation)
    using vert_comp [OF arr_f] apply simp
    using colim_ide [OF F.F.C.ide_cod [OF arr_f]].


  have dom_eq: "F.S.dom (colim_functor f) = F.S.dom (colim_functor (F.F.C.dom f))"
    apply (subst colim_functor_dom [OF arr_f])
    apply (subst colim_functor_dom)
    using arr_f apply simp
    unfolding colim_functor_def by (simp add: arr_f)

  show "F.S.dom (colim_functor f) = colim_functor (F.F.C.dom f)"
    apply (subst dom_eq)
    using F.S.ideD(2) [OF colim_functor_ide [OF ide_dom]].

  have cod_eq: "F.S.cod (colim_functor f) = F.S.cod (colim_functor (F.F.C.cod f))"
    apply (subst colim_functor_cod [OF arr_f])
    apply (subst colim_functor_cod)
    using arr_f apply simp
    unfolding colim_functor_def by (simp add: arr_f)

  show "F.S.cod (colim_functor f) = colim_functor (F.F.C.cod f)"
    apply (subst cod_eq)
    using F.S.ideD(3) [OF colim_functor_ide [OF ide_cod]].
next
  fix g f
  assume arr_gf: "F.F.C.seq g f"
  then have gf_prop: "F.F.C.arr f \<and> F.F.C.arr g \<and> F.F.C.dom g = F.F.C.cod f"
    using F.F.C.seqE [OF arr_gf] by auto 
  from gf_prop have arr_f : "F.F.C.arr f" by simp
  from gf_prop have arr_g : "F.F.C.arr g" by simp
  from gf_prop have seq : "F.F.C.dom g = F.F.C.cod f" by simp



  have in_hom_f: "F.S.in_hom (colim_UP_map (F.F.C.dom f) (colim (F.F.C.cod f))
       (vertical_composite.map (F_ob (F.F.C.dom f)) S (\<tau> f)
         (cocone_map (F.F.C.cod f) \<circ> F_arr f)))
     (colim (F.F.C.dom f)) (colim (F.F.C.cod f))"
    apply (rule_tac conjunct1 [OF colimit.UP_existence [OF colimit_existence]])
     apply (rule_tac F.F.C.ide_dom [OF arr_f])
    unfolding cocone_def
    apply (rule_tac vertical_composite.is_natural_transformation)
    using vert_comp [OF arr_f] apply simp
    using colim_ide [OF F.F.C.ide_cod [OF arr_f]].



  have in_hom_g: "F.S.in_hom
     (colim_UP_map (F.F.C.cod f) (colim (F.F.C.cod g))
       (vertical_composite.map (F_ob (F.F.C.cod f)) S (\<tau> g)
         (cocone_map (F.F.C.cod g) \<circ> F_arr g)))
     (colim (F.F.C.cod f)) (colim (F.F.C.cod g))"
    unfolding reverse_equality [OF seq]
    apply (rule_tac conjunct1 [OF colimit.UP_existence [OF colimit_existence]])
     apply (rule_tac F.F.C.ide_dom [OF arr_g])
    unfolding cocone_def
    apply (rule_tac vertical_composite.is_natural_transformation)
    using vert_comp [OF arr_g] apply simp
    using colim_ide [OF F.F.C.ide_cod [OF arr_g]].




  show "colim_functor (C g f) = S (colim_functor g) (colim_functor f)"
    unfolding colim_functor_def apply (simp add: gf_prop arr_gf)
    apply (rule_tac reverse_equality [OF colimit.UP_uniqueness [OF colimit_existence]])
      apply (rule_tac F.F.C.ide_dom [OF arr_f])
    unfolding cocone_def
     apply (rule_tac vertical_composite.is_natural_transformation)
    using vert_comp [OF arr_gf]
    unfolding F.F.C.dom_comp [OF arr_gf]
              F.F.C.cod_comp [OF arr_gf] apply simp
     apply safe
    using colim_ide [OF F.F.C.ide_cod [OF arr_g]] apply simp
     apply (rule_tac F.S.comp_in_homI)
      apply (rule_tac in_hom_f)
     apply (rule_tac in_hom_g)
  proof-

    fix x
    assume ide_x: "partial_magma.ide (F_ob (F.F.C.dom f)) x"
    then have ide_fx : "partial_magma.ide (F_ob (F.F.C.dom g)) (F_arr f x)"
      unfolding seq
      using functor.preserves_ide [OF F.F.Ffun [OF arr_f]] by simp

    from ide_x have arr_x : "partial_magma.arr (F_ob (F.F.C.dom f)) x"
      using F.F.Fcat [OF F.F.C.ide_dom [OF arr_f]]
      by (simp add: category.ideD(1))
    then have arr_fx : "partial_magma.arr (F_ob (F.F.C.dom g)) (F_arr f x)"
      unfolding seq
      using functor.preserves_arr [OF F.F.Ffun [OF arr_f]] by simp



    have "cocone (F_ob (F.F.C.dom g)) S (\<tau> (F.F.C.dom g)) (colim (F.F.C.cod g))
              (vertical_composite.map (F_ob (F.F.C.dom g)) S (\<tau> g)
         (cocone_map (F.F.C.cod g) \<circ> F_arr g))"
      unfolding cocone_def
      apply (rule_tac vertical_composite.is_natural_transformation)
      using vert_comp [OF arr_g].

    then have rule_g: "(\<And>c. partial_magma.ide (F_ob (F.F.C.dom g)) c \<Longrightarrow>
       ((vertical_composite.map (F_ob (F.F.C.dom g)) S (\<tau> g)
         (cocone_map (F.F.C.cod g) \<circ> F_arr g)) c) = S (colim_UP_map (F.F.C.dom g) (colim (F.F.C.cod g))
              (vertical_composite.map (F_ob (F.F.C.dom g)) S (\<tau> g)
         (cocone_map (F.F.C.cod g) \<circ> F_arr g))) (cocone_map (F.F.C.dom g) c))"
      using conjunct2 [OF colimit.UP_existence 
                      [OF colimit_existence 
                      [OF F.F.C.ide_dom [OF arr_g]]]]
      using colim_ide [OF F.F.C.ide_cod [OF arr_g]]
      by auto


   

    have "cocone (F_ob (F.F.C.dom f)) S (\<tau> (F.F.C.dom f)) (colim (F.F.C.cod f))
              (vertical_composite.map (F_ob (F.F.C.dom f)) S (\<tau> f)
         (cocone_map (F.F.C.cod f) \<circ> F_arr f))"
      unfolding cocone_def
      apply (rule_tac vertical_composite.is_natural_transformation)
      using vert_comp [OF arr_f].

    then have rule_f: "(\<And>c. partial_magma.ide (F_ob (F.F.C.dom f)) c \<Longrightarrow>
       ((vertical_composite.map (F_ob (F.F.C.dom f)) S (\<tau> f)
         (cocone_map (F.F.C.cod f) \<circ> F_arr f)) c) = S (colim_UP_map (F.F.C.dom f) (colim (F.F.C.cod f))
              (vertical_composite.map (F_ob (F.F.C.dom f)) S (\<tau> f)
         (cocone_map (F.F.C.cod f) \<circ> F_arr f))) (cocone_map (F.F.C.dom f) c))"
      using conjunct2 [OF colimit.UP_existence 
                      [OF colimit_existence 
                      [OF F.F.C.ide_dom [OF arr_f]]]]
      using colim_ide [OF F.F.C.ide_cod [OF arr_f]]
      by auto


    have hori_gf : "horizontal_composite 
             (F_ob (F.F.C.dom f)) (F_ob (F.F.C.cod f)) S 
                  (F_arr f) (F_arr f) (\<tau> (F.F.C.cod f)) 
         (\<tau> (F.F.C.cod g) \<circ> F_arr g) (F_arr f) (\<tau> g)"
      unfolding horizontal_composite_def
      using F.\<tau>nat [OF arr_g]
            functor_is_transformation [OF F.F.Ffun [OF arr_f]]
      unfolding natural_transformation_def
      using seq by auto

    have vert_gf : "vertical_composite (F_ob (F.F.C.dom f)) S 
                    (\<tau> (F.F.C.dom f)) 
                    (\<tau> (F.F.C.cod f) \<circ> F_arr f) 
                    (\<tau> (F.F.C.cod g) \<circ> F_arr g \<circ> F_arr f)
                    (\<tau> f) (\<tau> g \<circ> F_arr f)"
      unfolding vertical_composite_def
      using horizontal_composite.is_natural_transformation [OF hori_gf]
            F.\<tau>nat [OF arr_f]
      unfolding natural_transformation_def
      using seq by auto

    show "vertical_composite.map (F_ob (F.F.C.dom f)) S (\<tau> (C g f))
          (cocone_map (F.F.C.cod g) \<circ> F_arr (C g f)) x =
         S (S (colim_UP_map (F.F.C.cod f) (colim (F.F.C.cod g))
                (vertical_composite.map (F_ob (F.F.C.cod f)) S (\<tau> g)
                  (cocone_map (F.F.C.cod g) \<circ> F_arr g)))
             (colim_UP_map (F.F.C.dom f) (colim (F.F.C.cod f))
               (vertical_composite.map (F_ob (F.F.C.dom f)) S (\<tau> f)
                 (cocone_map (F.F.C.cod f) \<circ> F_arr f))))
          (cocone_map (F.F.C.dom f) x) "
      apply (subst F.S.comp_assoc)
      apply (subst reverse_equality [OF rule_f [OF ide_x]])
      apply (subst vertical_composite.map_def)
      using vert_comp [OF arr_gf]
      unfolding F.F.C.dom_comp [OF arr_gf]
                F.F.C.cod_comp [OF arr_gf] apply simp
      apply (simp add: arr_x)
      apply (subst category.ideD(3) [OF F.F.Fcat [OF F.F.C.ide_dom [OF arr_f]] ide_x])
      apply (subst vertical_composite.map_def)
      using vert_comp [OF arr_f] apply simp
      apply (simp add: arr_x)
      apply (subst category.ideD(3) [OF F.F.Fcat [OF F.F.C.ide_dom [OF arr_f]] ide_x])
      unfolding reverse_equality [OF seq]
      apply (subst reverse_equality [OF F.S.comp_assoc])
      apply (subst reverse_equality [OF rule_g])
      using functor.preserves_ide [OF F.F.Ffun [OF arr_f] ide_x] apply (simp add: seq)
      apply (subst F.\<tau>comp [OF arr_gf])
      apply (subst F.F.Ffun_comp [OF arr_gf])
      apply (subst vertical_composite.map_def)
       apply (rule_tac vert_gf)
      apply (simp add: arr_x)
      apply (subst vertical_composite.map_def)
       apply (rule_tac vert_comp [OF arr_g])
      apply (simp add: arr_fx)
      apply (subst category.ideD(3) [OF F.F.Fcat [OF F.F.C.ide_dom [OF arr_f]] ide_x])
      apply (subst category.ideD(3) [OF F.F.Fcat [OF F.F.C.ide_dom [OF arr_g]] ide_fx])
      apply (subst F.S.comp_assoc)
      by simp
  qed
qed


lemma colim_functor_obj_simp :
  assumes "F.F.C.ide A"
  shows "colim_functor A = colim A"
proof-
  interpret Col : colimit "F_ob A" S "\<tau> A" "cocone_map A" "colim A" "colim_UP_map A"
    using colimit_existence [OF assms].
  have EQ: "(vertical_composite.map (F_ob A) S (\<tau> A) (cocone_map A \<circ> F_arr A)) = cocone_map A"
    apply (rule_tac ext)
    apply (subst vertical_composite.map_def)
    using vert_comp [OF F.F.C.ideD(1) [OF assms]]
     apply (simp add: assms)
    apply auto
     apply (simp_all add: Col.\<tau>.is_extensional)
    apply (subst F.F.Ffun_id [OF assms])
    apply (subst Col.C.map_def)
    by simp

  have "F.S.dom (colim_functor A) = colim A"
    unfolding colim_functor_def
    apply (simp add: assms)
    apply (rule_tac F.S.in_hom_dom [OF colim_UP_map_in_hom])
      apply (simp add: assms)
    unfolding EQ
    using Col.cocone apply simp
    using colim_ide [OF assms].
  then show "colim_functor A = colim A"
    unfolding F.S.ideD(2) [OF functor.preserves_ide [OF is_functor assms]].
qed


      
end
       


locale coproduct_cocone =
  C : category C
  for C :: "'a comp"
  and obj :: "'a" +
assumes ide_obj : "C.ide obj"
begin
(*Here we construct a functor SetCat \<longrightarrow> {Categories over C} that sends each set S
  to the functor S \<longrightarrow> C that is constantly obj.*)


interpretation S : set_category SetCat.comp
  using SetCat.is_set_category.

lemma is_discrete_category : "discrete_category c"
  unfolding discrete_category_def free_category_def graph_def
  by simp


definition discrete_functor :: "('s SetCat.arr \<Rightarrow> 's SetCat.arr discrete_category.arr \<Rightarrow> 's SetCat.arr discrete_category.arr)" where
  "discrete_functor f = MkFunctor (discrete_category.comp (S.set (S.dom f)))
                                  (discrete_category.comp (S.set (S.cod f)))
                                  (\<lambda>x. discrete_category.mkIde (S.set (S.cod f)) 
                                  (S.Fun f (discrete_category.toObj x)))"


interpretation DF: functor_to_cat SetCat.comp 
       "(\<lambda>S. discrete_category.comp (S.set S))"
       discrete_functor
  unfolding functor_to_cat_def
  apply (simp add: SetCat.is_category)
  unfolding functor_to_cat_axioms_def
  apply auto
proof-
  show cat: "\<And>c. S.ide c \<Longrightarrow> category (discrete_category.comp (S.set c))"
    apply (rule_tac discrete_category.is_category)
    using is_discrete_category.
  show func: "\<And>c. S.arr c \<Longrightarrow>
         functor (discrete_category.comp (S.Dom c)) (discrete_category.comp (S.Cod c)) (discrete_functor c)"
  proof-
    fix c :: "'s SetCat.arr"
    assume arr_c: "S.arr c"
    interpret Dom: discrete_category "(S.set (S.dom c))"
      using is_discrete_category.
    interpret Cod: discrete_category "(S.set (S.cod c))"
      using is_discrete_category.
    show "functor Dom.comp Cod.comp (discrete_functor c)"
      unfolding functor_def
      apply (simp add: Dom.is_category Cod.is_category)
      unfolding functor_axioms_def
      apply safe
          apply (simp add: discrete_functor_def)
    proof-
      show arr: "\<And>f. Dom.arr f \<Longrightarrow> Cod.arr (discrete_functor c f)"
        unfolding discrete_functor_def
        apply (simp add: arr_c)
        unfolding Cod.arr_char
        using S.Fun_mapsto [OF arr_c] Dom.toObj_in_Obj 
        by auto
      show dom: "\<And>f. Dom.arr f \<Longrightarrow> Cod.dom (discrete_functor c f) = discrete_functor c (Dom.dom f)"
        unfolding Cod.dom_char
        by (simp add: arr)
      show cod: "\<And>f. Dom.arr f \<Longrightarrow> Cod.cod (discrete_functor c f) = discrete_functor c (Dom.cod f)"
        unfolding Cod.cod_char
        by (simp add: arr)
      fix g f
      assume arr_gf: "Dom.seq g f"
      have arr_dfg : "Cod.seq (discrete_functor c g) (discrete_functor c f)"
        apply (rule_tac Dom.seqE [OF arr_gf])
        apply (rule_tac Cod.seqI)
        unfolding dom cod
        by (simp_all add: arr)
      have if_helper : "\<And>P x y. P \<Longrightarrow> (if P then x else y) = x"
        by simp
      show "discrete_functor c (Dom.comp g f) = Cod.comp (discrete_functor c g) (discrete_functor c f)"
        apply (subst Cod.comp_char)
        unfolding if_helper [OF arr_dfg]
        apply (subst Dom.comp_char)
        unfolding if_helper [OF arr_gf]
        by simp
    qed
  qed
  show "\<And>c. S.ide c \<Longrightarrow> discrete_functor c = identity_functor.map (discrete_category.comp (S.set c))"
  proof-
    fix c :: "'s SetCat.arr"
    assume ide_c: "S.ide c"
    then have arr_c : "S.arr c" by simp
    have eq: "S.Dom c = S.set c \<and> S.Cod c = S.set c \<and> S.Fun c = (\<lambda>x\<in>S.Dom c. x)"
      using ide_c
      unfolding S.ide_char [OF arr_c] apply simp
      using S.ideD(3) [OF ide_c] by simp

    interpret D: discrete_category "S.set c"
      using is_discrete_category.
    show "discrete_functor c = D.map"
      apply (rule_tac ext)
      unfolding D.map_def
      unfolding discrete_functor_def
      unfolding conjunct1 [OF eq]
      unfolding conjunct1 [OF conjunct2 [OF eq]]
      unfolding conjunct2 [OF conjunct2 [OF eq]]
      apply auto
      unfolding S.ideD(2) [OF ide_c]
      using D.toObj_in_Obj by simp
  qed
  fix g f :: "'s SetCat.arr"
  assume arr_gf : "S.seq g f"
  then have arr_f: "S.arr f"
    by blast
  from arr_gf have seq_eq : "S.dom g = S.cod f" 
    by blast

  interpret Domf : discrete_category "S.Dom f"
    using is_discrete_category.
  interpret Codf : discrete_category "S.Cod f"
    using is_discrete_category.
  interpret Codg : discrete_category "S.Cod g"
    using is_discrete_category.
  interpret F : "functor" Domf.comp Codf.comp "discrete_functor f"
    using func [OF arr_f].

  show "discrete_functor (SetCat.comp g f) = discrete_functor g \<circ> discrete_functor f"
    apply (rule_tac ext)
    apply (subst discrete_functor_def)
    unfolding S.dom_comp [OF arr_gf]
    unfolding S.cod_comp [OF arr_gf]
    apply auto
     apply (subst discrete_functor_def)
    unfolding seq_eq
     apply (simp add: F.preserves_arr)
     apply (subst discrete_functor_def)
    apply simp
    unfolding S.Fun_comp [OF arr_gf] 
     apply (simp add : Domf.toObj_in_Obj)
     apply (subst Codf.toObj_mkIde)
    using S.Fun_mapsto [OF arr_f] Domf.toObj_in_Obj apply auto[2]
    unfolding seq_eq
    unfolding F.is_extensional
    unfolding discrete_functor_def seq_eq
    by simp
qed

definition cocone where
  "cocone f = constant_functor.map (discrete_category.comp (S.Dom f)) C obj"


lemma is_functor_to_cat : 
  "functor_to_cat SetCat.comp 
   (\<lambda>S. discrete_category.comp (S.set S))
   discrete_functor"
  using DF.functor_to_cat_axioms.


lemma const_fun :"\<And>c. S.ide c \<Longrightarrow> constant_functor (discrete_category.comp (S.set c)) C obj"
  unfolding constant_functor_def
  apply (subst discrete_category.is_category)
   apply (simp add: is_discrete_category)
  unfolding constant_functor_axioms_def
  by (simp add: C.category_axioms ide_obj)

lemma const_functor_overX: "functor_to_cat_overX SetCat.comp C 
       (\<lambda>S. discrete_category.comp (S.set S))
       discrete_functor cocone"
  unfolding cocone_def
  unfolding functor_to_cat_overX_def
  apply (simp add: DF.functor_to_cat_axioms C.category_axioms)
  unfolding functor_to_cat_overX_axioms_def
  apply auto
proof-
  show "\<And>ca. S.ide ca \<Longrightarrow>
          functor (discrete_category.comp (S.set ca)) C
           (constant_functor.map (discrete_category.comp (S.set ca)) C obj)"
    apply (rule_tac constant_functor.is_functor)
    using const_fun.
  have eq: "\<And>c. S.arr c \<Longrightarrow> 
           (constant_functor.map (discrete_category.comp (S.Cod c)) C obj \<circ>
           discrete_functor c) = (constant_functor.map (discrete_category.comp (S.Dom c)) C obj)"
    apply (rule_tac ext)
    apply (subst constant_functor.map_def)
     apply (rule_tac const_fun [OF S.ide_dom])
     apply auto
     apply (subst constant_functor.map_def)
      apply (rule_tac const_fun [OF S.ide_cod])
      apply simp
    using functor.preserves_arr [OF DF.Ffun] 
     apply auto[1]
    by (meson DF.Ffun S.ide_cod const_fun constant_functor.map_def functor.preserves_reflects_arr)
  show nat: "\<And>c. S.arr c \<Longrightarrow>
         natural_transformation (discrete_category.comp (S.Dom c)) C
          (constant_functor.map (discrete_category.comp (S.Dom c)) C obj)
          (constant_functor.map (discrete_category.comp (S.Cod c)) C obj \<circ>
           discrete_functor c)
          (constant_functor.map (discrete_category.comp (S.Dom c)) C obj)"
    apply (simp add: eq)
    apply (rule_tac functor_is_transformation)
    apply (rule_tac constant_functor.is_functor)
    using const_fun [OF S.ide_dom].
  fix g f :: "'s SetCat.arr"
  assume arr_gf : "S.seq g f"
  then have seq_eq: "S.dom g = S.cod f" by blast
  from arr_gf have arr_f: "S.arr f" by blast
  interpret Const : constant_functor "(discrete_category.comp (S.Dom f))" C obj
    using const_fun [OF S.ide_dom [OF arr_f]].

  show "Const.map =
    vertical_composite.map (discrete_category.comp (S.Dom f)) C Const.map
     (constant_functor.map (discrete_category.comp (S.Dom g)) C obj \<circ> discrete_functor f)"
    unfolding seq_eq
    apply (rule_tac ext)
    apply (subst vertical_composite.map_def)
    unfolding vertical_composite_def
    using nat [OF arr_f]
    unfolding eq [OF arr_f]
    unfolding natural_transformation_def
     apply auto
    using ide_obj apply simp
    unfolding Const.map_def by simp
qed



    


        

end



end
