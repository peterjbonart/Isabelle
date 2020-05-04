theory pointedSet_Factorization
  imports Main
          pointedSet
          
begin

locale pointed_set_factorization =
  S: set_category S +
  F: "functor" C S F
  for S :: "'s comp"
  and C :: "'c comp"
  and F :: "'c \<Rightarrow> 's"
  and basepoint :: "'c \<Rightarrow> 's" +
assumes pointed_obj : "\<And>c. F.A.ide c \<Longrightarrow> pointed_set.Obj' ((basepoint c) , S.set (F c))"
  and pointed_arr : "\<And>c. F.A.arr c \<Longrightarrow> S.Fun (F c) (basepoint (F.A.dom c)) = basepoint (F.A.cod c)"
begin

interpretation P : pointed_set.
interpretation PC : category P.pointed_set_comp
  using P.is_category.

definition FOb where
  "FOb c = (basepoint c, S.set (F c))"

definition map where
  "map = MkFunctor C P.pointed_set_comp
         (\<lambda>c. Some (S.Fun (F c) , FOb (F.A.dom c) , FOb (F.A.cod c) ))"


lemma is_functor: "functor C P.pointed_set_comp map"
  unfolding functor_def
  apply (simp add: F.A.category_axioms P.is_category)
  unfolding functor_axioms_def
  apply auto
      apply (simp add: map_def)
proof-
  show arr: "\<And>f. F.A.arr f \<Longrightarrow> PC.arr (local.map f)"
    unfolding map_def apply simp
    unfolding P.arr_char apply simp
    unfolding P.Arr'_def apply auto
  proof-
    fix f
    assume arr_f : "F.A.arr f"
    show "setcat.Arr (S.Fun (F f), snd (FOb (F.A.dom f)), snd (FOb (F.A.cod f)))"
      unfolding FOb_def apply simp
      unfolding setcat.Arr_def
      using S.Fun_mapsto [OF F.preserves_arr [OF arr_f]]
      unfolding F.preserves_dom [OF arr_f]
      unfolding F.preserves_cod [OF arr_f]
      by simp
    show "P.Obj' (FOb (F.A.dom f))"
      unfolding FOb_def
      apply (rule_tac pointed_obj)
      using F.A.ide_dom [OF arr_f].
    show "P.Obj' (FOb (F.A.cod f))"
      unfolding FOb_def
      apply (rule_tac pointed_obj)
      using F.A.ide_cod [OF arr_f].
    show "S.Fun (F f) (fst (FOb (F.A.dom f))) = fst (FOb (F.A.cod f))"
      unfolding FOb_def apply simp
      using pointed_arr [OF arr_f].
  qed
  show dom : "\<And>f. F.A.arr f \<Longrightarrow> PC.dom (local.map f) = local.map (F.A.dom f)"
    unfolding P.dom_char [OF arr]
    unfolding map_def apply simp
    unfolding P.Id'_def apply simp
    unfolding FOb_def by simp
  show cod : "\<And>f. F.A.arr f \<Longrightarrow> PC.cod (local.map f) = local.map (F.A.cod f)"
    unfolding P.cod_char [OF arr]
    unfolding map_def apply simp
    unfolding P.Id'_def apply simp
    unfolding FOb_def by simp
  fix g f
  assume arr_gf : "F.A.seq g f"
  have arr_mgf : "PC.seq (map g) (map f)"
    apply (rule_tac F.A.seqE [OF arr_gf])
    apply (rule_tac PC.seqI)
    unfolding dom cod
    using arr by simp_all
  show "local.map (C g f) = P.pointed_set_comp (local.map g) (local.map f)"
    apply (rule_tac reverse_equality)
    apply (rule_tac P.comp_eq_char2)
        apply (rule_tac arr_mgf)
       apply (rule_tac arr [OF arr_gf])
      apply (subst dom)
    using arr_gf apply blast
      apply (subst dom [OF arr_gf])
    using F.A.dom_comp [OF arr_gf] apply simp
     apply (subst cod)
    using arr_gf apply blast
      apply (subst cod [OF arr_gf])
    using F.A.cod_comp [OF arr_gf] apply simp
  proof-
    fix x
    assume "x \<in> snd (fst (snd (the (local.map f))))"
    then have x_in_dom : "x \<in> S.set (F (F.A.dom f))"
      apply (rule_tac F.A.seqE [OF arr_gf])
      unfolding map_def
      apply simp
      unfolding FOb_def by simp
    show "fst (the (local.map g)) (fst (the (local.map f)) x) = fst (the (local.map (C g f))) x"
      apply (rule_tac F.A.seqE [OF arr_gf])
      unfolding map_def
      by (simp add: x_in_dom)
  qed
qed

end







end
