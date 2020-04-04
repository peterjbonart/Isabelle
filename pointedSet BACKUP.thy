theory pointedSet
  imports Main
         "Category3.SetCat"
         "Category3.InitialTerminal"
         "Category3.Subcategory"
         Gamma
begin


lemma reverse_equality : "a = b \<Longrightarrow> b = a"
  by simp

 


type_synonym 'a pointed_set = "'a \<times> ('a set)"

type_synonym 'a pointed_arr = "('a \<Rightarrow> 'a) \<times> ('a pointed_set) \<times> ('a pointed_set)"


locale pointed_set
begin





abbreviation Dom'
  where "Dom' t \<equiv> fst (snd t)"

abbreviation Cod'
      where "Cod' t \<equiv> snd (snd t)"

abbreviation Fun'
      where "Fun' t \<equiv> fst t"

fun forget :: "'a pointed_arr \<Rightarrow> ('a \<Rightarrow> 'a) \<times> 'a set \<times> 'a set" where
  "forget f = (Fun' f, snd (Dom' f), snd (Cod' f))" 


definition Obj'
  where "Obj' X \<equiv> fst X \<in> (snd X)"

definition Arr'
  where "Arr' t \<equiv> setcat.Arr (forget t) \<and>
                  Obj' (Dom' t) \<and> Obj' (Cod' t) \<and>
                  Fun' t (fst (Dom' t)) = fst (Cod' t)"

definition Id'
  where "Id' X \<equiv> (\<lambda> x \<in> (snd X). x,(X,X))"

definition Comp'      (infixr "\<cdot>" 55)
  where "Comp' s t \<equiv> (if Arr' t \<and> Arr' s \<and> Cod' t = Dom' s then
      (compose (snd (Dom' t)) (Fun' s) (Fun' t), (Dom' t, Cod' s))
      else (\<lambda>x. x, (undefined,{undefined}), (undefined,{})))"





lemma forget_arr: "Arr' f \<Longrightarrow> setcat.Arr (forget f)"
  unfolding Arr'_def by simp

lemma forget_dom: "snd (Dom' f) = setcat.Dom (forget f)"
  by simp

lemma forget_cod: "snd (Cod' f) = setcat.Cod (forget f)"
  by simp

lemma forget_id: "forget (Id' A) = setcat.Id (snd A)"
  unfolding setcat.Id_def Id'_def by simp

lemma forget_comp : "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> Dom' f = Cod' g \<Longrightarrow>
     forget(Comp' f g) = setcat.comp (forget f) (forget g)"
  unfolding setcat.comp_def Comp'_def
proof-
  assume "Arr' f" "Arr' g" "Dom' f = Cod' g"
  have "setcat.Arr (forget f)" using \<open>Arr' f\<close> forget_arr by simp
  have "setcat.Arr (forget g)" using \<open>Arr' g\<close> forget_arr by simp
  have A1: "snd (snd g) = fst (snd f)" using \<open>Dom' f = Cod' g\<close> by simp
    then have A2: "snd (snd (forget g)) = fst (snd (forget f))" by simp
    show "forget
     (if Arr' g \<and> Arr' f \<and> snd (snd g) = fst (snd f)
      then (compose (snd (fst (snd g))) (fst f) (fst g), fst (snd g), snd (snd f))
      else (\<lambda>x. x, (undefined, {undefined}), undefined, {})) =
    (if setcat.Arr (forget g) \<and>
        setcat.Arr (forget f) \<and> snd (snd (forget g)) = fst (snd (forget f))
     then (compose (fst (snd (forget g))) (fst (forget f)) (fst (forget g)),
           fst (snd (forget g)), snd (snd (forget f)))
     else (\<lambda>x. x, {undefined}, {}))"
      apply (simp add: \<open>Arr' f\<close> \<open>Arr' g\<close> Arr'_def \<open>setcat.Arr (forget f)\<close> \<open>setcat.Arr (forget g)\<close> A1 A2)
      by (metis A1 \<open>Arr' f\<close> \<open>Arr' g\<close> pointed_set.Arr'_def)
  qed

lemma forget_faithful : "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd f = snd g \<Longrightarrow>
              forget f = forget g \<Longrightarrow> f = g"
proof
  show "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd f = snd g \<Longrightarrow> forget f = forget g \<Longrightarrow> snd f = snd g" by simp
  show "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd f = snd g \<Longrightarrow> forget f = forget g \<Longrightarrow> fst f = fst g" by simp
qed

lemma dom_obj : "\<And>f. Arr' f \<Longrightarrow> Obj' (fst (snd f))"
by (simp add: Arr'_def Obj'_def)

lemma cod_obj: "\<And>f. Arr' f \<Longrightarrow> Obj' (snd (snd f))"
  by (simp add: Arr'_def Obj'_def)

lemma dom_comp: "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow> fst (snd (g \<cdot> f)) = fst (snd f)"
  by (simp add: Comp'_def)

lemma cod_comp: "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow> snd (snd (g \<cdot> f)) = snd (snd g)"
  by (simp add: Comp'_def)

lemma arr_comp : "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow> Arr' (g \<cdot> f)" 
apply (subst Arr'_def)
  proof-
    have H1: "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow> setcat.Arr (forget (g \<cdot> f))"
      apply (subst forget_comp)
         apply simp 
        apply simp 
       apply simp
      using setcat.seq_char setcat.arr_char
      by (metis forget_arr forget_cod forget_dom)
    have H2: "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow> Obj' (fst (snd (g \<cdot> f)))"
      by (simp add: dom_obj Comp'_def)
    have H3: "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow> Obj' (snd (snd (g \<cdot> f)))"
    by (simp add: cod_obj Comp'_def)
  have H4: "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow>  fst (g \<cdot> f) (fst (fst (snd (g \<cdot> f)))) = fst (snd (snd (g \<cdot> f)))"
    by (simp add: Comp'_def Arr'_def Obj'_def)
  from H1 and H2 and H3 and H4 show "Arr' f \<Longrightarrow>
    Arr' g \<Longrightarrow>
    snd (snd f) = fst (snd g) \<Longrightarrow>
    setcat.Arr (forget (g \<cdot> f)) \<and>
    Obj' (fst (snd (g \<cdot> f))) \<and>
    Obj' (snd (snd (g \<cdot> f))) \<and> fst (g \<cdot> f) (fst (fst (snd (g \<cdot> f)))) = fst (snd (snd (g \<cdot> f)))" by simp
qed





lemma ccpf : "classical_category Obj' Arr' Dom' Cod' Id' Comp'"
  apply (unfold_locales)
  unfolding Id'_def
proof-
  show "\<And>f. Arr' f \<Longrightarrow> Obj' (fst (snd f))" using dom_obj.
  show "\<And>f. Arr' f \<Longrightarrow> Obj' (snd (snd f))" using cod_obj.
  show arr_id: "\<And>a. Obj' a \<Longrightarrow> Arr' (\<lambda>x\<in>snd a. x, a, a)" apply (simp add: Arr'_def Obj'_def)
    using setcat.Arr_Id setcat.Id_def by metis
  show "\<And>a. Obj' a \<Longrightarrow> fst (snd (\<lambda>x\<in>snd a. x, a, a)) = a" by simp
  show "\<And>a. Obj' a \<Longrightarrow> snd (snd (\<lambda>x\<in>snd a. x, a, a)) = a" by simp
  fix f g
  show "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow> Arr' (g \<cdot> f)"
    using arr_comp.
  fix h
  show "Arr' f \<Longrightarrow>  Arr' g \<Longrightarrow> Arr' h \<Longrightarrow>
       snd (snd f) = fst (snd g) \<Longrightarrow> snd (snd g) = fst (snd h) \<Longrightarrow> 
        (h \<cdot> g) \<cdot> f = h \<cdot> g \<cdot> f"
    apply (rule_tac forget_faithful)
  proof-
    show "Arr' f \<Longrightarrow>  Arr' g \<Longrightarrow> Arr' h \<Longrightarrow> 
      snd (snd f) = fst (snd g) \<Longrightarrow> snd (snd g) = fst (snd h) \<Longrightarrow> 
         Arr' ((h \<cdot> g) \<cdot> f)"
      apply (rule_tac arr_comp)
        apply simp
       apply (simp add: arr_comp)
      by (simp add: dom_comp)
    show "Arr' f \<Longrightarrow>  Arr' g \<Longrightarrow>  Arr' h \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow>
           snd (snd g) = fst (snd h) \<Longrightarrow> Arr' (h \<cdot> g \<cdot> f)"
      apply (rule_tac arr_comp)
        apply (simp add: arr_comp)
       apply simp
      by (simp add: cod_comp)
    show "Arr' f \<Longrightarrow>  Arr' g \<Longrightarrow>  Arr' h \<Longrightarrow>
    snd (snd f) = fst (snd g) \<Longrightarrow>
    snd (snd g) = fst (snd h) \<Longrightarrow> snd ((h \<cdot> g) \<cdot> f) = snd (h \<cdot> g \<cdot> f)"
    proof
      show "Arr' f \<Longrightarrow>
    Arr' g \<Longrightarrow>
    Arr' h \<Longrightarrow>
    snd (snd f) = fst (snd g) \<Longrightarrow>
    snd (snd g) = fst (snd h) \<Longrightarrow> fst (snd ((h \<cdot> g) \<cdot> f)) = fst (snd (h \<cdot> g \<cdot> f))"
        by (simp add: dom_comp arr_comp cod_comp)
      show "Arr' f \<Longrightarrow>
    Arr' g \<Longrightarrow>
    Arr' h \<Longrightarrow>
    snd (snd f) = fst (snd g) \<Longrightarrow>
    snd (snd g) = fst (snd h) \<Longrightarrow> snd (snd ((h \<cdot> g) \<cdot> f)) = snd (snd (h \<cdot> g \<cdot> f))"
        by (simp add: dom_comp arr_comp cod_comp)
    qed
    show "Arr' f \<Longrightarrow>
    Arr' g \<Longrightarrow>
    Arr' h \<Longrightarrow>
    snd (snd f) = fst (snd g) \<Longrightarrow>
    snd (snd g) = fst (snd h) \<Longrightarrow> forget ((h \<cdot> g) \<cdot> f) = forget (h \<cdot> g \<cdot> f)"
      apply (subst forget_comp)
         apply (simp add: arr_comp)
        apply simp
       apply (simp add: dom_comp)
      apply (subst forget_comp)
         apply simp
        apply simp
       apply simp
      apply (subst forget_comp)
         apply simp
        apply (simp add: arr_comp)
       apply (simp add: cod_comp)
      apply (subst forget_comp)
         apply simp
        apply simp
       apply simp
      apply (subst setcat.comp_assoc)
        apply (metis arr_comp forget_arr forget_comp setcat.not_Arr_Null setcat.null_char)
        apply (metis arr_comp forget_arr forget_comp setcat.not_Arr_Null setcat.null_char)
      by simp
  qed
  show " Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow> fst (snd (g \<cdot> f)) = fst (snd f)"
    using dom_comp.
  show "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> snd (snd f) = fst (snd g) \<Longrightarrow> snd (snd (g \<cdot> f)) = snd (snd g)"
    using cod_comp.
  show "Arr' f \<Longrightarrow> f \<cdot> (\<lambda>x\<in>snd (fst (snd f)). x, fst (snd f), fst (snd f)) = f"
    apply (rule_tac forget_faithful)
  proof-
    show "Arr' f \<Longrightarrow> Arr' (f \<cdot> (\<lambda>x\<in>snd (fst (snd f)). x, fst (snd f), fst (snd f)))"
      by (simp add: arr_id arr_comp dom_obj)
    show "Arr' f \<Longrightarrow> Arr' f" by simp
    show "Arr' f \<Longrightarrow> snd (f \<cdot> (\<lambda>x\<in>snd (fst (snd f)). x, fst (snd f), fst (snd f))) = snd f"
    proof
      show "Arr' f \<Longrightarrow>
    fst (snd (f \<cdot> (\<lambda>x\<in>snd (fst (snd f)). x, fst (snd f), fst (snd f)))) = fst (snd f)"
        by (simp add: dom_comp arr_id dom_obj)
      show "Arr' f \<Longrightarrow>
    snd (snd (f \<cdot> (\<lambda>x\<in>snd (fst (snd f)). x, fst (snd f), fst (snd f)))) = snd (snd f)"
        by (simp add: cod_comp arr_id dom_obj)
    qed
    have eq: "(\<lambda>x\<in>snd (fst (snd f)). x, fst (snd f), fst (snd f)) = Id' (Dom' f)"
      by (simp add: Id'_def)
    show "Arr' f \<Longrightarrow> forget (f \<cdot> (\<lambda>x\<in>snd (fst (snd f)). x, fst (snd f), fst (snd f))) = forget f"
      apply (subst forget_comp)
         apply simp
        apply (simp add: arr_id dom_obj)
       apply simp
      apply (subst eq)
      apply (subst forget_id)
      using forget_arr setcat.comp_Id_Dom by fastforce
  qed
  show "Arr' f \<Longrightarrow> (\<lambda>x\<in>snd (snd (snd f)). x, snd (snd f), snd (snd f)) \<cdot> f = f"
    apply (rule_tac forget_faithful)
proof-
    show "Arr' f \<Longrightarrow> Arr' ((\<lambda>x\<in>snd (snd (snd f)). x, snd (snd f), snd (snd f)) \<cdot> f)"
      by (simp add: arr_id arr_comp cod_obj)
    show "Arr' f \<Longrightarrow> Arr' f" by simp
    show "Arr' f \<Longrightarrow> snd ((\<lambda>x\<in>snd (snd (snd f)). x, snd (snd f), snd (snd f)) \<cdot> f) = snd f"
    proof
      show "Arr' f \<Longrightarrow>
    fst (snd ((\<lambda>x\<in>snd (snd (snd f)). x, snd (snd f), snd (snd f)) \<cdot> f)) = fst (snd f)"
        by (simp add: dom_comp arr_id cod_obj)
      show "Arr' f \<Longrightarrow>
    snd (snd ((\<lambda>x\<in>snd (snd (snd f)). x, snd (snd f), snd (snd f)) \<cdot> f)) = snd (snd f)"
        by (simp add: cod_comp arr_id cod_obj)
    qed
    have eq: "(\<lambda>x\<in>snd (snd (snd f)). x, snd (snd f), snd (snd f)) = Id' (Cod' f)"
      by (simp add: Id'_def)
    show "Arr' f \<Longrightarrow> forget ((\<lambda>x\<in>snd (snd (snd f)). x, snd (snd f), snd (snd f)) \<cdot> f) = forget f"
      apply (subst forget_comp)
         apply (simp add: arr_id cod_obj)
        apply simp
       apply simp
      apply (subst eq)
      apply (subst forget_id)
    using forget_arr setcat.comp_Cod_Id by fastforce
qed
qed




lemma fun_comp_char : "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> Dom' f = Cod' g \<Longrightarrow> 
                      x \<in> snd (Dom' g) \<Longrightarrow> fst (f \<cdot> g) x = (fst f) (fst g x)"
  unfolding Comp'_def by simp

lemma comp_arr : "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> Dom' f = Cod' g \<Longrightarrow> Arr' (f \<cdot> g)"
  apply (subst Arr'_def)
  apply (subst forget_comp)
     apply simp
    apply simp
   apply simp
  apply (subst setcat.Arr_comp)
  apply (simp add: Arr'_def)
    apply (simp add: Arr'_def)
   apply auto
    apply (subst dom_comp)
       apply simp_all
    apply (simp add: Arr'_def)
   apply (subst cod_comp)
      apply simp_all
   apply (simp add: Arr'_def)
  apply (subst fun_comp_char)
      apply (simp_all add: dom_comp)
   apply (simp add: Arr'_def Obj'_def)
  apply (subst cod_comp)
     apply simp_all
  by (simp add: Arr'_def Obj'_def)

lemma fun_eq_char : "Arr' f \<Longrightarrow> Arr' g \<Longrightarrow> Dom' f = Dom' g \<Longrightarrow> Cod' f = Cod' g \<Longrightarrow> 
                     (\<And>x. x \<in> snd (Dom' f) \<Longrightarrow> fst f x = fst g x) \<Longrightarrow> f = g"
proof
  assume "Arr' f" "Arr' g"
  assume "Dom' f = Dom' g"
  assume "Cod' f = Cod' g"
  assume A: "(\<And>x. x \<in> snd (Dom' f) \<Longrightarrow> fst f x = fst g x)"
  show "fst f = fst g"
  proof
    fix x
    have"x \<in> snd (Dom' f) \<or> x \<notin> snd (Dom' f)" by auto
    then show "fst f x = fst g x"
    proof
      assume "x \<in> snd (Dom' f)"
      thus "fst f x = fst g x" using A by simp
    next
      assume "x \<notin> snd (Dom' f)"
      from \<open>Arr' f\<close> have "fst f \<in> extensional (snd (Dom' f))" unfolding Arr'_def setcat.Arr_def by simp
      from this and \<open>x \<notin> snd (Dom' f)\<close> have eq1:"fst f x = undefined" by (meson extensional_arb)

      from \<open>x \<notin> snd (Dom' f)\<close> have "x \<notin> snd (Dom' g)" using \<open>Dom' f = Dom' g\<close> by simp
      from \<open>Arr' g\<close> have "fst g \<in> extensional (snd (Dom' g))" unfolding Arr'_def setcat.Arr_def by simp
      from this and \<open>x \<notin> snd (Dom' g)\<close> have eq2:"fst g x = undefined" by (meson extensional_arb)

      then show "fst f x = fst g x" using eq1 eq2 by simp
    qed
  qed
  show "snd f = snd g"
  proof
    show "fst (snd f) = fst (snd g)" using \<open>fst (snd f) = fst (snd g)\<close>.
    show "snd (snd f) = snd (snd g)" using \<open>snd (snd f) = snd (snd g)\<close>.
  qed
qed

lemma comp_eq_char:
  assumes "Arr' f" "Arr' g" "Arr' h"
       "Dom' g = Dom' h" "Cod' f = Cod' h" "Dom' f = Cod' g"
  and fst_eq: "\<And>x. x \<in> (snd (Dom' g)) \<Longrightarrow> fst f (fst g x) = fst h x"
  shows "f \<cdot> g = h"
  apply (rule_tac fun_eq_char)
      apply (rule_tac comp_arr [OF \<open>Arr' f\<close> \<open>Arr' g\<close> \<open>Dom' f = Cod' g\<close>])
     apply (rule_tac \<open>Arr' h\<close>)
    apply (subst dom_comp [OF \<open>Arr' g\<close> \<open>Arr' f\<close> reverse_equality [OF \<open>Dom' f = Cod' g\<close>]])
    apply (rule_tac \<open>Dom' g = Dom' h\<close>)
   apply (subst cod_comp [OF \<open>Arr' g\<close> \<open>Arr' f\<close> reverse_equality [OF \<open>Dom' f = Cod' g\<close>]])
  apply (rule_tac \<open>Cod' f = Cod' h\<close>)
proof-
  fix x
  assume "x \<in> snd (Dom' (f \<cdot> g))"
  then have "x \<in> snd (Dom' g)"
    using dom_comp [OF \<open>Arr' g\<close> \<open>Arr' f\<close> reverse_equality [OF \<open>Dom' f = Cod' g\<close>]] by simp
  show "fst (f \<cdot> g) x = fst h x"
    unfolding Comp'_def
    using \<open>Arr' g\<close> \<open>Arr' f\<close> \<open>Dom' f = Cod' g\<close> \<open>x \<in> snd (Dom' g)\<close> apply simp
    using fst_eq.
qed



lemma maps_to_char : "Arr' f \<Longrightarrow> (\<And>x. x \<in> snd (Dom' f) \<Longrightarrow> fst f x \<in> snd (Cod' f))"
proof-
  assume "Arr' f"
  then have "fst f \<in> (fst (snd (forget f))) \<rightarrow> (snd (snd (forget f)))"
    unfolding Arr'_def setcat.Arr_def by simp
  then have "fst f \<in> (snd (Dom' f)) \<rightarrow> (snd (Cod' f))" by simp
  then show "(\<And>x. x \<in> snd (Dom' f) \<Longrightarrow> fst f x \<in> snd (Cod' f))" by blast
qed



lemma pointed_finite_imp_nat_seg_image_inj_on:
  assumes "Obj' A" "finite (snd A)"
  shows "\<exists>(n :: nat) f. bij_betw f {i. i<n} (snd A) \<and> f 0 = fst A"
proof-
  from finite_imp_nat_seg_image_inj_on [OF \<open>finite (snd A)\<close>]
  obtain f and n :: nat where bij: "bij_betw f {i. i<n} (snd A)"
    by (auto simp: bij_betw_def)

  have "fst A \<in> snd A"
    using \<open>Obj' A\<close> unfolding Obj'_def.
  then have "fst A \<in> f ` {i. i < n}"
    using bij unfolding bij_betw_def by simp
  then have "\<exists>i \<in> {i. i<n}. f i = fst A"
    by auto
  then obtain i where i_def: "i < n \<and> f i = fst A" by auto
  then have "n > 0"
    using i_def by auto
  define switch :: "nat \<Rightarrow> nat" where
     "switch = (\<lambda>n. if n = 0 then i else (if n = i then 0 else n))"
  have switch_bij : "bij_betw switch {i. i<n} {i. i<n}"
    unfolding bij_betw_def switch_def inj_on_def apply simp
    apply auto
    apply (simp add: i_def)
  proof-
    fix x
    assume "x \<noteq> i"
    assume "x < n"
    assume H: "x \<notin> (\<lambda>a. 0) ` ({i. i < n} \<inter> Collect ((<) 0) \<inter> {i})"
    have "i = 0 \<or> 0 < i" by auto
    then show "0 < x"
    proof
      assume "i = 0"
      then show "0 < x" using \<open>x \<noteq> i\<close> by simp
    next
      assume "0 < i"
      then have "i \<in> ({i. i < n} \<inter> Collect ((<) 0) \<inter> {i})"
        by (simp add: i_def)
      then have "(\<lambda>a. 0) ` ({i. i < n} \<inter> Collect ((<) 0) \<inter> {i}) = {0}"
        by auto
      from this and H have "x \<notin> {0}" by blast
      then show "0 < x" by auto
    qed
  qed
  define f2 where "f2 = compose {i. i<n} f switch"
  have f2_bij : "bij_betw f2 {i. i<n} (snd A)"
    unfolding f2_def
    apply (rule_tac bij_betw_compose)
    using switch_bij apply simp
    using bij.
  then have f2_thesis: "bij_betw f2 {i. i < n} (snd A) \<and> f2 0 = fst A"
    apply simp
    unfolding f2_def switch_def apply (simp add: \<open>n > 0\<close>)
    using i_def by simp
  then show "\<exists>(n::nat) f. bij_betw f {i. i < n} (snd A) \<and> f 0 = fst A"
    apply (rule_tac exI)
    apply (rule_tac exI)
    by auto
qed
    

definition finite_set_length :: "'a pointed_set \<Rightarrow> nat" where
  "finite_set_length A \<equiv> (SOME (n :: nat). \<exists>f. bij_betw f {i. i<n} (snd A) \<and> f 0 = fst A)"

definition finite_set_interval_bijection :: "'a pointed_set \<Rightarrow> nat \<Rightarrow> 'a" where
  "finite_set_interval_bijection A \<equiv> (SOME f. bij_betw f {i. i<finite_set_length A} (snd A) \<and> f 0 = fst A)"

lemma finite_set_interval_bijection_char :
  assumes "Obj' A" "finite (snd A)" 
  shows "bij_betw (finite_set_interval_bijection A) {i. i<finite_set_length A} (snd A) \<and>
         (finite_set_interval_bijection A) 0 = fst A"
proof-
  have H: "\<exists>f. bij_betw f {i. i < (finite_set_length A)} (snd A) \<and>
      f 0 = fst A"
    unfolding finite_set_length_def
    using someI_ex [OF pointed_finite_imp_nat_seg_image_inj_on [OF \<open>Obj' A\<close> \<open>finite (snd A)\<close>]].
  show "bij_betw (finite_set_interval_bijection A) {i. i < finite_set_length A} (snd A) \<and>
    finite_set_interval_bijection A 0 = fst A"
    unfolding finite_set_interval_bijection_def
    using someI_ex [OF H].
qed

lemma pointed_set_length_nn : 
  assumes "Obj' A" "finite (snd A)" 
  shows "finite_set_length A > 0"
proof-
  have "fst A \<in> snd A"
    using \<open>Obj' A\<close> unfolding Obj'_def.
  then have "fst A \<in> (finite_set_interval_bijection A) ` {i . i < (finite_set_length A)}"
    using finite_set_interval_bijection_char [OF \<open>Obj' A\<close> \<open>finite (snd A)\<close>]
    unfolding bij_betw_def by simp
  then obtain i where "i < (finite_set_length A)" by auto
  then show "0 < finite_set_length A" by simp
qed

 




section "Completeness"


context begin

(*LC is an abbreviation for "list completion"*)
(*It is a type containing 'a, which is closed under taking lists*)
datatype 'a LC = Just 'a | K nat | Join "'a LC list"

(*parr is an abbreviation for pointed arrow*)
type_synonym 'a parr =  "('a \<Rightarrow> 'a) \<times> ('a pointed_set) \<times> ('a pointed_set)"




subsection "Finite Products"

fun pointed_product :: "'a LC pointed_set list \<Rightarrow> 'a LC pointed_set" where 
  "pointed_product X = (Join (rev_get (length X) (\<lambda>n. fst (get X n))) ,
                      {x. \<exists>xs. x = Join xs \<and> length xs = length X \<and> (\<forall>n< length X. get xs n \<in> snd (get X n))})"


definition prod_proj :: "'a LC pointed_set list \<Rightarrow> nat \<Rightarrow> 'a LC parr" where
  "prod_proj X n = ((\<lambda>x \<in> snd (pointed_product X). get (SOME xs. x = Join xs) n), 
                    pointed_product X , get X n)"

definition prod_UP_map :: "'a LC parr list \<Rightarrow> 'a LC pointed_set \<Rightarrow> 'a LC parr" where
  "prod_UP_map cone X = ((\<lambda>x \<in>snd X. Join (rev_get (length cone) (\<lambda>n. fst (get cone n) x)  )),
              (X, pointed_product (rev_get (length cone) (\<lambda>n. Cod' (get cone n)))))"

lemma pointed_product_obj: 
  assumes "\<forall>n<length X. Obj' (get X n)" 
  shows "Obj' (pointed_product X)"
  unfolding Obj'_def
  apply (simp add: get_rev_get)
  using \<open>\<forall>n<length X. Obj' (get X n)\<close>
  unfolding Obj'_def.


lemma prod_proj_arr : "\<forall> k<length f . Obj' (get f k) \<Longrightarrow> 
                   k < length f \<Longrightarrow> Arr' (prod_proj f k)"
  unfolding Arr'_def apply safe
proof-
  assume "\<forall>k<length f. Obj' (get f k)"
  then have pointed: "\<forall>k<length f. fst (get f k) \<in> snd (get f k)"
    unfolding Obj'_def.
  assume "k < length f"
  show "setcat.Arr (forget (prod_proj f k))"
    unfolding setcat.Arr_def prod_proj_def apply simp
  proof
    fix x
    assume "x \<in> {Join xs |xs. length xs = length f \<and> (\<forall>n<length f. get xs n \<in> snd (get f n))}"
    then obtain xs where xs_def : "x = Join xs \<and> length xs = length f \<and> (\<forall>n<length f. get xs n \<in> snd (get f n))" by auto
    have xs_some : "(SOME xs. x = Join xs) = xs"
    proof
      show "x = Join xs" by (simp add: xs_def)
      show "\<And>xsa. x = Join xsa \<Longrightarrow> xsa = xs" by (simp add: xs_def)
    qed
    show "get (SOME xs. x = Join xs) k \<in> snd (get f k)"
      apply (subst xs_some)
      using xs_def \<open>k<length f\<close> by simp
  qed
  show "Obj' (fst (snd (prod_proj f k)))"
    unfolding prod_proj_def apply simp
    unfolding Obj'_def apply simp
    apply (simp add: get_rev_get)
    using pointed.
  show "Obj' (snd (snd (prod_proj f k)))"
    unfolding prod_proj_def apply simp
    unfolding Obj'_def
    using pointed \<open>k < length f\<close> by simp
  have "(\<forall>n<length f. get (rev_get (length f) (\<lambda>n. fst (get f n))) n \<in> snd (get f n))"
    apply (simp add: get_rev_get)
    using pointed.
  then show "fst (prod_proj f k) (fst (fst (snd (prod_proj f k)))) = fst (snd (snd (prod_proj f k)))"
    unfolding prod_proj_def apply simp
    by (simp add: get_rev_get \<open>k < length f\<close>)
qed

lemma prod_UP_map_arr: "(\<forall>k<length cone. Arr' (get cone k) \<and> Dom' (get cone k) = X \<and> Cod' (get cone k) = get c k)
    \<Longrightarrow> Obj' X \<Longrightarrow>Arr' (prod_UP_map cone X)"
  apply (subst Arr'_def)
  apply safe
proof-
  assume cone: "\<forall>k<length cone.
       Arr' (get cone k) \<and>
       fst (snd (get cone k)) = X \<and> snd (snd (get cone k)) = get c k"
  assume "Obj' X" 
  have "\<And>k. k < length cone \<Longrightarrow> Obj' (get c k)"
    using cone
    unfolding Arr'_def by auto
  show "setcat.Arr (forget (prod_UP_map cone X))"
    unfolding setcat.Arr_def prod_UP_map_def apply simp
    apply auto
  proof-
    fix x n
    assume "x \<in> snd X"
    assume "n < length cone"
    have "fst (get cone n)
            \<in> snd (fst (snd (get cone n))) \<rightarrow> snd (snd (snd (get cone n)))"
      using cone unfolding Arr'_def setcat.Arr_def apply auto
      using \<open>n < length cone\<close> by blast
    then have "fst (get cone n)
            \<in> snd X \<rightarrow> snd (get c n)"
      using cone \<open>n < length cone\<close> by simp
    show "get (rev_get (length cone) (\<lambda>n. fst (get cone n) x)) n
           \<in> snd (get (rev_get (length cone) (\<lambda>n. snd (snd (get cone n)))) n)"
      apply (simp add: get_rev_get \<open>n < length cone\<close>)
      using cone unfolding Arr'_def setcat.Arr_def
      using \<open>fst (get cone n) \<in> snd X \<rightarrow> snd (get c n)\<close>
            \<open>x \<in> snd X\<close>
            \<open>n < length cone\<close> by auto
  qed
  show "Obj' (fst (snd (prod_UP_map cone X)))"
    unfolding prod_UP_map_def apply simp
    using \<open>Obj' X\<close>.
  show "Obj' (snd (snd (prod_UP_map cone X)))"
    unfolding prod_UP_map_def apply simp
    unfolding Obj'_def apply auto
    apply (simp add: get_rev_get)
    apply (simp add: cone)
    using \<open>\<And>k. k < length cone \<Longrightarrow> Obj' (get c k) \<close>
    unfolding Obj'_def.
  have cone_pointed: "\<And>n. n < length cone \<Longrightarrow> 
        fst (get cone n) (fst (Dom' (get cone n))) = fst (Cod' (get cone n))"
    using cone
    unfolding Arr'_def by auto
  show "fst (prod_UP_map cone X) (fst (fst (snd (prod_UP_map cone X)))) =
    fst (snd (snd (prod_UP_map cone X)))"
    unfolding prod_UP_map_def 
    using \<open>Obj' X\<close>
    unfolding Obj'_def apply simp
    apply (rule_tac getFaithful)
     apply simp
    apply (simp add: get_rev_get)
    using cone_pointed cone by simp
qed


lemma prod_UP_map_dom : "Dom' (prod_UP_map cone X) = X"
  unfolding prod_UP_map_def by simp

lemma prod_UP_map_cod : "Cod' (prod_UP_map cone X) = pointed_product (fmap Cod' cone)"
  unfolding prod_UP_map_def by simp


lemma productUP : "(\<forall>k<length cone. Arr' (get cone k) \<and> Dom' (get cone k) = X \<and> Cod' (get cone k) = get c k)
    \<Longrightarrow> Obj' X \<Longrightarrow> length cone = length c \<Longrightarrow> \<exists>! f. Arr' f \<and> Dom' f = X \<and> Cod' f = (pointed_product c) \<and>
    (\<forall>k<length cone. (prod_proj c k) \<cdot> f = get cone k )"
proof
  assume cone : "\<forall>k<length cone.
       Arr' (get cone k) \<and>
       fst (snd (get cone k)) = X \<and> snd (snd (get cone k)) = get c k"
  assume "Obj' X"
  have c_obj: "\<forall>k < length cone. Obj' (get c k)"
    using cone
    unfolding Arr'_def by auto
  assume "length cone = length c" 

  have arr_up: "Arr' (prod_UP_map cone X)"
    using prod_UP_map_arr [OF cone \<open>Obj' X\<close>].
  have dom_up: "fst (snd (prod_UP_map cone X)) = X"
    unfolding prod_UP_map_def by simp
  have cod_up: "snd (snd (prod_UP_map cone X)) =
    (Join (rev_get (length c) (\<lambda>n. fst (get c n))),
     {Join xs |xs. length xs = length c \<and> (\<forall>n<length c. get xs n \<in> snd (get c n))})"
    unfolding prod_UP_map_def apply auto
      apply (rule_tac getFaithful)
       apply (simp add: \<open>length cone = length c\<close>)
    by (simp_all add: \<open>length cone = length c\<close> get_rev_get cone)

  show "Arr' (prod_UP_map cone X) \<and>
    fst (snd (prod_UP_map cone X)) = X \<and>
    snd (snd (prod_UP_map cone X)) = pointed_product c \<and>
    (\<forall>k<length cone. prod_proj c k \<cdot> (prod_UP_map cone X) = get cone k)"
    apply auto
  proof-
    show "Arr' (prod_UP_map cone X)"
      using arr_up.
    show "fst (snd (prod_UP_map cone X)) = X"
      using dom_up.
    show "snd (snd (prod_UP_map cone X)) =
    (Join (rev_get (length c) (\<lambda>n. fst (get c n))),
     {Join xs |xs. length xs = length c \<and> (\<forall>n<length c. get xs n \<in> snd (get c n))})"
      using cod_up.
    fix k
    assume "k < length cone"
    have arr_proj : "Arr' (prod_proj c k)"
      apply (rule_tac prod_proj_arr)
      using c_obj \<open>length cone = length c\<close> apply simp
      using \<open>k < length cone\<close> \<open>length cone = length c\<close> by simp
    have seq : "snd (snd (prod_UP_map cone X)) = fst (snd (prod_proj c k))"
      unfolding prod_proj_def apply simp
      using cod_up.
    show "prod_proj c k \<cdot> prod_UP_map cone X = get cone k"
      apply (rule_tac comp_eq_char)
      using arr_proj apply simp
      using arr_up apply simp
      using cone \<open>k < length cone\<close> apply simp
      using \<open>fst (snd (prod_UP_map cone X)) = X\<close>
            cone \<open>k < length cone\<close> apply simp
       apply (subst prod_proj_def) apply simp
      using cone \<open>k < length cone\<close> apply simp
      using seq apply simp
    proof-
      fix x
      assume "x \<in> snd (fst (snd (prod_UP_map cone X)))"
      then have "x \<in> snd X"
        using \<open>fst (snd (prod_UP_map cone X)) = X\<close> by simp
      have proj_def_lemma: "(\<forall>n<length c.
         get (rev_get (length cone) (\<lambda>n. fst (get cone n) x)) n \<in> snd (get c n))"
        apply (simp add: get_rev_get \<open>length cone = length c\<close>)
        apply auto
      proof-
        fix n
        assume "n < length c"
        then have "n < length cone"
          using \<open>length cone = length c\<close> by simp
        then have "Arr' (get cone n)"
          using cone by simp
        then have "fst (get cone n) \<in> snd (Dom' (get cone n)) \<rightarrow> snd (Cod' (get cone n))"
          unfolding Arr'_def setcat.Arr_def by simp
        then have "fst (get cone n) \<in> snd X \<rightarrow> snd (get c n)"
          using cone \<open>n < length cone\<close> by simp
        then show "fst (get cone n) x \<in> snd (get c n)"
          using \<open>x \<in> snd X\<close> by auto
      qed
      show "fst (prod_proj c k) (fst (prod_UP_map cone X) x) = fst (get cone k) x"
        unfolding prod_UP_map_def
        using \<open>x \<in> snd X\<close> apply simp
        unfolding prod_proj_def
        using proj_def_lemma \<open>length cone = length c\<close> apply simp
        using get_rev_get \<open>k < length cone\<close> \<open>length cone = length c\<close> by auto
    qed
  qed
  fix f
  assume f_def: "Arr' f \<and>
         fst (snd f) = X \<and>
         snd (snd f) = pointed_product c \<and>
         (\<forall>k<length cone. prod_proj c k \<cdot> f = get cone k)"
  show "f = prod_UP_map cone X"
    apply (rule_tac fun_eq_char)
        apply (simp add: f_def)
       apply (simp add: arr_up)
      apply (simp add: dom_up f_def)
     apply (simp add: cod_up f_def)
  proof-
    fix x
    assume "x \<in> snd (Dom' f)"
    then have "x \<in> snd X"
      using f_def by simp
    have "fst f \<in> snd X \<rightarrow> snd (pointed_product c)"
      using f_def
      unfolding Arr'_def setcat.Arr_def by auto
    then have "fst f x \<in> snd (pointed_product c)"
      using \<open>x \<in> snd X\<close> by auto
    then have ex_xs : "(\<exists>xs. fst f x = Join xs \<and>
           length xs = length c \<and> (\<forall>n<length c. get xs n \<in> snd (get c n)))" by simp
    then obtain xs where xs_def: "fst f x = Join xs \<and> length xs = length c \<and>
                      (\<forall>n<length c. get xs n \<in> snd (get c n))" by auto
    have xs_some : "(SOME xs. fst f x = Join xs) = xs"
    proof
      show "fst f x = Join xs" by (simp add: xs_def)
      show "\<And>xsa. fst f x = Join xsa \<Longrightarrow> xsa = xs" by (simp add: xs_def)
    qed
    show "fst f x = fst (prod_UP_map cone X) x"
      unfolding prod_UP_map_def 
      using \<open>x \<in> snd X\<close> apply simp
      apply (simp add: xs_def)
      apply (rule_tac getFaithful)
       apply (simp add: xs_def \<open>length cone = length c\<close>)
      apply (subst get_rev_get)
       apply (simp add: xs_def \<open>length cone = length c\<close>)
    proof-
      fix n
      assume "n < length xs"
      then have "n < length cone"
        by (simp add: xs_def \<open>length cone = length c\<close>)
      then have "prod_proj c n \<cdot> f = get cone n"
        using f_def by simp
      have "Arr' f" using f_def by simp
      have arr_proj : "Arr' (prod_proj c n)"
        apply (rule_tac prod_proj_arr)
        using c_obj \<open>length cone = length c\<close> apply simp
        using \<open>n < length cone\<close> \<open>length cone = length c\<close> by simp 
      have seq: "snd (snd f) = fst (snd (prod_proj c n))"
        unfolding prod_proj_def apply simp
        using f_def by simp
      have "x \<in> snd (Dom' f)"
        using \<open>x \<in> snd X\<close> f_def by simp
      have "fst (prod_proj c n \<cdot> f) x = get xs n"
        unfolding Comp'_def 
        using \<open>Arr' f\<close> arr_proj seq \<open>x \<in> snd (Dom' f)\<close> apply simp
        apply (subst prod_proj_def) 
        using ex_xs apply simp
        using xs_some by simp
      then show "get xs n = fst (get cone n) x"
        using \<open>prod_proj c n \<cdot> f = get cone n\<close> by simp
    qed
  qed
qed




subsection "Quotients"

fun quotient_by_equiv_rel:: "'a pointed_set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a pointed_set" where
 "quotient_by_equiv_rel A R = (Eps(\<lambda>b. R (fst A) b \<and> b \<in> (snd A))  ,  {i. \<exists>a \<in> (snd A). i = Eps(\<lambda>b. R a b \<and> b \<in> (snd A))  })"

fun quotient_proj :: "'a pointed_set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 
            ('a \<Rightarrow> 'a) \<times> 'a pointed_set \<times> 'a pointed_set" where
  "quotient_proj A R = ( \<lambda>a\<in>(snd A). Eps(\<lambda>b. R a b \<and> b \<in> (snd A))  ,(A ,quotient_by_equiv_rel A R))"


fun quotient_section :: "'a pointed_set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
            ('a \<Rightarrow> 'a) \<times> 'a pointed_set \<times> 'a pointed_set" where
  "quotient_section A R = ((\<lambda>a \<in> snd (quotient_by_equiv_rel A R). 
          (if a = fst (quotient_proj A R) (fst A) then fst A else a )),
               (quotient_by_equiv_rel A R, A))"

fun cur_rel :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "cur_rel R a b = ((a, b) \<in> R)"


lemma quotient_lemma : "sym R \<Longrightarrow> trans R \<Longrightarrow> cur_rel R a b \<Longrightarrow> 
       Eps (\<lambda>c. cur_rel R a c) = Eps (\<lambda>c. cur_rel R b c)"
proof-
  assume sym: "sym R"
  assume trans: "trans R"
  assume "cur_rel R a b"
  have "cur_rel R a = cur_rel R b"
  proof
    fix x
    show "cur_rel R a x = cur_rel R b x"
    proof
      from trans and \<open>cur_rel R a b\<close> show "cur_rel R b x \<Longrightarrow> cur_rel R a x"
        by (meson trans_def cur_rel.elims(2) cur_rel.elims(3))
      from sym have sym2: "\<And> a b. cur_rel R a b \<Longrightarrow> cur_rel R b a"
        by (simp add: sym_def)
      from this and \<open>cur_rel R a b\<close> have "cur_rel R b a" by simp
      from this and trans show "cur_rel R a x \<Longrightarrow> cur_rel R b x"
      by (meson cur_rel.elims(2) cur_rel.elims(3) transD)
    qed
  qed
  then show " (SOME c. cur_rel R a c) = (SOME c. cur_rel R b c)" by simp
qed

lemma quot_proj_arr : "Obj' A \<Longrightarrow> Arr' (quotient_proj A R)"
  unfolding Arr'_def Obj'_def apply auto
  unfolding setcat.Arr_def apply simp
proof
  fix a
  assume irrelevant : "fst A \<in> snd A"
  assume "a \<in> snd A"
  show " (SOME b. R a b \<and> b \<in> snd A) \<in> {i. \<exists>a\<in>snd A. i = (SOME b. R a b \<and> b \<in> snd A)}"
  proof
    show "\<exists>z\<in>snd A. (SOME b. R a b \<and> b \<in> snd A) = (SOME b. R z b \<and> b \<in> snd A)"
    proof
      show "a \<in> snd A" using \<open>a \<in> snd A\<close>.
      show "(SOME b. R a b \<and> b \<in> snd A) = (SOME b. R a b \<and> b \<in> snd A)" by simp
    qed
  qed
qed


lemma R_implies_quot_eq : assumes equiv: "equiv (snd A) {(x,y). R x y}"
  and "R x y" "x \<in> snd A" "y \<in> snd A" 
  shows "fst (quotient_proj A R) x = fst (quotient_proj A R) y"
  using \<open>x \<in> snd A\<close> \<open>y \<in> snd A\<close> apply simp
proof-
  define R' where "R' = {(x,y). R x y \<and> y \<in> snd A}"
  have propeq: "\<And>x. \<And>b. ((R x b \<and> b \<in> snd A) = (cur_rel R' x b))" unfolding R'_def by simp
  show "(SOME b. R x b \<and> b \<in> snd A) = (SOME b. R y b \<and> b \<in> snd A)"
    apply (subst propeq)
    apply (subst propeq)
    apply (rule_tac quotient_lemma)
    unfolding sym_def trans_def R'_def apply auto
    using equiv unfolding equiv_def sym_def apply simp
    using equiv unfolding equiv_def refl_on_def apply blast
    using equiv unfolding equiv_def trans_def apply blast
    using \<open>R x y\<close> \<open>y \<in> snd A\<close> by simp_all
qed


lemma quot_sec_arr : "equiv (snd A) {(x,y). R x y} \<Longrightarrow> Obj' A \<Longrightarrow> Arr' (quotient_section A R)"
  unfolding Arr'_def Obj'_def apply auto
  unfolding setcat.Arr_def apply auto
proof-
  fix a c
  assume equiv: "equiv (snd A) {(x,y). R x y}"
  assume irrelevant: "fst A \<in> snd A"
  assume irrelevant2: "a \<in> snd A"
  assume irrelevant3: "(SOME b. R (fst A) b \<and> b \<in> snd A) = (SOME b. R a b \<and> b \<in> snd A)"
  assume "c \<in> snd A"
  from this and equiv have "(c,c) \<in> {(x,y). R x y}"
    unfolding equiv_def refl_on_def by simp
  then have "R c c" by simp
  obtain P where P_def: "P = (\<lambda>b. R c b \<and> b \<in> snd A)" by simp
  from this and \<open>c \<in> snd A\<close> and \<open>R c c\<close> have "P c" by simp
  then have "P (SOME b. P b)" by (meson someI_ex)
  then show "(SOME b. R c b \<and> b \<in> snd A) \<in> snd A" by (simp add: P_def)
qed

lemma proj_sec_id : "equiv (snd A) {(x, y). R x y} \<Longrightarrow> Obj' A \<Longrightarrow> (quotient_proj A R) \<cdot> (quotient_section A R) = Id' (quotient_by_equiv_rel A R)"
  apply (rule_tac fun_eq_char)
      apply (rule_tac comp_arr)
proof-
  show arr1: "equiv (snd A) {(x, y). R x y} \<Longrightarrow> Obj' A \<Longrightarrow> Arr' (quotient_proj A R)"
    apply (subst quot_proj_arr)
    by simp_all
  show arr2: "equiv (snd A) {(x, y). R x y} \<Longrightarrow> Obj' A \<Longrightarrow> Arr' (quotient_section A R)"
    apply (subst quot_sec_arr)
    by simp_all
  show "equiv (snd A) {(x, y). R x y} \<Longrightarrow>
    Obj' A \<Longrightarrow> fst (snd (quotient_proj A R)) = snd (snd (quotient_section A R))"
    by simp
  assume "Obj' A"
  then have H: "Obj' (quotient_by_equiv_rel A R)" unfolding Obj'_def apply simp
  proof
    show "fst A \<in> snd A \<Longrightarrow> fst A \<in> snd A" by simp
    show "(SOME b. R (fst A) b \<and> b \<in> snd A) = (SOME b. R (fst A) b \<and> b \<in> snd A)" by simp
  qed
  have "(\<And>Obj Arr Dom Cod Id Comp a.
        classical_category Obj Arr Dom Cod Id Comp \<Longrightarrow> Obj a \<Longrightarrow> Arr (Id a))"
    by (simp add: classical_category.Arr_Id)
  then have "\<And>a. classical_category Obj' Arr' (\<lambda>t. fst (snd t)) (\<lambda>t. snd (snd t)) Id' (\<cdot>)
             \<Longrightarrow> Obj' a \<Longrightarrow> Arr' (Id' a)" using ccpf by fastforce
  then have "\<And>a. Obj' a \<Longrightarrow> Arr' (Id' a)" by (simp add: ccpf)
  then have "Obj' (quotient_by_equiv_rel A R) \<Longrightarrow> Arr' (Id' (quotient_by_equiv_rel A R))" by simp
  from this and H show "Arr' (Id' (quotient_by_equiv_rel A R))" by simp
  show "equiv (snd A) {(x, y). R x y} \<Longrightarrow>
    Obj' A \<Longrightarrow>
    fst (snd (quotient_proj A R \<cdot> quotient_section A R)) =
    fst (snd (Id' (quotient_by_equiv_rel A R)))"
    apply (subst dom_comp)
    using arr2 apply simp
    using arr1 apply simp
    apply simp
    by (simp add: Id'_def)
  show "equiv (snd A) {(x, y). R x y} \<Longrightarrow>
    Obj' A \<Longrightarrow>
    snd (snd (quotient_proj A R \<cdot> quotient_section A R)) =
    snd (snd (Id' (quotient_by_equiv_rel A R)))"
    apply (subst cod_comp)
    using arr2 apply simp
    using arr1 apply simp
    apply simp
    by (simp add: Id'_def)
  fix x
  have eq: "equiv (snd A) {(x, y). R x y} \<Longrightarrow>
         Obj' A \<Longrightarrow> fst (snd (quotient_section A R)) = fst (snd (quotient_proj A R \<cdot> quotient_section A R))" 
    apply (subst dom_comp)
    using arr2 apply simp
    using arr1 apply simp
     apply simp
    by simp
  show "equiv (snd A) {(x, y). R x y} \<Longrightarrow>
         Obj' A \<Longrightarrow>
         x \<in> snd (fst (snd (quotient_proj A R \<cdot> quotient_section A R))) \<Longrightarrow>
         fst (quotient_proj A R \<cdot> quotient_section A R) x =
         fst (Id' (quotient_by_equiv_rel A R)) x"
    apply (subst fun_comp_char)
    using arr1 apply simp
    using arr2 apply simp
      apply simp
  proof-
    assume A1: "equiv (snd A) {(x, y). R x y}"
    assume "Obj' A"
    then have A2: "fst A \<in> snd A" unfolding Obj'_def by simp
    assume "x \<in> snd (fst (snd (quotient_proj A R \<cdot> quotient_section A R)))"
    then show A3: "x \<in> snd (fst (snd (quotient_section A R)))"
      apply (subst eq)
      by (simp_all add: A1 \<open>Obj' A\<close>) 
    have "x = Eps (\<lambda>b. R (fst A) b \<and> b \<in> (snd A)) \<or>
          x \<noteq> Eps (\<lambda>b. R (fst A) b \<and> b \<in> (snd A))" by auto
    then
    show "fst (quotient_proj A R) (fst (quotient_section A R) x) =
    fst (Id' (quotient_by_equiv_rel A R)) x"
    proof
      have "\<exists>a\<in>snd A. (SOME b. R (fst A) b \<and> b \<in> snd A) = (SOME b. R a b \<and> b \<in> snd A)"
      proof
        show "fst A \<in> snd A" using A2.
        show "(SOME b. R (fst A) b \<and> b \<in> snd A) = (SOME b. R (fst A) b \<and> b \<in> snd A)" by simp
      qed
      then show "x = (SOME b. R (fst A) b \<and> b \<in> snd A) \<Longrightarrow>
    fst (quotient_proj A R) (fst (quotient_section A R) x) =
    fst (Id' (quotient_by_equiv_rel A R)) x"
        unfolding Id'_def by (simp add: A2 A3)
    next
      assume "x \<noteq> (SOME b. R (fst A) b \<and> b \<in> snd A)"
      from A3 have "x \<in> {i. \<exists>a\<in>snd A. i = (SOME b. R a b \<and> b \<in> snd A)}" by simp
      then have ex_a: "\<exists>a \<in> snd A. x = (SOME b. R a b \<and> b \<in> snd A)" by simp
      then obtain a where a_def: "a \<in> snd A \<and> x = (SOME b. R a b \<and> b \<in> snd A)" by blast


      obtain P where P_def: "P = (\<lambda>b. R a b \<and> b \<in> snd A)" by simp
      have "R a a \<and> a \<in> snd A"
        apply (simp add: a_def)
        using \<open>equiv (snd A) {(x,y). R x y}\<close> unfolding equiv_def refl_on_def using a_def by blast
      then have "\<exists>b. R a b \<and> b \<in> snd A" by auto
      then have "\<exists>b. P b" by (simp add: P_def)
      then have "P (SOME b. P b)" by (meson someI_ex)
      then have H: "R a (SOME b. R a b \<and> b \<in> snd A) \<and> (SOME b. R a b \<and> b \<in> snd A) \<in> snd A"
        by (simp add: P_def)
      from H and a_def have "R a x" by simp
      from H and a_def have "x \<in> snd A" by simp


      obtain Q where Q_def: "Q = {(x,y). R x y \<and> y \<in> snd A}" by simp
      have eq: "\<And>x y. (R x y \<and> y \<in> snd A) = (cur_rel Q x y)" by (simp add: Q_def)
     
      have x_eq: "x = (SOME b. R x b \<and> b \<in> snd A)"
        apply (subst a_def)
        apply (subst eq)
        apply (subst eq)
        apply (subst quotient_lemma)
        unfolding sym_def trans_def Q_def
        apply auto
        using \<open>equiv (snd A) {(x,y). R x y}\<close> unfolding equiv_def sym_def
            apply simp
        using \<open>equiv (snd A) {(x,y). R x y}\<close> unfolding equiv_def refl_on_def
           apply blast
      proof-
        fix p q r
        assume "R p q"
        then have r1: "(p, q) \<in> {(x,y). R x y}" by simp
        assume "q \<in> snd A"
        assume "R q r"
        then have r2: "(q, r) \<in> {(x,y). R x y}" by simp
        assume "r \<in> snd A"
        have "(\<forall>x y z.
        (x, y) \<in> {(x, y). R x y} \<longrightarrow> (y, z) \<in> {(x, y). R x y} \<longrightarrow> (x, z) \<in> {(x, y). R x y})"
          using \<open>equiv (snd A) {(x,y). R x y}\<close> unfolding equiv_def trans_def
          by blast
        from this and r1 and r2 have "(p, r) \<in> {(x,y). R x y}" by blast
        then show "R p r" by simp
      next
        show "R a x" using \<open>R a x\<close>.
        show "x \<in> snd A" using \<open>x \<in> snd A\<close>.
      qed
      from x_eq show "x \<noteq> (SOME b. R (fst A) b \<and> b \<in> snd A) \<Longrightarrow>
    fst (quotient_proj A R) (fst (quotient_section A R) x) =
    fst (Id' (quotient_by_equiv_rel A R)) x"
        unfolding Id'_def by (simp add: A2 A3 ex_a \<open>x \<in> snd A\<close>)
    qed
  qed
qed
          

lemma quotient_UP_existence : assumes equiv: "equiv (snd A) {(x,y). R x y}"
   and  cocone : "Arr' g \<and> Dom' g = A \<and> Cod' g = Z \<and> (\<forall>x y. R x y \<longrightarrow> fst g x = fst g y)"
  and "Obj' A" 
  shows "Arr' (g \<cdot> quotient_section A R) \<and>
    fst (snd (g \<cdot> quotient_section A R)) = quotient_by_equiv_rel A R \<and>
    snd (snd (g \<cdot> quotient_section A R)) = Z \<and>
    (g \<cdot> quotient_section A R) \<cdot> quotient_proj A R = g"
proof-
  show "Arr' (g \<cdot> quotient_section A R) \<and>
    fst (snd (g \<cdot> quotient_section A R)) = quotient_by_equiv_rel A R \<and>
    snd (snd (g \<cdot> quotient_section A R)) = Z \<and>
    (g \<cdot> quotient_section A R) \<cdot> quotient_proj A R = g"
    apply safe
  proof-
    from cocone have arr_g: "Arr' g" by simp
    have arr_sec: "Arr' (quotient_section A R)"
      using quot_sec_arr [OF equiv \<open>Obj' A\<close>].
    have seq: "fst (snd g) = snd (snd (quotient_section A R))" 
      using cocone by simp
    show "Arr' (g \<cdot> quotient_section A R)"
      using comp_arr [OF arr_g arr_sec seq].
    show "fst (snd (g \<cdot> quotient_section A R)) = quotient_by_equiv_rel A R"
      apply (subst dom_comp [OF arr_sec arr_g reverse_equality [OF seq]])
      by simp
    show "snd (snd (g \<cdot> quotient_section A R)) = Z"
      apply (subst cod_comp [OF arr_sec arr_g reverse_equality [OF seq]])
      using cocone by simp
    show "(g \<cdot> quotient_section A R) \<cdot> quotient_proj A R = g"
      apply (subst classical_category.Comp_assoc [OF ccpf
             quot_proj_arr [OF \<open>Obj' A\<close>] arr_sec arr_g])
        apply simp
      using cocone apply simp
      apply (rule_tac comp_eq_char)
      using arr_g apply simp
           apply (rule_tac comp_arr [OF arr_sec quot_proj_arr [OF \<open>Obj' A\<close>]])
           apply simp
      using arr_g apply simp
         apply (subst dom_comp [OF quot_proj_arr [OF \<open>Obj' A\<close>] arr_sec])
          apply simp
      using cocone apply simp
        apply simp
       apply (subst cod_comp [OF quot_proj_arr [OF \<open>Obj' A\<close>] arr_sec])
        apply simp
      using cocone apply simp
    proof-
      fix x
      assume "x \<in> snd (fst (snd (quotient_section A R \<cdot> quotient_proj A R)))"
      then have "x \<in> snd (fst (snd (quotient_proj A R)))"
        using dom_comp [OF quot_proj_arr [OF \<open>Obj' A\<close>] arr_sec] by simp
      then have "x \<in> snd A" by simp
      from cocone have gReq: "(\<And> x y. R x y \<Longrightarrow> fst g x = fst g y)" by simp
      define s where "s = quotient_section A R"
      define pi where "pi = quotient_proj A R"
      have "Arr' s" unfolding s_def using arr_sec.
      have "Arr' pi" unfolding pi_def using quot_proj_arr [OF \<open>Obj' A\<close>].
      have seq: "snd (snd pi) = fst (snd s)" unfolding pi_def s_def by simp
      from \<open>x \<in> snd A\<close> have x_in_pi: "x \<in> snd (fst (snd pi))" unfolding pi_def by simp
      have "fst g x = fst g (fst (s \<cdot> pi) x)"
        apply (rule_tac gReq)
        unfolding Comp'_def
        using \<open>Arr' pi\<close> \<open>Arr' s\<close> seq x_in_pi apply simp
        apply (subst pi_def)
        using \<open>x \<in> snd A\<close> apply simp
      proof-
        have "R x (fst A) \<or> \<not> (R x (fst A))" by auto
        then show "R x (fst s (SOME b. R x b \<and> b \<in> snd A))"
        proof
          assume "R x (fst A)"
          have "(\<forall>x y z. (x, y) \<in> {(x, y). R x y} \<longrightarrow> (y, z) \<in> {(x, y). R x y} \<longrightarrow> (x, z) \<in> {(x, y). R x y})"
            using equiv unfolding equiv_def trans_def by blast
          then have trans: "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z" by blast
          have "(\<forall>x y. (x, y) \<in> {(x, y). R x y} \<longrightarrow> (y, x) \<in> {(x, y). R x y})"
            using equiv unfolding equiv_def sym_def by blast
          then have sym: "\<And>x y. R x y \<Longrightarrow> R y x" by blast
          have "\<And>b. ((R x b \<and> b \<in> snd A) = (R (fst A) b \<and> b \<in> snd A))"
          proof-
            fix b
            show "(R x b \<and> b \<in> snd A) = (R (fst A) b \<and> b \<in> snd A)"
              apply auto
               apply (rule_tac trans)
                apply (rule_tac sym [OF \<open>R x (fst A)\<close>])
               apply simp
              apply (rule_tac trans [OF \<open>R x (fst A)\<close>])
              by simp
          qed 
          then have eq: "(SOME b. R x b \<and> b \<in> snd A) = (SOME b. R (fst A) b \<and> b \<in> snd A)" by simp
          have ex_a: "\<exists>a\<in>snd A. (SOME b. R (fst A) b \<and> b \<in> snd A) = (SOME b. R a b \<and> b \<in> snd A)"
          proof
            show "(SOME b. R (fst A) b \<and> b \<in> snd A) = (SOME b. R (fst A) b \<and> b \<in> snd A)" by simp
            show "fst A \<in> snd A" using \<open>Obj' A\<close> unfolding Obj'_def.
          qed
          from eq show "R x (fst s (SOME b. R x b \<and> b \<in> snd A))"
            apply simp
            unfolding s_def
            using \<open>Obj' A\<close> unfolding Obj'_def
            using ex_a apply simp
            using \<open>R x (fst A)\<close>.
        next
          assume nR: "\<not> R x (fst A)"

          have R_some: "\<And>x.  x \<in> snd A \<Longrightarrow> R x (SOME b. R x b \<and> b \<in> snd A)"
          proof-
            fix x
            assume "x \<in> snd A" 
            have "R x x \<and> x \<in> snd A"
              using equiv unfolding equiv_def refl_on_def'
              using \<open>x \<in> snd A\<close> by simp
            then have "\<exists>b. R x b \<and> b \<in> snd A"
              apply (rule_tac exI)
              by simp
            show "R x (SOME b. R x b \<and> b \<in> snd A)"
              using someI_ex [OF \<open>\<exists>b. R x b \<and> b \<in> snd A\<close>] by blast
          qed
          have "R (fst A) (SOME b. R (fst A) b \<and> b \<in> snd A)"
            using R_some \<open>Obj' A\<close> unfolding Obj'_def by simp
          then have "R (SOME b. R (fst A) b \<and> b \<in> snd A) (fst A)"
            using equiv
            unfolding equiv_def sym_def by blast
          have "\<not> R x (SOME b. R (fst A) b \<and> b \<in> snd A)"
            apply auto
          proof-
            assume "R x (SOME b. R (fst A) b \<and> b \<in> snd A)"
            from this and \<open>R (SOME b. R (fst A) b \<and> b \<in> snd A) (fst A)\<close>
            have "R x (fst A)"
              using equiv
              unfolding equiv_def trans_def by blast
            then show "False"
              using \<open>\<not> R x (fst A)\<close> by simp
          qed
          then have n_some: "(SOME b. R x b \<and> b \<in> snd A) \<noteq> (SOME b. R (fst A) b \<and> b \<in> snd A)"
            using R_some [OF \<open>x \<in> snd A\<close>] by auto
          have ex_a : "\<exists>a\<in>snd A. (SOME b. R x b \<and> b \<in> snd A) = (SOME b. R a b \<and> b \<in> snd A)"
          proof
            show "(SOME b. R x b \<and> b \<in> snd A) = (SOME b. R x b \<and> b \<in> snd A)" by simp
            show "x \<in> snd A" using \<open>x \<in> snd A\<close>.
          qed
          from nR show "R x (fst s (SOME b. R x b \<and> b \<in> snd A))"
            unfolding s_def
            using \<open>Obj' A\<close> unfolding Obj'_def
            using n_some ex_a apply simp
            using R_some [OF \<open>x \<in> snd A\<close>].
        qed
      qed
      then show "fst g (fst (quotient_section A R \<cdot> quotient_proj A R) x) = fst g x"
        unfolding pi_def s_def by simp
    qed
  qed
qed

lemma quotient_UP_uniqueness : assumes equiv: "equiv (snd A) {(x,y). R x y}"
   and  cocone : "Arr' g \<and> Dom' g = A \<and> Cod' g = Z \<and> (\<forall>x y. R x y \<longrightarrow> fst g x = fst g y)"
  and "Obj' A" 
  shows "\<And>f. Arr' f \<and>
         fst (snd f) = quotient_by_equiv_rel A R \<and> snd (snd f) = Z \<and> f \<cdot> quotient_proj A R = g \<Longrightarrow>
         f = g \<cdot> quotient_section A R"
proof-
  fix f
  assume f_def: "Arr' f \<and>
         fst (snd f) = quotient_by_equiv_rel A R \<and> snd (snd f) = Z \<and> f \<cdot> quotient_proj A R = g"
  then have "(f \<cdot> quotient_proj A R) \<cdot> quotient_section A R = g \<cdot> quotient_section A R" by simp
  then have "f \<cdot> (quotient_proj A R \<cdot> quotient_section A R) = g \<cdot> quotient_section A R"
    apply (subst reverse_equality [OF classical_category.Comp_assoc[OF ccpf]])
    using quot_sec_arr [OF equiv \<open>Obj' A\<close>] apply simp
    using quot_proj_arr [OF \<open>Obj' A\<close>] apply simp
    using f_def apply simp
      apply simp
    using f_def apply simp
    by simp
  then have "f \<cdot> Id' (quotient_by_equiv_rel A R) = g \<cdot> quotient_section A R"
    apply (subst reverse_equality [OF proj_sec_id [OF equiv \<open>Obj' A\<close>]]) 
    by simp
  then show "f = g \<cdot> quotient_section A R"
    apply (subst reverse_equality [OF classical_category.Comp_Arr_Id_Dom [OF ccpf]])
    using f_def apply simp
    using f_def by simp
qed


lemma quotient_UP : assumes equiv: "equiv (snd A) {(x,y). R x y}"
   and  cocone : "Arr' g \<and> Dom' g = A \<and> Cod' g = Z \<and> (\<forall>x y. R x y \<longrightarrow> fst g x = fst g y)"
  and "Obj' A" 
  shows "\<exists>!f. Arr' f \<and> Dom' f = quotient_by_equiv_rel A R \<and> Cod' f = Z \<and>
         f \<cdot> (quotient_proj A R) = g"
proof
  show "Arr' (g \<cdot> quotient_section A R) \<and>
    fst (snd (g \<cdot> quotient_section A R)) = quotient_by_equiv_rel A R \<and>
    snd (snd (g \<cdot> quotient_section A R)) = Z \<and>
    (g \<cdot> quotient_section A R) \<cdot> quotient_proj A R = g"
    using quotient_UP_existence[OF equiv cocone \<open>Obj' A\<close>].
  show "\<And>f. Arr' f \<and>
         fst (snd f) = quotient_by_equiv_rel A R \<and> snd (snd f) = Z \<and> f \<cdot> quotient_proj A R = g \<Longrightarrow>
         f = g \<cdot> quotient_section A R"
    using quotient_UP_uniqueness[OF equiv cocone \<open>Obj' A\<close>].
qed







       
fun subset_eq_relation:: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set" where
  "subset_eq_relation A B = {(a,b). a \<in> A \<and> b \<in> A \<and> (a = b \<or> (a \<in> B \<and> b \<in> B))}"

lemma subst_eq_rel_equiv: "equiv A (subset_eq_relation A B)"
  unfolding equiv_def
  apply auto
proof-
  show "refl_on A {(a, b). a \<in> A \<and> b \<in> A \<and> (a = b \<or> a \<in> B \<and> b \<in> B)}"
  proof
    show "{(a, b). a \<in> A \<and> b \<in> A \<and> (a = b \<or> a \<in> B \<and> b \<in> B)} \<subseteq> A \<times> A" by auto
    show "\<And>x. x \<in> A \<Longrightarrow> (x, x) \<in> {(a, b). a \<in> A \<and> b \<in> A \<and> (a = b \<or> a \<in> B \<and> b \<in> B)}" 
      by simp
  qed
  show "sym {(a, b). a \<in> A \<and> b \<in> A \<and> (a = b \<or> a \<in> B \<and> b \<in> B)}"
    unfolding sym_def by auto
  show "trans {(a, b). a \<in> A \<and> b \<in> A \<and> (a = b \<or> a \<in> B \<and> b \<in> B)}"
    unfolding trans_def by auto
qed

fun quotient_by_subset:: "'a pointed_set \<Rightarrow> 'a pointed_set \<Rightarrow> 'a pointed_set" where
  "quotient_by_subset A B = quotient_by_equiv_rel A (cur_rel (subset_eq_relation (snd A) (snd B)))"

fun quot_subs_proj :: "'a pointed_set \<Rightarrow> 'a pointed_set \<Rightarrow> 'a parr" where
  "quot_subs_proj A B = quotient_proj A (cur_rel (subset_eq_relation (snd A) (snd B)))"

fun quot_subs_section :: "'a pointed_set \<Rightarrow> 'a pointed_set \<Rightarrow> 'a parr" where
  "quot_subs_section A B = quotient_section A (cur_rel (subset_eq_relation (snd A) (snd B)))"


lemma quotient_is_subset : "equiv (snd A) {(x, y). R x y} \<Longrightarrow> 
         snd (quotient_by_equiv_rel A R) \<subseteq> snd A"
  apply auto
proof-
  fix a
  assume equiv_R: "equiv (snd A) {(x, y). R x y}"
  assume "a \<in> snd A"
  from this and equiv_R have "R a a"
    unfolding equiv_def refl_on_def by auto
  then have ex_b: "\<exists> b. R a b \<and> b \<in> snd A"
    apply (rule_tac exI)
    using \<open>a \<in> snd A\<close> by simp
  then show "(SOME b. R a b \<and> b \<in> snd A) \<in> snd A"
    using someI_ex [OF ex_b] by simp
qed

lemma subset_quotient_is_subset : "snd (quotient_by_subset A B) \<subseteq> snd A"
  unfolding quotient_by_subset.simps
  apply (rule_tac quotient_is_subset)
  using subst_eq_rel_equiv by auto




subsection "Some colimits"

definition pointed_list :: "'a LC pointed_set \<Rightarrow> 'a LC list \<Rightarrow> bool" where
  "pointed_list X xs \<equiv> xs \<noteq> [] \<and> get xs 0 = fst X \<and> (\<forall>n<length xs. get xs n \<in> snd X)"

fun raw_coproductOverPointedLists :: "'a LC pointed_set \<Rightarrow> ('a LC list \<Rightarrow> 'a LC pointed_set) \<Rightarrow> 'a LC pointed_set" where
  "raw_coproductOverPointedLists X A = (Join([ fst (A [fst X]) ,fst X])  ,
           {x. \<exists>xs a. x = Join (a#xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs})" 

fun basepoints_in_raw_coproduct :: "'a LC pointed_set \<Rightarrow> ('a LC list \<Rightarrow> 'a LC pointed_set) \<Rightarrow> 'a LC pointed_set" where
  "basepoints_in_raw_coproduct X A = (Join([ fst (A [fst X]) ,fst X])  ,
           {x. \<exists>xs. x = Join (fst (A xs)#xs) \<and> pointed_list X xs})"

definition coproductOverPointedLists :: "'a LC pointed_set \<Rightarrow> ('a LC list \<Rightarrow> 'a LC pointed_set) \<Rightarrow> 'a LC pointed_set" where
  "coproductOverPointedLists X A \<equiv> quotient_by_subset (raw_coproductOverPointedLists X A)
                                    (basepoints_in_raw_coproduct X A)"

fun raw_cop_proj :: "'a LC pointed_set \<Rightarrow> ('a LC list \<Rightarrow> 'a LC pointed_set) \<Rightarrow> 'a LC parr" where
  "raw_cop_proj X A = quot_subs_proj (raw_coproductOverPointedLists X A)
                                    (basepoints_in_raw_coproduct X A)"

fun raw_cop_section :: "'a LC pointed_set \<Rightarrow> ('a LC list \<Rightarrow> 'a LC pointed_set) \<Rightarrow> 'a LC parr" where
  "raw_cop_section X A = quot_subs_section (raw_coproductOverPointedLists X A)
                                    (basepoints_in_raw_coproduct X A)"

definition cop_list_inclusion :: "'a LC pointed_set \<Rightarrow> ('a LC list \<Rightarrow> 'a LC pointed_set) \<Rightarrow> 'a LC list \<Rightarrow> 'a LC parr" where
  "cop_list_inclusion X A xs \<equiv> ((\<lambda>a \<in> snd (A xs). fst (raw_cop_proj X A) (Join(a # xs))), 
                   (A xs, coproductOverPointedLists X A))"

fun cop_list_index :: "'a LC \<Rightarrow> 'a LC list" where
  "cop_list_index (Join (a # as)) = as" |
  "cop_list_index other = undefined"

fun cop_list_value :: "'a LC \<Rightarrow> 'a LC" where
  "cop_list_value (Join (a # as)) = a" |
  "cop_list_value other = undefined"

definition coprod_list_UP_map :: "'a LC pointed_set \<Rightarrow> ('a LC list \<Rightarrow> 'a LC parr) \<Rightarrow> 'a LC pointed_set \<Rightarrow> 'a LC parr" where
  "coprod_list_UP_map X cocone Z \<equiv> ((\<lambda>a \<in> snd (coproductOverPointedLists X (\<lambda>xs. Dom' (cocone xs))).
               fst (cocone (cop_list_index a)) (cop_list_value a)),
              (coproductOverPointedLists X (\<lambda>xs. Dom' (cocone xs)), Z))"

lemma baselist_pointed: "Obj' X \<Longrightarrow> pointed_list X [fst X]"
  unfolding pointed_list_def Obj'_def by simp


lemma cop_list_obj : "(\<forall>xs. pointed_list X xs \<longrightarrow> Obj' (A xs)) \<Longrightarrow> Obj' X \<Longrightarrow> Obj' (coproductOverPointedLists X A)"
  unfolding coproductOverPointedLists_def Obj'_def
  apply simp
  apply (rule_tac exI)
  apply (rule_tac conjI)
   apply (rule_tac exI)
proof
  assume "(\<forall>xs. pointed_list X xs \<longrightarrow> fst (A xs) \<in> snd (A xs))"
  then have A_obj: "(\<And> xs. pointed_list X xs \<Longrightarrow> fst (A xs) \<in> snd (A xs))" by auto
  assume X_obj: "fst X \<in> snd X" 
  show "(Join [fst (A [fst X]), fst X]) = Join ((fst (A [fst X])) # [fst X]) \<and>
        fst (A [fst X]) \<in> snd (A [fst X]) \<and>
         pointed_list X [fst X]"
    apply auto
     apply (rule_tac A_obj)
    unfolding pointed_list_def apply auto
    using X_obj by simp_all
  have propeq: "\<And>b. ((fst (A [fst X]) \<in> snd (A [fst X]) \<and>
        pointed_list X [fst X] \<and>
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<and>
        (Join [fst (A [fst X]), fst X] = b \<or>
         pointed_list X [fst X] \<and> (\<exists>xs. b = Join (fst (A xs) # xs) \<and> pointed_list X xs)) \<and>
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs)) = 
        ((\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<and>
        (Join [fst (A [fst X]), fst X] = b \<or>
         (\<exists>xs. Join [fst (A [fst X]), fst X] = Join (fst (A xs) # xs) \<and> pointed_list X xs) \<and>
         (\<exists>xs. b = Join (fst (A xs) # xs) \<and> pointed_list X xs)) \<and>
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs)))"
    apply auto
    using A_obj[OF baselist_pointed]
    unfolding Obj'_def using X_obj by simp
  show " (SOME b.
        fst (A [fst X]) \<in> snd (A [fst X]) \<and>
        pointed_list X [fst X] \<and>
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<and>
        (Join [fst (A [fst X]), fst X] = b \<or>
         pointed_list X [fst X] \<and> (\<exists>xs. b = Join (fst (A xs) # xs) \<and> pointed_list X xs)) \<and>
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs)) =
    (SOME b.
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<and>
        (Join [fst (A [fst X]), fst X] = b \<or>
         (\<exists>xs. Join [fst (A [fst X]), fst X] = Join (fst (A xs) # xs) \<and> pointed_list X xs) \<and>
         (\<exists>xs. b = Join (fst (A xs) # xs) \<and> pointed_list X xs)) \<and>
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs))"
    apply (subst propeq)
    by simp
qed
    



lemma cop_list_inclusion_arr : "(\<forall>xs. pointed_list X xs \<longrightarrow> Obj' (A xs)) \<Longrightarrow> Obj' X \<Longrightarrow> pointed_list X xs 
       \<Longrightarrow> Arr' (cop_list_inclusion X A xs)"
  unfolding Arr'_def apply safe
proof-
  assume "pointed_list X xs"
  assume "Obj' X" 
  assume A_obj: "(\<forall>xs. pointed_list X xs \<longrightarrow> Obj' (A xs))"
  then have "Obj' (A xs)" using \<open>pointed_list X xs\<close> by simp
  then show "setcat.Arr (forget (cop_list_inclusion X A xs))"
    unfolding setcat.Arr_def apply auto
     apply (simp add: cop_list_inclusion_def)
  proof-
    fix x
    assume "x \<in> snd (Dom' (cop_list_inclusion X A xs))"
    then have "x \<in> snd (A xs)"
      unfolding cop_list_inclusion_def by simp
    have "x = fst (A xs) \<or> x \<noteq> fst (A xs)" by auto
    then show "fst (cop_list_inclusion X A xs) x \<in> snd (snd (snd (cop_list_inclusion X A xs)))"
    proof
      assume "x \<noteq> fst (A xs)"
      have some_eq: "(SOME b.
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<and>
        (Join (x # xs) = b \<or>
         x = fst (A xs) \<and> (\<exists>xs. b = Join (fst (A xs) # xs) \<and> pointed_list X xs)) \<and>
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs)) = Join (x # xs)"
      proof
        show "(\<exists>xsa a. Join (x # xs) = Join (a # xsa) \<and> a \<in> snd (A xsa) \<and> pointed_list X xsa) \<and>
    (Join (x # xs) = Join (x # xs) \<or>
     x = fst (A xs) \<and> (\<exists>xsa. Join (x # xs) = Join (fst (A xsa) # xsa) \<and> pointed_list X xsa)) \<and>
    (\<exists>xsa a. Join (x # xs) = Join (a # xsa) \<and> a \<in> snd (A xsa) \<and> pointed_list X xsa)"
          using \<open>x \<in> snd (A xs)\<close> \<open>pointed_list X xs\<close> by auto
        fix b
        show "(\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<and>
         (Join (x # xs) = b \<or>
          x = fst (A xs) \<and> (\<exists>xs. b = Join (fst (A xs) # xs) \<and> pointed_list X xs)) \<and>
         (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<Longrightarrow>
         b = Join (x # xs)"
          using \<open>x \<noteq> fst (A xs)\<close> by simp
      qed
      show "fst (cop_list_inclusion X A xs) x \<in> snd (snd (snd (cop_list_inclusion X A xs)))"
        unfolding cop_list_inclusion_def 
        using \<open>pointed_list X xs\<close> \<open>x \<in> snd (A xs)\<close> apply simp
        apply (subst some_eq)
        unfolding coproductOverPointedLists_def apply simp
        apply (rule_tac exI)
        apply auto
        using some_eq by simp
    next
      assume "x = fst (A xs)"
      show "fst (cop_list_inclusion X A xs) x \<in> snd (snd (snd (cop_list_inclusion X A xs)))"
        apply (subst \<open>x = fst (A xs)\<close>)
        unfolding cop_list_inclusion_def
        using \<open>pointed_list X xs\<close> \<open>Obj' (A xs)\<close>
        unfolding Obj'_def apply simp
        unfolding coproductOverPointedLists_def apply simp
        apply (rule_tac exI)
        by auto
    qed
  qed
  show "Obj' (fst (snd (cop_list_inclusion X A xs)))"
    unfolding cop_list_inclusion_def 
    using \<open>Obj' (A xs)\<close> by simp
  show "Obj' (snd (snd (cop_list_inclusion X A xs)))"
    unfolding cop_list_inclusion_def apply simp
    using cop_list_obj [OF A_obj \<open>Obj' X\<close>].
  have "fst (A [fst X]) \<in> snd (A [fst X])"
    using A_obj unfolding Obj'_def
    using baselist_pointed [OF \<open>Obj' X\<close>] by simp
  have prop_eq : "\<And>b. (((\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<and>
        (Join (fst (A xs) # xs) = b \<or> (\<exists>xs. b = Join (fst (A xs) # xs) \<and> pointed_list X xs)) \<and>
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs)) =
        (fst (A [fst X]) \<in> snd (A [fst X]) \<and>
        pointed_list X [fst X] \<and>
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<and>
        (Join [fst (A [fst X]), fst X] = b \<or>
         pointed_list X [fst X] \<and> (\<exists>xs. b = Join (fst (A xs) # xs) \<and> pointed_list X xs)) \<and>
        (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs)))"
    using baselist_pointed [OF \<open>Obj' X\<close>]
          \<open>fst (A [fst X]) \<in> snd (A [fst X])\<close> by auto
        
  show "fst (cop_list_inclusion X A xs) (fst (fst (snd (cop_list_inclusion X A xs)))) =
    fst (snd (snd (cop_list_inclusion X A xs)))"
    unfolding cop_list_inclusion_def 
    using \<open>pointed_list X xs\<close> \<open>Obj' (A xs)\<close>
    unfolding Obj'_def apply simp
    unfolding coproductOverPointedLists_def apply simp
    apply (subst prop_eq) 
    by simp
qed



    
lemma coprod_list_UP_map_arr : assumes 
      cocone: "(\<forall>xs. pointed_list X xs \<longrightarrow> Arr' (cocone xs) \<and>
              Cod' (cocone xs) = Z)"
          "Obj' X"
  shows "Arr' (coprod_list_UP_map X cocone Z)"
  unfolding Arr'_def
  apply safe
proof-
  have "Obj' Z"
    using cocone baselist_pointed [OF \<open>Obj' X\<close>]
    unfolding Arr'_def by auto
  show "setcat.Arr (forget (coprod_list_UP_map X cocone Z))"
    unfolding setcat.Arr_def apply auto
    unfolding coprod_list_UP_map_def apply auto
  proof-
    fix x
    assume "x \<in> snd (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))))"
    then have "x \<in> snd (raw_coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))))"
      apply (rule_tac subsetD [OF subset_quotient_is_subset])
      unfolding coproductOverPointedLists_def.
    then obtain a xs where a_xs_def: "x = Join (a # xs) \<and>
          a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs" by auto
    have "Arr' (cocone xs)" 
      using cocone a_xs_def by simp
    then have "fst (cocone xs) \<in> (snd (Dom' (cocone xs)) \<rightarrow> snd Z)"
      unfolding Arr'_def setcat.Arr_def
      using cocone a_xs_def by simp
    then show "fst (cocone (cop_list_index x)) (cop_list_value x) \<in> snd Z"
      using a_xs_def by auto
  qed
  have cop_obj: "Obj' (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))))"
    apply (rule_tac cop_list_obj)
    using cocone unfolding Arr'_def apply simp
    using \<open>Obj' X\<close>.
  then show "Obj' (fst (snd (coprod_list_UP_map X cocone Z)))"
    unfolding coprod_list_UP_map_def by simp
  show "Obj' (snd (snd (coprod_list_UP_map X cocone Z)))"
    unfolding coprod_list_UP_map_def apply simp
    using \<open>Obj' Z\<close>.
  show "fst (coprod_list_UP_map X cocone Z)
     (fst (fst (snd (coprod_list_UP_map X cocone Z)))) =
    fst (snd (snd (coprod_list_UP_map X cocone Z)))"
    unfolding coprod_list_UP_map_def
    using cop_obj unfolding Obj'_def apply simp
  proof-
    define P where "P =(\<lambda>b. fst (fst (snd (cocone [fst X]))) \<in> snd (fst (snd (cocone [fst X]))) \<and>
                pointed_list X [fst X] \<and>
                (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs) \<and>
                (Join [fst (fst (snd (cocone [fst X]))), fst X] = b \<or>
                 pointed_list X [fst X] \<and>
                 (\<exists>xs. b = Join (fst (fst (snd (cocone xs))) # xs) \<and> pointed_list X xs)) \<and>
                (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs))"
    have "P (SOME b. P b)"
      apply (rule_tac someI_ex)
      unfolding P_def
      apply (rule_tac exI)
      apply auto
      using cocone baselist_pointed [OF \<open>Obj' X\<close>]
      unfolding Arr'_def Obj'_def by simp_all
    then obtain a xs where a_xs_def: "(SOME b. P b) = Join( a # xs) \<and>
                    a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs" using P_def by auto
    have "a \<in> snd (Dom' (cocone xs))"
      by (simp add: a_xs_def) 
    have "fst (cocone xs) a = fst Z"
      using cocone a_xs_def
      unfolding Arr'_def setcat.Arr_def
      using P_def \<open>P (SOME b. P b)\<close> by auto
    then show "fst (cocone
          (cop_list_index
            (fst (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs)))))))
     (cop_list_value (fst (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs)))))) =
    fst Z"
      unfolding coproductOverPointedLists_def apply simp
      using a_xs_def P_def by simp
  qed
qed




lemma x_in_cop_list_char: assumes A_obj: "\<forall>xs. pointed_list X xs \<longrightarrow> Obj' (A xs)"
                             "Obj' X" 
                           shows  "\<And>x. x \<in> snd (coproductOverPointedLists X A) \<Longrightarrow>
           pointed_list X (cop_list_index x) \<and> cop_list_value x \<in> snd (A (cop_list_index x)) \<and>
       fst (cop_list_inclusion X A (cop_list_index x)) (cop_list_value x) = x"
proof-
  fix x
  assume x_in_cop: "x \<in> snd (coproductOverPointedLists X A)"

  from x_in_cop obtain x' where x'_def: "(\<exists>xs aa. x' = Join (aa # xs) \<and> aa \<in> snd (A xs) \<and> pointed_list X xs) \<and>
        x =
        (SOME b.
            (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<and>
            (x' = b \<or>
             (\<exists>xs. x' = Join (fst (A xs) # xs) \<and> pointed_list X xs) \<and>
             (\<exists>xs. b = Join (fst (A xs) # xs) \<and> pointed_list X xs)) \<and>
            (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs))"
    unfolding coproductOverPointedLists_def by auto
  define P where "P = (\<lambda>b. (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs) \<and>
            (x' = b \<or>
             (\<exists>xs. x' = Join (fst (A xs) # xs) \<and> pointed_list X xs) \<and>
             (\<exists>xs. b = Join (fst (A xs) # xs) \<and> pointed_list X xs)) \<and>
            (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (A xs) \<and> pointed_list X xs))"
  
  have "\<exists>x. P x"
    unfolding P_def
    apply (rule_tac exI)
    apply auto
    using x'_def by simp_all
  from x'_def have "x = (SOME b. P b)"
    unfolding P_def by simp
  then have "P x"
    using someI_ex [OF \<open>\<exists>x. P x\<close>] by simp

  from x'_def obtain a xs where a_xs_def : "x' = Join( a # xs) \<and>
               a \<in> snd (A xs) \<and> pointed_list X xs" by auto
  have inc_a_x: "fst (cop_list_inclusion X A xs) a = x" 
    apply (simp add: x'_def)
    unfolding cop_list_inclusion_def
    using a_xs_def by simp

  from \<open>P x\<close> have "x = x' \<or> ((\<exists>xs. x' = Join (fst (A xs) # xs) \<and> pointed_list X xs) \<and>
                             (\<exists>xs. x = Join (fst (A xs) # xs) \<and> pointed_list X xs))"
    unfolding P_def by auto
  then show "pointed_list X (cop_list_index x) \<and>
         cop_list_value x \<in> snd (A (cop_list_index x)) \<and>
         fst (cop_list_inclusion X A (cop_list_index x)) (cop_list_value x) = x"
  proof
    assume "x = x'"
    then show "pointed_list X (cop_list_index x) \<and>
    cop_list_value x \<in> snd (A (cop_list_index x)) \<and>
    fst (cop_list_inclusion X A (cop_list_index x)) (cop_list_value x) = x"
      using inc_a_x a_xs_def by simp
  next
    assume H: "((\<exists>xs. x' = Join (fst (A xs) # xs) \<and> pointed_list X xs) \<and>
             (\<exists>xs. x = Join (fst (A xs) # xs) \<and> pointed_list X xs))"
    then obtain zs where zs_def: "x = Join(fst (A zs) # zs) \<and> pointed_list X zs" by auto
    then have val_x: "cop_list_value x = fst (A zs)" by simp
    from H obtain xs' where "x' = Join (fst (A xs') # xs') \<and> pointed_list X xs'" by auto
    then have "a = fst (A xs)" using a_xs_def by simp
    have zs_inc_dom: "A zs = Dom' (cop_list_inclusion X A (cop_list_index x))"
      unfolding cop_list_inclusion_def using zs_def by simp
    have xs_inc_dom : "A xs = Dom' (cop_list_inclusion X A xs)"
      unfolding cop_list_inclusion_def by simp

    have eq1:"fst (cop_list_inclusion X A (cop_list_index x)) (cop_list_value x) =
          fst (Cod' (cop_list_inclusion X A (cop_list_index x)))"
      apply (subst val_x)
      apply (subst zs_inc_dom)
      using cop_list_inclusion_arr [OF A_obj] zs_def
      unfolding Arr'_def by simp

    have eq2:"x = fst (Cod' (cop_list_inclusion X A xs))"
      apply (subst reverse_equality [OF inc_a_x])
      apply (subst \<open>a = fst (A xs)\<close>)
      apply (subst xs_inc_dom)
      using cop_list_inclusion_arr [OF A_obj] a_xs_def
      unfolding Arr'_def by simp

    show "pointed_list X (cop_list_index x) \<and>
    cop_list_value x \<in> snd (A (cop_list_index x)) \<and>
    fst (cop_list_inclusion X A (cop_list_index x)) (cop_list_value x) = x"
      apply safe
      using zs_def apply simp
      using val_x A_obj unfolding Obj'_def
      using zs_def apply simp
      apply (rule_tac reverse_equality)
      apply (subst eq1)
      apply (subst eq2)
      unfolding cop_list_inclusion_def by simp
  qed
qed


lemma coprod_list_UP_existence: assumes 
      cocone: "\<forall>xs. pointed_list X xs \<longrightarrow> Arr' (cocone xs) \<and> Cod' (cocone xs) = Z"
            "Obj' X" 
     shows "Arr' (coprod_list_UP_map X cocone Z) \<and>
    fst (snd (coprod_list_UP_map X cocone Z)) = coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))) \<and>
    snd (snd (coprod_list_UP_map X cocone Z)) = Z \<and>
    (\<forall>xs. pointed_list X xs \<longrightarrow>
          (coprod_list_UP_map X cocone Z) \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs = cocone xs)"
proof-
  have arr_up: "Arr' (coprod_list_UP_map X cocone Z)"
    using coprod_list_UP_map_arr [OF cocone].
  have dom_up: "fst (snd (coprod_list_UP_map X cocone Z)) =
    coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs)))"
    unfolding coprod_list_UP_map_def by simp
  have cod_up : "snd (snd (coprod_list_UP_map X cocone Z)) = Z"
    unfolding coprod_list_UP_map_def by simp

  show "Arr' (coprod_list_UP_map X cocone Z) \<and>
    fst (snd (coprod_list_UP_map X cocone Z)) =
    coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))) \<and>
    snd (snd (coprod_list_UP_map X cocone Z)) = Z \<and>
    (\<forall>xs. pointed_list X xs \<longrightarrow>
          coprod_list_UP_map X cocone Z \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs =
          cocone xs)" 
    apply (auto simp: arr_up dom_up cod_up)
  proof-
    fix xs
    assume "pointed_list X xs"
    have arr_inc : "Arr' (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)"
      apply (rule_tac cop_list_inclusion_arr)
      using cocone unfolding Arr'_def apply simp
       apply (simp add: \<open>Obj' X\<close>)
      using \<open>pointed_list X xs\<close>.
    have seq: "fst (snd (coprod_list_UP_map X cocone Z)) =
    snd (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs))"
      unfolding coprod_list_UP_map_def cop_list_inclusion_def by simp

    have comp_dom : "fst (snd (coprod_list_UP_map X cocone Z \<cdot>
              cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)) =
    fst (snd (cocone xs))"
      apply (simp add: dom_comp [OF arr_inc arr_up] seq)
      apply (subst cop_list_inclusion_def) by simp

    have comp_cod : "snd (snd (coprod_list_UP_map X cocone Z \<cdot>
              cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)) =
    snd (snd (cocone xs))"
      apply (simp add: cod_comp [OF arr_inc arr_up] seq)
      using cod_up cocone \<open>pointed_list X xs\<close> by simp

    show "coprod_list_UP_map X cocone Z \<cdot>
          cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs =
          cocone xs"
      apply (rule_tac fun_eq_char)
          apply (rule_tac comp_arr [OF arr_up arr_inc seq])
      using cocone \<open>pointed_list X xs\<close> apply simp
        apply (simp add: comp_dom)
       apply (simp add: comp_cod)
    proof-
      fix x
      assume "x \<in> snd (fst (snd (coprod_list_UP_map X cocone Z \<cdot>
                            cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)))"
      then have x_in_inc_dom: "x \<in> snd (fst (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)))"
        by (simp add: dom_comp [OF arr_inc arr_up] seq)
      then have x_in_coc_dom: "x \<in> snd (Dom' (cocone xs))"
        unfolding cop_list_inclusion_def by simp
      have "x = fst (Dom' (cocone xs)) \<or> x \<noteq> fst (Dom' (cocone xs))" by auto
      then show "fst (coprod_list_UP_map X cocone Z \<cdot>
              cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)
          x =
         fst (cocone xs) x"
      proof
        assume "x = fst (Dom' (cocone xs))"
        have "fst (coprod_list_UP_map X cocone Z \<cdot>
       cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)
   (fst (Dom' (cocone xs))) =
  fst (Cod' (cocone xs))"
          using comp_arr [OF arr_up arr_inc seq]
          unfolding Arr'_def
          using comp_dom comp_cod by simp
        then have "fst (coprod_list_UP_map X cocone Z \<cdot>
         cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs) x = fst Z"
          apply (subst \<open>x = fst (Dom' (cocone xs))\<close>)
          using cocone \<open>pointed_list X xs\<close> by simp
        then show "fst (coprod_list_UP_map X cocone Z \<cdot>
         cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs) x = fst (cocone xs) x"
          apply simp
          apply (subst \<open>x = fst (Dom' (cocone xs))\<close>)
          using cocone \<open>pointed_list X xs\<close> unfolding Arr'_def by simp
      next
        assume "x \<noteq> fst (fst (snd (cocone xs)))"
        show "fst (coprod_list_UP_map X cocone Z \<cdot>
         cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)
     x = fst (cocone xs) x"
          unfolding Comp'_def
          using arr_up arr_inc seq x_in_inc_dom apply simp
        proof-
          have some_eq : "(SOME b.
         (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs) \<and>
         Join (x # xs) = b \<and>
         (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs))
          = Join(x # xs)"
          proof
            show "(\<exists>xsa a.
        Join (x # xs) = Join (a # xsa) \<and> a \<in> snd (fst (snd (cocone xsa))) \<and> pointed_list X xsa) \<and>
    Join (x # xs) = Join (x # xs) \<and>
    (\<exists>xsa a.
        Join (x # xs) = Join (a # xsa) \<and> a \<in> snd (fst (snd (cocone xsa))) \<and> pointed_list X xsa)"
              using \<open>pointed_list X xs\<close> x_in_coc_dom by simp
            show "\<And>b. (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs) \<and>
         Join (x # xs) = b \<and>
         (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs) \<Longrightarrow>
         b = Join (x # xs)" by simp
          qed
          have x_xs_in_cop: "Join (x # xs) \<in> snd (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))))"
            unfolding coproductOverPointedLists_def apply simp
            apply (rule_tac exI)
            apply auto
            apply (rule_tac exI)
             apply (rule_tac exI)
            using \<open>pointed_list X xs\<close> x_in_coc_dom apply simp
            apply (rule_tac reverse_equality)
          proof
            show "(\<exists>xsa a.
        Join (x # xs) = Join (a # xsa) \<and> a \<in> snd (fst (snd (cocone xsa))) \<and> pointed_list X xsa) \<and>
    (Join (x # xs) = Join (x # xs) \<or>
     (\<exists>xsa. Join (x # xs) = Join (fst (fst (snd (cocone xsa))) # xsa) \<and> pointed_list X xsa) \<and>
     (\<exists>xsa. Join (x # xs) = Join (fst (fst (snd (cocone xsa))) # xsa) \<and> pointed_list X xsa)) \<and>
    (\<exists>xsa a.
        Join (x # xs) = Join (a # xsa) \<and> a \<in> snd (fst (snd (cocone xsa))) \<and> pointed_list X xsa)"
              using x_in_coc_dom \<open>pointed_list X xs\<close> by auto
            show "\<And>b. (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs) \<and>
         (Join (x # xs) = b \<or>
          (\<exists>xsa. Join (x # xs) = Join (fst (fst (snd (cocone xsa))) # xsa) \<and> pointed_list X xsa) \<and>
          (\<exists>xs. b = Join (fst (fst (snd (cocone xs))) # xs) \<and> pointed_list X xs)) \<and>
         (\<exists>xs a. b = Join (a # xs) \<and> a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs) \<Longrightarrow>
         b = Join (x # xs)" 
              using \<open>x \<noteq> fst (Dom' (cocone xs))\<close> by simp
          qed
            
          show "fst (coprod_list_UP_map X cocone Z)
     (fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs) x) =
    fst (cocone xs) x"
            unfolding cop_list_inclusion_def
            using \<open>x \<noteq> fst (fst (snd (cocone xs)))\<close> 
                  \<open>pointed_list X xs\<close> x_in_coc_dom apply simp
            apply (subst some_eq)
            unfolding coprod_list_UP_map_def 
            using x_xs_in_cop by simp
        qed
      qed
    qed
  qed
qed

lemma coprod_list_UP_uniqueness : assumes
        cocone: "\<forall>xs. pointed_list X xs \<longrightarrow> Arr' (cocone xs) \<and> Cod' (cocone xs) = Z"
            "Obj' X" 
          shows "\<And>f. Arr' f \<and>
         fst (snd f) = coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))) \<and>
         snd (snd f) = Z \<and>
         (\<forall>xs. pointed_list X xs \<longrightarrow>
               f \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs = cocone xs) \<Longrightarrow>
         f = coprod_list_UP_map X cocone Z"
proof-
  have arr_up: "Arr' (coprod_list_UP_map X cocone Z)"
    using coprod_list_UP_map_arr [OF cocone].
  have dom_up: "fst (snd (coprod_list_UP_map X cocone Z)) =
    coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs)))"
    unfolding coprod_list_UP_map_def by simp
  have cod_up : "snd (snd (coprod_list_UP_map X cocone Z)) = Z"
    unfolding coprod_list_UP_map_def by simp
  fix f
  assume f_def: "Arr' f \<and>
         fst (snd f) = coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))) \<and>
         snd (snd f) = Z \<and>
         (\<forall>xs. pointed_list X xs \<longrightarrow>
               f \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs = cocone xs)"
  show "f = coprod_list_UP_map X cocone Z"
    apply (rule_tac fun_eq_char)
  proof-
    show "Arr' f" using f_def by simp
    show "Arr' (coprod_list_UP_map X cocone Z)" 
      using coprod_list_UP_map_arr [OF cocone].
    show "fst (snd f) = fst (snd (coprod_list_UP_map X cocone Z))"
      using dom_up f_def by simp
    show "snd (snd f) = snd (snd (coprod_list_UP_map X cocone Z))"
      using cod_up f_def by simp
    fix x
    assume "x \<in> snd (Dom' f)"
    then have "x \<in> snd (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))))"
      using f_def by simp
    then have x_in_cop: "
    pointed_list X (cop_list_index x) \<and>
    cop_list_value x \<in> snd ((\<lambda>xs. fst (snd (cocone xs))) (cop_list_index x)) \<and>
    fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) (cop_list_index x)) (cop_list_value x) = x"
      apply (rule_tac x_in_cop_list_char)
      using cocone unfolding Arr'_def apply simp
      using \<open>Obj' X\<close> by simp_all
    define a where "a = cop_list_value x"
    define xs where "xs = cop_list_index x"
    from x_in_cop have a_xs_def: "a \<in> snd (fst (snd (cocone xs))) \<and> pointed_list X xs"
      unfolding a_def xs_def by simp
    from x_in_cop have inc_a_x: "fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs) a = x"
      unfolding a_def xs_def by simp

    from a_xs_def have EQ_f: "cocone xs = f \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs"
      using f_def by simp
    have arr_inc: "Arr' (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)"
      apply (rule_tac cop_list_inclusion_arr)
      using cocone unfolding Arr'_def apply simp
       apply (simp add: \<open>Obj' X\<close>)
      by (simp add: a_xs_def)
    have seq: "snd (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)) = fst (snd f)"
      unfolding cop_list_inclusion_def using f_def by simp
    have a_in_inc : "a \<in> snd (fst (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)))"
      unfolding cop_list_inclusion_def
      using a_xs_def by simp

    have fst_f_x: "fst f x = fst (cocone xs) a"
      apply (subst EQ_f)
      unfolding Comp'_def
      using arr_inc f_def seq a_in_inc apply simp
      using inc_a_x by simp

    from coprod_list_UP_existence [OF cocone] 
    have EQ_up: "(coprod_list_UP_map X cocone Z) \<cdot> 
       cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs = cocone xs"
      using a_xs_def by simp
    have up_seq: "snd (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs)) =
            fst (snd (coprod_list_UP_map X cocone Z))"
      unfolding cop_list_inclusion_def coprod_list_UP_map_def by simp
    have fst_up_x: "fst (coprod_list_UP_map X cocone Z) x = fst (cocone xs) a"
      apply (subst reverse_equality [OF EQ_up])
      unfolding Comp'_def
      using arr_inc coprod_list_UP_existence [OF cocone]
            up_seq a_in_inc apply simp
      using inc_a_x by simp

    from fst_f_x and fst_up_x show "fst f x = fst (coprod_list_UP_map X cocone Z) x"
      by simp
  qed
qed


lemma coprod_list_UP : assumes
       cocone: "\<forall>xs. pointed_list X xs \<longrightarrow> Arr' (cocone xs) \<and> Cod' (cocone xs) = Z"
            "Obj' X" 
     shows "\<exists>! f. Arr' f \<and> 
            Dom' f = (coproductOverPointedLists X (\<lambda>xs. Dom' (cocone xs))) \<and> 
            Cod' f = Z \<and>
           (\<forall>xs. pointed_list X xs 
   \<longrightarrow> f \<cdot> (cop_list_inclusion X (\<lambda>xs. Dom' (cocone xs)) xs) = cocone xs)"
proof
  show "Arr' (coprod_list_UP_map X cocone Z) \<and>
    fst (snd (coprod_list_UP_map X cocone Z)) = coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))) \<and>
    snd (snd (coprod_list_UP_map X cocone Z)) = Z \<and>
    (\<forall>xs. pointed_list X xs \<longrightarrow>
          (coprod_list_UP_map X cocone Z) \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs = cocone xs)"
    using coprod_list_UP_existence [OF cocone].
  show "\<And>f. Arr' f \<and>
         fst (snd f) = coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone xs))) \<and>
         snd (snd f) = Z \<and>
         (\<forall>xs. pointed_list X xs \<longrightarrow>
               f \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone xs))) xs = cocone xs) \<Longrightarrow>
         f = coprod_list_UP_map X cocone Z"
    using coprod_list_UP_uniqueness [OF cocone].
qed
      


definition pointed_finset :: "'a pointed_set \<Rightarrow> 'a pointed_set \<Rightarrow> bool" where
  "pointed_finset X A \<equiv> (Obj' A \<and> fst A = fst X \<and> (snd A) \<subseteq> (snd X) \<and> finite (snd A))"

lemma pointed_finset_obj : "pointed_finset X A \<Longrightarrow> Obj' X"
  unfolding Obj'_def pointed_finset_def by auto


fun finite_set_to_list :: "'a pointed_set \<Rightarrow> 'a list" where
  "finite_set_to_list A = rev_get (finite_set_length A) (finite_set_interval_bijection A)"

lemma pointed_finite_set_to_list :"pointed_finset X A \<Longrightarrow> pointed_list X (finite_set_to_list A)"
  unfolding pointed_finset_def pointed_list_def apply auto
proof-
  assume "Obj' A"
  assume "fst A = fst X"
  assume "snd A \<subseteq> snd X"
  assume "finite (snd A)"
  have "length (rev_get (finite_set_length A) (finite_set_interval_bijection A)) \<noteq> length []"
    using pointed_set_length_nn [OF \<open>Obj' A\<close> \<open>finite (snd A)\<close>] by simp
  then show "rev_get (finite_set_length A) (finite_set_interval_bijection A) = [] \<Longrightarrow> False"
    by simp
  show "get (rev_get (finite_set_length A) (finite_set_interval_bijection A)) 0 = fst X"
    apply (subst get_rev_get)
    using pointed_set_length_nn [OF \<open>Obj' A\<close> \<open>finite (snd A)\<close>] apply simp
    using finite_set_interval_bijection_char [OF \<open>Obj' A\<close> \<open>finite (snd A)\<close>] apply simp
    using \<open>fst A = fst X\<close>.
  fix n
  assume "n < finite_set_length A"
  then have "n \<in> {i . i < (finite_set_length A)}" by simp
  then have "finite_set_interval_bijection A n \<in> finite_set_interval_bijection A ` {i . i < (finite_set_length A)}"
    by simp
  then have n_in_x: "finite_set_interval_bijection A n \<in> snd X"
    using finite_set_interval_bijection_char [OF \<open>Obj' A\<close> \<open>finite (snd A)\<close>]
    unfolding bij_betw_def 
    using \<open>snd A \<subseteq> snd X\<close> by auto
  show "get (rev_get (finite_set_length A) (finite_set_interval_bijection A)) n \<in> snd X"
    apply (subst get_rev_get)
    using \<open>n < finite_set_length A\<close> apply simp
    using n_in_x.
qed


fun list_to_finite_set :: "'a list \<Rightarrow> 'a pointed_set" where
  "list_to_finite_set xs = (get xs 0, {x. \<exists>i<length xs. get xs i = x})"

lemma pointed_list_to_finite_set : "pointed_list X xs \<Longrightarrow> pointed_finset X (list_to_finite_set xs)"
  unfolding pointed_finset_def pointed_list_def Obj'_def by auto

fun finset_relation :: "'a LC set \<Rightarrow> 'a LC \<Rightarrow> 'a LC \<Rightarrow> bool" where
  "finset_relation A a b = (a \<in> A \<and> b \<in> A \<and> cop_list_value a = cop_list_value b \<and> 
             list_to_finite_set (cop_list_index a) = list_to_finite_set (cop_list_index b))"


lemma list_finset_id: assumes "pointed_finset X A"
  shows "list_to_finite_set (finite_set_to_list A) = A"
proof
  from \<open>pointed_finset X A\<close> have "Obj' A" unfolding pointed_finset_def by simp
  from \<open>pointed_finset X A\<close> have "finite (snd A)" unfolding pointed_finset_def by simp
  show "fst (list_to_finite_set (finite_set_to_list A)) = fst A"
    apply simp
    apply (subst get_rev_get)
    using pointed_set_length_nn [OF \<open>Obj' A\<close> \<open>finite (snd A)\<close>] apply simp
    using finite_set_interval_bijection_char [OF \<open>Obj' A\<close> \<open>finite (snd A)\<close>] by simp
  show "snd (list_to_finite_set (finite_set_to_list A)) = snd A"
    apply auto
    apply (simp add: get_rev_get)
    using finite_set_interval_bijection_char [OF \<open>Obj' A\<close> \<open>finite (snd A)\<close>]
    unfolding bij_betw_def apply auto[1]
  proof-
    fix x
    assume "x \<in> snd A"
    then have "x \<in> (finite_set_interval_bijection A) ` {i . i < finite_set_length A}"
      using finite_set_interval_bijection_char [OF \<open>Obj' A\<close> \<open>finite (snd A)\<close>]
      unfolding bij_betw_def by simp
    then obtain i where i_def: "i < finite_set_length A \<and> (finite_set_interval_bijection A) i = x"
      by auto
    show "\<exists>i<finite_set_length A.
            get (rev_get (finite_set_length A) (finite_set_interval_bijection A)) i = x"
    proof
      show "i < finite_set_length A \<and>
    get (rev_get (finite_set_length A) (finite_set_interval_bijection A)) i = x"
        using i_def by (simp add: get_rev_get)
    qed
  qed
qed

lemma finset_relation_equiv : "equiv A {(x, y). finset_relation A x y}"
  unfolding equiv_def refl_on_def' sym_def trans_def by simp


lemma finset_relation_inclusion_intro : assumes 
          A_obj: " \<forall>xs. pointed_list X xs \<longrightarrow> Obj' (A xs)"
  and finset_eq: "list_to_finite_set xs = list_to_finite_set ys" 
           and   "Obj' X" "pointed_list X xs" "pointed_list X ys" 
                 "A xs = A ys" 
                 "a \<in> snd (A xs)"
            shows  "finset_relation (snd (coproductOverPointedLists X A))
                 (fst (cop_list_inclusion X A xs) a) (fst (cop_list_inclusion X A ys) a)"
proof-
  have arr_inc_x: "Arr' (cop_list_inclusion X A xs)"
    using cop_list_inclusion_arr [OF A_obj \<open>Obj' X\<close> \<open>pointed_list X xs\<close>].
  have dom_inc_x : "Dom' (cop_list_inclusion X A xs) = A xs"
    unfolding cop_list_inclusion_def by simp
  have cod_inc_x: "Cod' (cop_list_inclusion X A xs) = coproductOverPointedLists X A"
    unfolding cop_list_inclusion_def by simp
  have "a \<in> snd (Dom' (cop_list_inclusion X A xs))"
    using dom_inc_x \<open>a \<in> snd (A xs)\<close> by simp
  from this and arr_inc_x have "fst (cop_list_inclusion X A xs) a \<in> snd (Cod' (cop_list_inclusion X A xs))"
    unfolding Arr'_def setcat.Arr_def by auto
  then have goal1: "fst (cop_list_inclusion X A xs) a \<in> snd (coproductOverPointedLists X A)"
    using cod_inc_x by simp
  have "a \<in> snd (A ys)"
    using \<open>a \<in> snd (A xs)\<close> \<open>A xs = A ys\<close> by simp
  have arr_inc_y: "Arr' (cop_list_inclusion X A ys)"
    using cop_list_inclusion_arr [OF A_obj \<open>Obj' X\<close> \<open>pointed_list X ys\<close>].
  have dom_inc_y : "Dom' (cop_list_inclusion X A ys) = A ys"
    unfolding cop_list_inclusion_def by simp
  have cod_inc_y: "Cod' (cop_list_inclusion X A ys) = coproductOverPointedLists X A"
    unfolding cop_list_inclusion_def by simp

  have "a \<in> snd (Dom' (cop_list_inclusion X A ys))"
    using dom_inc_y \<open>a \<in> snd (A ys)\<close> by simp
  from this and arr_inc_y have "fst (cop_list_inclusion X A ys) a \<in> snd (Cod' (cop_list_inclusion X A ys))"
    unfolding Arr'_def setcat.Arr_def by auto
  then have goal2: "fst (cop_list_inclusion X A ys) a \<in> snd (coproductOverPointedLists X A)"
    using cod_inc_y by simp
  have lem: "a = fst (A xs) \<or> a \<noteq> fst (A xs)" by auto
  show "finset_relation (snd (coproductOverPointedLists X A))
                 (fst (cop_list_inclusion X A xs) a) (fst (cop_list_inclusion X A ys) a)"
    using lem
  proof
    assume "a = fst (A xs)"
    have fst_a_x: "fst (cop_list_inclusion X A xs) a = fst (coproductOverPointedLists X A)" 
      apply (subst \<open>a = fst (A xs)\<close>)
      using arr_inc_x dom_inc_x cod_inc_x unfolding Arr'_def by simp
    have "a = fst (A ys)" 
      using \<open>a = fst (A xs)\<close> \<open>A xs = A ys\<close> by simp
    have fst_a_y : "fst (cop_list_inclusion X A ys) a = fst (coproductOverPointedLists X A)" 
      apply (subst \<open>a = fst (A ys)\<close>)
      using arr_inc_y dom_inc_y cod_inc_y unfolding Arr'_def by simp
    from fst_a_x and fst_a_y show "finset_relation (snd (coproductOverPointedLists X A)) (fst (cop_list_inclusion X A xs) a)
     (fst (cop_list_inclusion X A ys) a)"
      using goal1 goal2 by simp
  next
    assume "a \<noteq> fst (A xs)"
    have inc_a_x: "fst (cop_list_inclusion X A xs) a = Join(a # xs)"
      unfolding cop_list_inclusion_def
      using \<open>a \<in> snd (A xs)\<close> \<open>a \<noteq> fst (A xs)\<close> \<open>pointed_list X xs\<close> by auto
    have "a \<noteq> fst (A ys)"
      using \<open>a \<noteq> fst (A xs)\<close> \<open>A xs = A ys\<close> by simp
    have inc_a_y : "fst (cop_list_inclusion X A ys) a = Join (a # ys)"
      unfolding cop_list_inclusion_def
      using \<open>a \<in> snd (A ys)\<close> \<open>a \<noteq> fst (A ys)\<close> \<open>pointed_list X ys\<close> by auto
    from inc_a_x and inc_a_y show "finset_relation (snd (coproductOverPointedLists X A)) (fst (cop_list_inclusion X A xs) a)
     (fst (cop_list_inclusion X A ys) a)"
      using goal1 goal2 finset_eq by simp
  qed
qed




definition coproductOverFinsets :: "'a LC pointed_set \<Rightarrow> ('a LC pointed_set \<Rightarrow> 'a LC pointed_set) \<Rightarrow> 'a LC pointed_set" where
  "coproductOverFinsets X A \<equiv> 
         quotient_by_equiv_rel
         (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k)))
         (finset_relation (snd (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k)))))"


definition cop_finset_inclusion :: "'a LC pointed_set \<Rightarrow> ('a LC pointed_set \<Rightarrow> 'a LC pointed_set) \<Rightarrow> 'a LC pointed_set \<Rightarrow> 'a LC parr" where
  "cop_finset_inclusion X A S \<equiv> Comp' 
    (quotient_proj (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k))) 
     (finset_relation (snd (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k)))) )) 
    (cop_list_inclusion X (\<lambda>xs. A (list_to_finite_set xs)) (finite_set_to_list S))"

fun cop_finset_index :: "'a LC \<Rightarrow> 'a LC pointed_set" where
  "cop_finset_index x = list_to_finite_set (cop_list_index x)"

fun cop_finset_value :: "'a LC \<Rightarrow> 'a LC" where
  "cop_finset_value x = cop_list_value x"

definition coprod_finset_UP_map :: "'a LC pointed_set \<Rightarrow> ('a LC pointed_set \<Rightarrow> 'a LC parr) \<Rightarrow> 'a LC pointed_set \<Rightarrow> 'a LC parr" where
  "coprod_finset_UP_map X cocone Z \<equiv> Comp'
                          (coprod_list_UP_map X (\<lambda>k. cocone (list_to_finite_set k)) Z)
                          (quotient_section (coproductOverPointedLists X (\<lambda>k. Dom' (cocone (list_to_finite_set k)))) 
                          (finset_relation (snd ( coproductOverPointedLists X (\<lambda>k. Dom' (cocone (list_to_finite_set k))))  )))"

definition list_finset_proj where
  "list_finset_proj X A \<equiv>  quotient_proj (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k))) 
                           (finset_relation (snd (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k)))))"

lemma cop_finset_obj:
  assumes cocone: "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A S)"
  and "Obj' X"
  shows "Obj' (coproductOverFinsets X A)"
proof-
  have "Arr' (list_finset_proj X A)"
    unfolding list_finset_proj_def
    apply (rule_tac quot_proj_arr)
    apply (rule_tac cop_list_obj)
    using cocone pointed_list_to_finite_set apply blast
    using \<open>Obj' X\<close>.
  then have "Obj' (Cod' (list_finset_proj X A))"
    unfolding Arr'_def by simp
  then show "Obj' (coproductOverFinsets X A)"
    unfolding list_finset_proj_def coproductOverFinsets_def by simp
qed


lemma cop_finset_inclusion_arr : 
  assumes cocone: "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (cocone S)"
      and "pointed_finset X A" 
    shows "Arr' (cop_finset_inclusion X cocone A)"
  unfolding cop_finset_inclusion_def
  apply (rule_tac comp_arr)
    apply (rule_tac quot_proj_arr)
    apply (rule_tac cop_list_obj)
  using pointed_list_to_finite_set cocone apply blast
  using pointed_finset_obj [OF \<open>pointed_finset X A\<close>] apply simp
   apply (rule_tac cop_list_inclusion_arr)
  using pointed_list_to_finite_set cocone apply blast
  using pointed_finset_obj [OF \<open>pointed_finset X A\<close>] apply simp
  using pointed_finite_set_to_list [OF \<open>pointed_finset X A\<close>] apply simp
  unfolding cop_list_inclusion_def by simp

lemma cop_finset_inclusion_dom : assumes cocone : "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A S)"
  and "pointed_finset X S" 
  shows "Dom' (cop_finset_inclusion X A S) = A S"
  unfolding cop_finset_inclusion_def
  apply (subst dom_comp)
     apply (rule_tac cop_list_inclusion_arr)
  using pointed_list_to_finite_set cocone apply blast
  using pointed_finset_obj [OF \<open>pointed_finset X S\<close>] apply simp
  using pointed_finite_set_to_list [OF \<open>pointed_finset X S\<close>] apply simp
    apply (rule_tac quot_proj_arr)
    apply (rule_tac cop_list_obj)
  using pointed_list_to_finite_set cocone apply blast
  using pointed_finset_obj [OF \<open>pointed_finset X S\<close>] apply simp
  unfolding cop_list_inclusion_def apply simp
  using list_finset_id [OF \<open>pointed_finset X S\<close>] by simp

lemma cop_finset_inclusion_cod : assumes cocone : "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A S)"
  and "pointed_finset X S" 
shows "Cod' (cop_finset_inclusion X A S) = coproductOverFinsets X A"
  unfolding cop_finset_inclusion_def
  apply (subst cod_comp)
     apply (rule_tac cop_list_inclusion_arr)
  using pointed_list_to_finite_set cocone apply blast
  using pointed_finset_obj [OF \<open>pointed_finset X S\<close>] apply simp
  using pointed_finite_set_to_list [OF \<open>pointed_finset X S\<close>] apply simp
    apply (rule_tac quot_proj_arr)
    apply (rule_tac cop_list_obj)
  using pointed_list_to_finite_set cocone apply blast
  using pointed_finset_obj [OF \<open>pointed_finset X S\<close>] apply simp
  unfolding cop_list_inclusion_def apply simp
  unfolding coproductOverFinsets_def by simp


lemma x_in_cop_finset_char : 
  assumes A_obj: "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A S)" 
   and "Obj' X" "x \<in> snd (coproductOverFinsets X A)"
 shows "pointed_finset X (cop_finset_index x) \<and>
        cop_finset_value x \<in> snd (A (cop_finset_index x)) \<and>
        fst (cop_finset_inclusion X A (cop_finset_index x)) (cop_finset_value x) = x"
  apply safe
proof-
  obtain x' where x'_def: "x' \<in>snd (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k))) \<and>
       x =
       (SOME b.
           b \<in> snd (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k))) \<and>
           cop_list_value x' = cop_list_value b \<and>
           get (cop_list_index x') 0 = get (cop_list_index b) 0 \<and>
           {x. \<exists>i<length (cop_list_index x'). get (cop_list_index x') i = x} =
           {x. \<exists>i<length (cop_list_index b). get (cop_list_index b) i = x} \<and>
           b \<in> snd (coproductOverPointedLists X
                      (\<lambda>k. A (list_to_finite_set k))))"
    using \<open>x \<in> snd (coproductOverFinsets X A)\<close>
    unfolding coproductOverFinsets_def by auto
  define P where "P = (\<lambda>b. b \<in> snd (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k))) \<and>
           cop_list_value x' = cop_list_value b \<and>
           get (cop_list_index x') 0 = get (cop_list_index b) 0 \<and>
           {x. \<exists>i<length (cop_list_index x'). get (cop_list_index x') i = x} =
           {x. \<exists>i<length (cop_list_index b). get (cop_list_index b) i = x} \<and>
           b \<in> snd (coproductOverPointedLists X
                      (\<lambda>k. A (list_to_finite_set k))))"
  have "\<exists>x. P x"
    unfolding P_def
    apply (rule_tac exI)
    using x'_def by auto
  have "P x"
    using someI_ex [OF \<open>\<exists>x. P x\<close>] x'_def
    unfolding reverse_equality [OF P_def] by simp
  then have "x \<in> snd (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k)))"
    unfolding P_def by simp
  then have x_in_cop : "pointed_list X (cop_list_index x) \<and>
    cop_list_value x \<in> snd (A (list_to_finite_set (cop_list_index x))) \<and>
    fst (cop_list_inclusion X (\<lambda>k. A (list_to_finite_set k)) (cop_list_index x)) (cop_list_value x) = x"
    apply (rule_tac x_in_cop_list_char)
    using pointed_list_to_finite_set A_obj apply blast
    using \<open>Obj' X\<close> by simp

  have arr_inc: "Arr'
             (cop_list_inclusion X (\<lambda>xs. A (list_to_finite_set xs))
               (finite_set_to_list (cop_finset_index x)))"
    apply (rule_tac cop_list_inclusion_arr)
    using A_obj pointed_list_to_finite_set apply blast
    using \<open>Obj' X\<close> apply simp
    apply (subst cop_finset_index.simps)
    using pointed_finite_set_to_list[OF pointed_list_to_finite_set] x_in_cop by blast
    
  define pi where "pi =  (quotient_proj (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k)))
               (finset_relation
                 (snd (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k))))))"
  have arr_pi : "Arr' pi"
    unfolding pi_def
    apply (rule_tac quot_proj_arr)
    apply (rule_tac cop_list_obj)
    using A_obj pointed_list_to_finite_set apply blast
    using \<open>Obj' X\<close> by simp
  have seq: "Cod' (cop_list_inclusion X (\<lambda>xs. A (list_to_finite_set xs))
               (finite_set_to_list (cop_finset_index x))) = Dom' pi"
    unfolding pi_def cop_list_inclusion_def by simp
  have in_dom : "cop_list_value x \<in> snd (Dom' (cop_list_inclusion X (\<lambda>xs. A (list_to_finite_set xs))
               (finite_set_to_list (cop_finset_index x))))"
    unfolding cop_list_inclusion_def
    apply (subst list_finset_id)
    apply (subst cop_finset_index.simps)
    using pointed_list_to_finite_set x_in_cop apply blast 
    apply (subst list_finset_id)
    apply (subst cop_finset_index.simps)
    using pointed_list_to_finite_set x_in_cop apply blast 
    using x_in_cop by simp

  have comp_char: "fst (cop_finset_inclusion X A (cop_finset_index x)) (cop_finset_value x) =
        fst pi (fst (cop_list_inclusion X (\<lambda>xs. A (list_to_finite_set xs))
                       (finite_set_to_list (cop_finset_index x)))(cop_finset_value x))"
    unfolding cop_finset_inclusion_def
    apply (subst reverse_equality [OF pi_def])
    unfolding Comp'_def 
    using arr_inc arr_pi seq in_dom by simp

  from x_in_cop have inc_list_eq : "fst (cop_list_inclusion X (\<lambda>k. A (list_to_finite_set k)) (cop_list_index x)) (cop_list_value x) =
  x" by simp

  have proj_eq : "x = fst pi x"
    unfolding pi_def 
    using \<open>P x\<close> unfolding P_def
    using x'_def by simp

  have A_list_obj: "\<forall>xs. pointed_list X xs \<longrightarrow> Obj' ((\<lambda>k. A (list_to_finite_set k)) xs)"
    using A_obj pointed_list_to_finite_set by blast


  show "fst (cop_finset_inclusion X A (cop_finset_index x)) (cop_finset_value x) = x"
    apply (subst comp_char)
    apply (rule_tac reverse_equality)
    apply (subst proj_eq)
    apply (subst reverse_equality [OF inc_list_eq])
    unfolding pi_def
    apply (rule_tac R_implies_quot_eq)
    using finset_relation_equiv apply blast
    apply (subst cop_finset_value.simps)
      apply (rule_tac finset_relation_inclusion_intro)
    using A_obj pointed_list_to_finite_set apply blast
           apply (subst cop_finset_index.simps)
    using reverse_equality [OF list_finset_id[OF pointed_list_to_finite_set]]
          x_in_cop apply blast
    using \<open>Obj' X\<close> apply simp
    using x_in_cop apply simp
        apply (subst cop_finset_index.simps)
    using pointed_finite_set_to_list [OF pointed_list_to_finite_set]
          x_in_cop apply blast
       apply (subst cop_finset_index.simps)
       apply (subst list_finset_id[OF pointed_list_to_finite_set])
    using x_in_cop apply blast
       apply simp
    using x_in_cop apply simp
  proof-
    define inc1 where "inc1 = (cop_list_inclusion X (\<lambda>xs. A (list_to_finite_set xs))
          (finite_set_to_list (cop_finset_index x)))"
    define inc2 where "inc2 = (cop_list_inclusion X (\<lambda>k. A (list_to_finite_set k)) (cop_list_index x))"

    have "Arr' inc1"
      unfolding inc1_def
      using arr_inc.

    have "Arr' inc2"
      unfolding inc2_def
      apply (rule_tac cop_list_inclusion_arr)
      using A_obj pointed_list_to_finite_set apply blast
      using \<open>Obj' X\<close> apply simp
      using x_in_cop by simp

    have in_dom1 : "cop_list_value x \<in> snd (Dom' (inc1))"
      unfolding inc1_def
      apply (subst cop_finset_index.simps)
      unfolding cop_list_inclusion_def
      apply (subst list_finset_id)
       apply (rule_tac pointed_list_to_finite_set)
      using x_in_cop apply blast
      apply (subst list_finset_id)
       apply (rule_tac pointed_list_to_finite_set)
      using x_in_cop apply blast
      using x_in_cop by simp
    from \<open>Arr' inc1\<close> and in_dom1 have "fst inc1 (cop_list_value x) \<in> snd (Cod' inc1)"
      unfolding Arr'_def setcat.Arr_def by auto
    then show "fst (cop_list_inclusion X (\<lambda>xs. A (list_to_finite_set xs))
          (finite_set_to_list (cop_finset_index x)))
     (cop_finset_value x)
    \<in> snd (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k)))"
      unfolding inc1_def cop_list_inclusion_def by simp

    have in_dom2: "(cop_list_value x) \<in> snd (Dom' inc2)"
      unfolding inc2_def
      unfolding cop_list_inclusion_def using x_in_cop by simp
    from \<open>Arr' inc2\<close> and in_dom2 have "fst inc2 (cop_list_value x) \<in> snd (Cod' inc2)"
      unfolding Arr'_def setcat.Arr_def by auto
    then show "fst (cop_list_inclusion X (\<lambda>k. A (list_to_finite_set k)) (cop_list_index x)) (cop_list_value x)
    \<in> snd (coproductOverPointedLists X (\<lambda>k. A (list_to_finite_set k)))"
      unfolding inc2_def cop_list_inclusion_def by simp
  qed

  show "pointed_finset X (cop_finset_index x)"
    apply (subst cop_finset_index.simps)
    using x_in_cop pointed_list_to_finite_set by blast
  show "cop_finset_value x \<in> snd (A (cop_finset_index x))"
    apply (subst cop_finset_index.simps)
    apply (subst cop_finset_value.simps)
    using x_in_cop by simp
qed






lemma coprod_finset_UP_map_arr : assumes
       cocone: "\<forall>A. pointed_finset X A \<longrightarrow> Arr' (cocone A) \<and> Cod' (cocone A) = Z"
            "Obj' X" "Obj' Z" 
          shows "Arr' (coprod_finset_UP_map X cocone Z)"
  unfolding coprod_finset_UP_map_def
  apply (rule_tac comp_arr)
    apply (rule_tac coprod_list_UP_map_arr)
  using pointed_list_to_finite_set cocone apply blast
  using \<open>Obj' X\<close> apply simp
   apply (rule_tac quot_sec_arr)
  using finset_relation_equiv apply blast
   apply (rule_tac cop_list_obj)
  using pointed_list_to_finite_set cocone unfolding Arr'_def apply blast
  using \<open>Obj' X\<close> apply simp
  unfolding coprod_list_UP_map_def by simp

lemma coprod_finset_UP_map_dom: assumes
       cocone: "\<forall>A. pointed_finset X A \<longrightarrow> Arr' (cocone A) \<and> Cod' (cocone A) = Z"
            "Obj' X" "Obj' Z" 
          shows "Dom' (coprod_finset_UP_map X cocone Z) = coproductOverFinsets X (\<lambda>k. Dom' (cocone k))"
  unfolding coprod_finset_UP_map_def
  apply (subst dom_comp)
     apply (rule_tac quot_sec_arr)
  using finset_relation_equiv apply blast
     apply (rule_tac cop_list_obj)
  using pointed_list_to_finite_set cocone Arr'_def apply blast
  using \<open>Obj' X\<close> apply simp
    apply (rule_tac coprod_list_UP_map_arr)
  using pointed_list_to_finite_set cocone apply blast
  using \<open>Obj' X\<close> apply simp
  unfolding coprod_list_UP_map_def apply simp
  unfolding coproductOverFinsets_def by simp

lemma coprod_finset_UP_map_cod: assumes
       cocone: "\<forall>A. pointed_finset X A \<longrightarrow> Arr' (cocone A) \<and> Cod' (cocone A) = Z"
            "Obj' X" "Obj' Z" 
          shows "Cod' (coprod_finset_UP_map X cocone Z) = Z"
  unfolding coprod_finset_UP_map_def
  apply (subst cod_comp)
     apply (rule_tac quot_sec_arr)
  using finset_relation_equiv apply blast
     apply (rule_tac cop_list_obj)
  using pointed_list_to_finite_set cocone Arr'_def apply blast
  using \<open>Obj' X\<close> apply simp
    apply (rule_tac coprod_list_UP_map_arr)
  using pointed_list_to_finite_set cocone apply blast
  using \<open>Obj' X\<close> apply simp
  unfolding coprod_list_UP_map_def apply simp
  unfolding coproductOverFinsets_def by simp






lemma list_finset_quot_cocone :  assumes
       cocone: "\<forall>A. pointed_finset X A \<longrightarrow> Arr' (cocone A) \<and> Cod' (cocone A) = Z"
            "Obj' X" "Obj' Z" 
          shows "Arr' (coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z) \<and>
 fst (snd (coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z)) = (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))) \<and>
         snd (snd (coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z)) = Z \<and>
 (\<forall>x y. (finset_relation (snd (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))))) x y 
         \<longrightarrow> fst (coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z) x = fst (coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z) y)"
proof-
  from cocone have 
  list_cocone : "\<forall>xs. pointed_list X xs \<longrightarrow> Arr' (cocone (list_to_finite_set xs)) \<and>
                 Cod' (cocone (list_to_finite_set xs)) = Z"
    using pointed_list_to_finite_set by blast

  define list_f where "list_f = coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z"

  have list_f_prop : "Arr' list_f \<and>
         fst (snd list_f) =
         coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) \<and>
         snd (snd list_f) = Z \<and>
         (\<forall>xs. pointed_list X xs \<longrightarrow>
               list_f \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs =
               cocone (list_to_finite_set xs))"
    unfolding list_f_def
    using coprod_list_UP_existence [OF list_cocone \<open>Obj' X\<close>].

  define A where "A = (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))))"
  define R where "R = finset_relation (snd A)"
  have quot_cocone : "Arr' list_f \<and> fst (snd list_f) = A \<and>
         snd (snd (list_f)) = Z \<and> (\<forall>x y. R x y \<longrightarrow> fst list_f x = fst list_f y)"
    using list_f_prop unfolding A_def apply safe
  proof-
    fix x y
    assume "R x y" 
    from \<open>R x y\<close> have "x \<in> snd (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))))"
      unfolding R_def A_def by simp
    then have x_in_cop: "pointed_list X (cop_list_index x) \<and>
    cop_list_value x \<in> snd ((\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) (cop_list_index x)) \<and>
    fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) (cop_list_index x)) (cop_list_value x) = x"
      apply (rule_tac x_in_cop_list_char)
      using list_cocone unfolding Arr'_def apply simp
      using \<open>Obj' X\<close> apply simp
      by simp
    from \<open>R x y\<close> have "y \<in> snd (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))))"
      unfolding R_def A_def by simp
    then have y_in_cop: "pointed_list X (cop_list_index y) \<and>
    cop_list_value y \<in> snd ((\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) (cop_list_index y)) \<and>
    fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) (cop_list_index y)) (cop_list_value y) = y"
      apply (rule_tac x_in_cop_list_char)
      using list_cocone unfolding Arr'_def apply simp
      using \<open>Obj' X\<close> apply simp
      by simp
    from x_in_cop have x_inc: "x = fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) (cop_list_index x)) (cop_list_value x)"
      by simp
    from y_in_cop have y_inc: "y = fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) (cop_list_index y)) (cop_list_value y)"
      by simp
    have val_eq : "cop_list_value x = cop_list_value y"
      using \<open>R x y\<close> unfolding R_def by simp
    have ind_eq: "list_to_finite_set (cop_list_index x) = list_to_finite_set (cop_list_index y)"
      using \<open>R x y\<close> unfolding R_def by simp
    have x_cocone_eq: "list_f \<cdot>
     (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
            (cop_list_index x)) = cocone (list_to_finite_set (cop_list_index x))"
      using list_f_prop x_in_cop by simp
    have y_cocone_eq: "list_f \<cdot>
     (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
            (cop_list_index y)) = cocone (list_to_finite_set (cop_list_index y))"
      using list_f_prop y_in_cop by simp
    have arr_inc_x : " Arr'
                  (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
                    (cop_list_index x))"
      apply (rule_tac cop_list_inclusion_arr)
      using list_cocone unfolding Arr'_def apply simp
      using \<open>Obj' X\<close> apply simp
      using x_in_cop by simp
    have arr_inc_y : " Arr'
                  (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
                    (cop_list_index y))"
      apply (rule_tac cop_list_inclusion_arr)
      using list_cocone unfolding Arr'_def apply simp
      using \<open>Obj' X\<close> apply simp
      using y_in_cop by simp
    have arr_list_f : "Arr' (list_f)" using list_f_prop by simp
    have seq_x : "snd (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
                            (cop_list_index x))) =
                 fst (snd list_f)"
      unfolding cop_list_inclusion_def using list_f_prop by simp
    have seq_y : "snd (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
                            (cop_list_index y))) =
                 fst (snd list_f)"
      unfolding cop_list_inclusion_def using list_f_prop by simp
    have comp_char_x: "\<And>z. z \<in> snd (Dom' (cop_list_inclusion X
                              (\<lambda>xs. fst (snd (cocone (get xs 0, {x. \<exists>i<length xs. get xs i = x}))))
                              (cop_list_index x))) \<Longrightarrow>
      fst list_f
     (fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
            (cop_list_index x)) z) = fst (list_f \<cdot>
     (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
            (cop_list_index x))) z"
      unfolding Comp'_def
      using arr_inc_x seq_x arr_list_f by simp
    have comp_char_y: "\<And>z. z \<in> snd (Dom' (cop_list_inclusion X
                              (\<lambda>xs. fst (snd (cocone (get xs 0, {x. \<exists>i<length xs. get xs i = x}))))
                              (cop_list_index y))) \<Longrightarrow>
      fst list_f
     (fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
            (cop_list_index y)) z) = fst (list_f \<cdot>
     (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
            (cop_list_index y))) z"
      unfolding Comp'_def
      using arr_inc_y seq_y arr_list_f by simp


    show "fst list_f x = fst list_f y"
      apply (subst x_inc)
      apply (subst comp_char_x)
       apply (subst cop_list_inclusion_def)
       apply simp
      using x_in_cop apply simp
      apply (subst x_cocone_eq)
      apply (subst val_eq)
      apply (subst ind_eq)
      apply (subst reverse_equality [OF y_cocone_eq])
      apply (subst reverse_equality [OF comp_char_y])
       apply (subst cop_list_inclusion_def)
       apply simp
      using y_in_cop apply simp
      using y_in_cop by simp
  qed
  then show "Arr' (coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z) \<and>
    fst (snd (coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z)) =
    coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) \<and>
    snd (snd (coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z)) = Z \<and>
    (\<forall>x y. finset_relation
            (snd (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))))) x
            y \<longrightarrow>
           fst (coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z) x =
           fst (coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z) y)"
    unfolding list_f_def R_def A_def.
qed



lemma coprod_finset_UP_existence : assumes
       cocone: "\<forall>S. pointed_finset X S \<longrightarrow> Arr' (cocone S) \<and> Cod' (cocone S) = Z"
            "Obj' X" "Obj' Z" 
     shows "Arr' (coprod_finset_UP_map X cocone Z) \<and> 
            Dom' (coprod_finset_UP_map X cocone Z) = (coproductOverFinsets X (\<lambda>B. Dom' (cocone B))) \<and> 
            Cod' (coprod_finset_UP_map X cocone Z) = Z \<and>
           (\<forall>S. pointed_finset X S 
   \<longrightarrow> (coprod_finset_UP_map X cocone Z) \<cdot> (cop_finset_inclusion X (\<lambda>B. Dom' (cocone B)) S) = cocone S)"
proof-
  from cocone have 
  list_cocone : "\<forall>xs. pointed_list X xs \<longrightarrow> Arr' (cocone (list_to_finite_set xs)) \<and>
                 Cod' (cocone (list_to_finite_set xs)) = Z"
    using pointed_list_to_finite_set by blast

  define list_f where "list_f = coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z"

  have list_f_prop : "Arr' list_f \<and>
         fst (snd list_f) =
         coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) \<and>
         snd (snd list_f) = Z \<and>
         (\<forall>xs. pointed_list X xs \<longrightarrow>
               list_f \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs =
               cocone (list_to_finite_set xs))"
    unfolding list_f_def
    using coprod_list_UP_existence [OF list_cocone \<open>Obj' X\<close>].

  define A where "A = (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))))"
  define R where "R = finset_relation (snd A)"
  have quot_cocone : "Arr' list_f \<and> fst (snd list_f) = A \<and>
         snd (snd (list_f)) = Z \<and> (\<forall>x y. R x y \<longrightarrow> fst list_f x = fst list_f y)"
    unfolding list_f_def R_def A_def
    using list_finset_quot_cocone [OF cocone].

  have R_equiv: "equiv (snd A) {(x, y). R x y}"
    unfolding R_def using finset_relation_equiv.
  have "Obj' A"
    unfolding A_def
    apply (rule_tac cop_list_obj)
    using list_cocone unfolding Arr'_def apply simp
    using \<open>Obj' X\<close>.

  define f where "f = list_f \<cdot> (quotient_section A R)"
  have f_up_map: "f = coprod_finset_UP_map X cocone Z"
    unfolding f_def list_f_def coprod_finset_UP_map_def A_def R_def by blast
  have f_prop : "Arr' f \<and>
         fst (snd f) = quotient_by_equiv_rel A R \<and> snd (snd f) = Z \<and> f \<cdot> quotient_proj A R = list_f"
    using quotient_UP_existence [OF R_equiv quot_cocone \<open>Obj' A\<close>]
    unfolding f_def.
  have "Arr' f \<and>
         fst (snd f) = coproductOverFinsets X (\<lambda>B. fst (snd (cocone B))) \<and>
         snd (snd f) = Z \<and>
         (\<forall>A. pointed_finset X A \<longrightarrow>
              f \<cdot> cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) A = cocone A)"
    apply safe
    using f_prop apply simp
    unfolding coproductOverFinsets_def
    using f_prop
    unfolding A_def R_def apply simp
    using f_prop apply simp
  proof-
    fix a A
    assume "pointed_finset X (a, A)"
    show "f \<cdot> cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) (a, A) = cocone (a, A)"
      unfolding cop_finset_inclusion_def
      apply (subst reverse_equality [OF classical_category.Comp_assoc [OF ccpf]])
    proof-
      show "Arr'
     (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
       (finite_set_to_list (a, A)))"
        apply (rule_tac cop_list_inclusion_arr)
        using list_cocone unfolding Arr'_def apply simp
        using \<open>Obj' X\<close> apply simp
        using pointed_finite_set_to_list [OF \<open>pointed_finset X (a, A)\<close>].
      show "Arr'
     (quotient_proj (coproductOverPointedLists X (\<lambda>k. fst (snd (cocone (list_to_finite_set k)))))
       (finset_relation
         (snd (coproductOverPointedLists X (\<lambda>k. fst (snd (cocone (list_to_finite_set k))))))))"
        apply (rule_tac quot_proj_arr)
        apply (rule_tac cop_list_obj)
        using list_cocone unfolding Arr'_def apply simp
        using \<open>Obj' X\<close>.
      show "Arr' f"
        using f_prop by simp
      show "snd (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
               (finite_set_to_list (a, A)))) =
    fst (snd (quotient_proj
               (coproductOverPointedLists X (\<lambda>k. fst (snd (cocone (list_to_finite_set k)))))
               (finset_relation
                 (snd (coproductOverPointedLists X
                        (\<lambda>k. fst (snd (cocone (list_to_finite_set k)))))))))"
        unfolding cop_list_inclusion_def by simp
      show "snd (snd (quotient_proj
               (coproductOverPointedLists X (\<lambda>k. fst (snd (cocone (list_to_finite_set k)))))
               (finset_relation
                 (snd (coproductOverPointedLists X
                        (\<lambda>k. fst (snd (cocone (list_to_finite_set k))))))))) =
    fst (snd f)"
        using f_prop unfolding R_def A_def by simp
      have eq1: "f \<cdot> quotient_proj (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))))
       (finset_relation
         (snd (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))))) =
  list_f"
        using f_prop unfolding R_def A_def by simp
      have eq2: "(\<And>xs. pointed_list X xs \<Longrightarrow>
          list_f \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs =
          cocone (list_to_finite_set xs))"
        using list_f_prop by simp
      show "(f \<cdot> quotient_proj (coproductOverPointedLists X (\<lambda>k. fst (snd (cocone (list_to_finite_set k)))))
          (finset_relation
            (snd (coproductOverPointedLists X (\<lambda>k. fst (snd (cocone (list_to_finite_set k)))))))) \<cdot>
    cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
     (finite_set_to_list (a, A)) =
    cocone (a, A)"
        apply (subst eq1)
        apply (subst eq2)
        using pointed_finite_set_to_list [OF \<open>pointed_finset X (a, A)\<close>] apply simp
        apply (subst list_finset_id)
        using \<open>pointed_finset X (a, A)\<close> by auto
    qed
  qed
  then show "Arr' (coprod_finset_UP_map X cocone Z) \<and>
    fst (snd (coprod_finset_UP_map X cocone Z)) =
    coproductOverFinsets X (\<lambda>B. fst (snd (cocone B))) \<and>
    snd (snd (coprod_finset_UP_map X cocone Z)) = Z \<and>
    (\<forall>A. pointed_finset X A \<longrightarrow>
         coprod_finset_UP_map X cocone Z \<cdot> cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) A =
         cocone A)"
    using f_up_map by simp
qed

lemma coprod_finset_UP_uniqueness: assumes
       cocone: "\<forall>A. pointed_finset X A \<longrightarrow> Arr' (cocone A) \<and> Cod' (cocone A) = Z"
            "Obj' X" "Obj' Z" 
          shows "\<And>f. Arr' f \<and>
         fst (snd f) = coproductOverFinsets X (\<lambda>B. fst (snd (cocone B))) \<and>
         snd (snd f) = Z \<and>
         (\<forall>A. pointed_finset X A \<longrightarrow>
              f \<cdot> cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) A = cocone A) \<Longrightarrow>
         f = coprod_finset_UP_map X cocone Z"
proof-
  from cocone have 
  list_cocone : "\<forall>xs. pointed_list X xs \<longrightarrow> Arr' (cocone (list_to_finite_set xs)) \<and>
                 Cod' (cocone (list_to_finite_set xs)) = Z"
    using pointed_list_to_finite_set by blast

  define list_f where "list_f = coprod_list_UP_map X (\<lambda>xs. cocone (list_to_finite_set xs)) Z"

  have list_f_prop : "Arr' list_f \<and>
         fst (snd list_f) =
         coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) \<and>
         snd (snd list_f) = Z \<and>
         (\<forall>xs. pointed_list X xs \<longrightarrow>
               list_f \<cdot> cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs =
               cocone (list_to_finite_set xs))"
    unfolding list_f_def
    using coprod_list_UP_existence [OF list_cocone \<open>Obj' X\<close>].

  define A where "A = (coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))))"
  define R where "R = finset_relation (snd A)"
  have quot_cocone : "Arr' list_f \<and> fst (snd list_f) = A \<and>
         snd (snd (list_f)) = Z \<and> (\<forall>x y. R x y \<longrightarrow> fst list_f x = fst list_f y)"
    unfolding list_f_def R_def A_def
    using list_finset_quot_cocone [OF cocone].

  have R_equiv: "equiv (snd A) {(x, y). R x y}"
    unfolding R_def using finset_relation_equiv.
  have "Obj' A"
    unfolding A_def
    apply (rule_tac cop_list_obj)
    using list_cocone unfolding Arr'_def apply simp
    using \<open>Obj' X\<close>.

  fix f
  assume f_prop : "Arr' f \<and>
         fst (snd f) = coproductOverFinsets X (\<lambda>B. fst (snd (cocone B))) \<and>
         snd (snd f) = Z \<and>
         (\<forall>A. pointed_finset X A \<longrightarrow>
              f \<cdot> cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) A = cocone A)"

  show "f = coprod_finset_UP_map X cocone Z"
    unfolding coprod_finset_UP_map_def
    apply (subst reverse_equality [OF list_f_def])
    apply (subst reverse_equality [OF A_def])
    apply (subst reverse_equality [OF A_def])
    apply (subst reverse_equality [OF R_def])
    apply (rule_tac quotient_UP_uniqueness [OF R_equiv quot_cocone \<open>Obj' A\<close>])
    apply safe
  proof-
    show "Arr' f" using f_prop by simp
    show "fst (snd f) = quotient_by_equiv_rel A R"
      unfolding R_def A_def
      using f_prop
      unfolding coproductOverFinsets_def by simp
    show "snd (snd f) = Z"
      using f_prop by simp
    show "f \<cdot> quotient_proj A R = list_f"
      unfolding list_f_def
      apply (rule_tac coprod_list_UP_uniqueness [OF list_cocone \<open>Obj' X\<close>])
      apply safe
    proof-
      have arr_f: "Arr' f" using f_prop by simp
      have arr_proj : "Arr' (quotient_proj A R)"
        using quot_proj_arr [OF \<open>Obj' A\<close>] by simp
      have seq: "fst (snd f) = snd (snd (quotient_proj A R))"
        using f_prop
        unfolding coproductOverFinsets_def R_def A_def by simp
      show "Arr' (f \<cdot> quotient_proj A R)"
        using comp_arr [OF arr_f arr_proj seq].
      show "fst (snd (f \<cdot> quotient_proj A R)) =
    coproductOverPointedLists X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))"
        apply (subst dom_comp [OF arr_proj arr_f reverse_equality [OF seq]])
        unfolding A_def by simp
      show "snd (snd (f \<cdot> quotient_proj A R)) = Z"
        apply (subst cod_comp [OF arr_proj arr_f reverse_equality [OF seq]])
        using f_prop by simp
      fix xs
      assume "pointed_list X xs"
      show "(f \<cdot> quotient_proj A R) \<cdot>
          cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs =
          cocone (list_to_finite_set xs)"
        apply (subst classical_category.Comp_assoc [OF ccpf])
      proof-
        show arr_inc: "Arr' (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs)"
          apply (rule_tac cop_list_inclusion_arr)
          using list_cocone unfolding Arr'_def apply simp
          using \<open>Obj' X\<close> apply simp
          using \<open>pointed_list X xs\<close> by simp
        show "Arr' (quotient_proj A R)" using arr_proj.
        show "Arr' f" using arr_f.
        show "snd (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs)) =
    fst (snd (quotient_proj A R))"
          unfolding cop_list_inclusion_def R_def A_def by simp
        show "snd (snd (quotient_proj A R)) = fst (snd f)" using seq by simp

        define S where "S = (list_to_finite_set xs)" 
        have "pointed_finset X S"
          using pointed_list_to_finite_set [OF \<open>pointed_list X xs\<close>]
          unfolding S_def.
        then have EQ2: "f \<cdot> cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) S = cocone S" 
          using f_prop by blast
        have arr_finset_inc: "Arr' (cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) (list_to_finite_set xs))"
          apply (rule_tac cop_finset_inclusion_arr)
          using cocone unfolding Arr'_def apply simp
          using \<open>pointed_finset X S\<close> unfolding S_def.
        have arr_inc2 : "Arr'
     (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
       (finite_set_to_list (list_to_finite_set xs)))"
          apply (rule_tac cop_list_inclusion_arr)
          using list_cocone unfolding Arr'_def apply simp
          using \<open>Obj' X\<close> apply simp
          using pointed_finite_set_to_list [OF pointed_list_to_finite_set [OF \<open>pointed_list X xs\<close>]].

        have list_finset_eq: "list_to_finite_set (finite_set_to_list (list_to_finite_set xs)) =
              list_to_finite_set xs"
          apply (rule_tac list_finset_id)
          using \<open>pointed_finset X S\<close> unfolding S_def by simp

        have EQ: "quotient_proj A R \<cdot>
        cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs = 
        cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) (list_to_finite_set xs)"
          apply (rule_tac comp_eq_char)
          using arr_proj apply simp
          using arr_inc apply simp
          using arr_finset_inc apply simp
             apply (subst cop_finset_inclusion_def)
             apply (subst dom_comp)
          using arr_inc2 apply simp
               apply (rule_tac quot_proj_arr)
          using A_def \<open>Obj' A\<close> apply blast
              apply (simp add: cop_list_inclusion_def coproductOverPointedLists_def)
          using list_finset_eq apply (simp add: cop_list_inclusion_def)
            apply (subst cop_finset_inclusion_def)
            apply (subst cod_comp)
          using arr_inc2 apply simp
               apply (rule_tac quot_proj_arr)
          using A_def \<open>Obj' A\<close> apply blast
             apply (simp add: cop_list_inclusion_def coproductOverPointedLists_def)
            apply (simp add: R_def A_def)
           apply (simp add: cop_list_inclusion_def A_def)
        proof-
          fix x
          assume x_in_inc_dom: "x \<in> snd (fst (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
                             xs)))"
          then have x_in_cocone_dom: "x \<in> snd( Dom' (cocone (list_to_finite_set xs)))"
            unfolding cop_list_inclusion_def by simp
          then have x_in_inc_dom2: "x \<in> snd (fst (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
                           (finite_set_to_list ( list_to_finite_set xs )) )))"
            using list_finset_eq unfolding cop_list_inclusion_def by simp
          have seq : "snd (snd (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
                       (finite_set_to_list (list_to_finite_set xs)))) =
            fst (snd (quotient_proj A R))"
            unfolding cop_list_inclusion_def R_def A_def by simp
          have comp_char : "fst (cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) (list_to_finite_set xs)) x =
                (fst (quotient_proj A R) (fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
                       (finite_set_to_list (list_to_finite_set xs))) x ))"
            unfolding cop_finset_inclusion_def
            apply (subst reverse_equality [OF A_def])
            apply (subst reverse_equality [OF A_def])
            apply (subst reverse_equality [OF R_def])
            unfolding Comp'_def
            using arr_inc2 arr_proj seq 
            using x_in_inc_dom2 by simp

          show "fst (quotient_proj A R)
          (fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs) x) =
         fst (cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) (list_to_finite_set xs)) x"
            apply (subst comp_char)
            apply (rule_tac R_implies_quot_eq)
            using R_equiv apply simp
            unfolding R_def
            apply (subst A_def)
              apply (rule_tac finset_relation_inclusion_intro)
            using list_cocone unfolding Arr'_def apply simp
            using list_finset_eq apply simp
            using \<open>Obj' X\<close> apply simp
            using \<open>pointed_list X xs\<close> apply simp
            using pointed_finite_set_to_list [OF pointed_list_to_finite_set [OF \<open>pointed_list X xs\<close>]] apply simp
            using list_finset_eq apply simp
            using x_in_cocone_dom apply simp
          proof-
            have "fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs) x \<in>
                  snd (Cod' (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs))"
              using arr_inc unfolding Arr'_def setcat.Arr_def
              using x_in_inc_dom by auto
            then show "fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs) x \<in> snd A"
              unfolding A_def cop_list_inclusion_def by simp
            have "fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
          (finite_set_to_list (list_to_finite_set xs))) x
    \<in> snd (Cod' (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
          (finite_set_to_list (list_to_finite_set xs))))"
              using arr_inc2 unfolding Arr'_def setcat.Arr_def
              using x_in_inc_dom2 by auto
            then show "fst (cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs))))
          (finite_set_to_list (list_to_finite_set xs))) x \<in> snd A"
              unfolding A_def cop_list_inclusion_def by simp
          qed
        qed
          
        show "f \<cdot> quotient_proj A R \<cdot>
        cop_list_inclusion X (\<lambda>xs. fst (snd (cocone (list_to_finite_set xs)))) xs =
      cocone (list_to_finite_set xs)"
          apply (subst EQ)
          using EQ2 unfolding S_def.
      qed
    qed
  qed
qed



lemma coprod_finset_UP : assumes
       cocone: "\<forall>A. pointed_finset X A \<longrightarrow> Arr' (cocone A) \<and> Cod' (cocone A) = Z"
            "Obj' X" "Obj' Z" 
     shows "\<exists>! f. Arr' f \<and> 
            Dom' f = (coproductOverFinsets X (\<lambda>B. Dom' (cocone B))) \<and> 
            Cod' f = Z \<and>
           (\<forall>A. pointed_finset X A 
   \<longrightarrow> f \<cdot> (cop_finset_inclusion X (\<lambda>B. Dom' (cocone B)) A) = cocone A)"
proof
  show "Arr' (coprod_finset_UP_map X cocone Z) \<and> 
            Dom' (coprod_finset_UP_map X cocone Z) = (coproductOverFinsets X (\<lambda>B. Dom' (cocone B))) \<and> 
            Cod' (coprod_finset_UP_map X cocone Z) = Z \<and>
           (\<forall>A. pointed_finset X A 
   \<longrightarrow> (coprod_finset_UP_map X cocone Z) \<cdot> (cop_finset_inclusion X (\<lambda>B. Dom' (cocone B)) A) = cocone A)"
    using coprod_finset_UP_existence [OF cocone].
  show "\<And>f. Arr' f \<and>
         fst (snd f) = coproductOverFinsets X (\<lambda>B. fst (snd (cocone B))) \<and>
         snd (snd f) = Z \<and>
         (\<forall>A. pointed_finset X A \<longrightarrow>
              f \<cdot> cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) A = cocone A) \<Longrightarrow>
         f = coprod_finset_UP_map X cocone Z"
    using coprod_finset_UP_uniqueness [OF cocone].
qed







section "More pointed set theory"

interpretation CC: classical_category Obj' Arr' Dom' Cod' Id' Comp'
  using ccpf.

definition pointed_set_comp where "pointed_set_comp = CC.comp"


lemma is_category: "category pointed_set_comp"
  unfolding pointed_set_comp_def
  by (simp add: CC.induces_category)  

definition MkArr :: "'a pointed_set \<Rightarrow> 'a pointed_set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow>
                    ('a \<Rightarrow> 'a) \<times> 'a pointed_set \<times> 'a pointed_set" where
  "MkArr A B F \<equiv> (restrict F (snd A), (A, B))"



lemma arr_char : "partial_magma.arr pointed_set_comp f =
       (f \<noteq> None \<and> Arr' (the f))"
  unfolding pointed_set_comp_def
  using CC.arr_char.

lemma dom_char : "partial_magma.arr pointed_set_comp f \<Longrightarrow>
        partial_magma.dom pointed_set_comp f =
        Some (Id' (fst (snd (the f))))"
  unfolding pointed_set_comp_def 
  apply (subst classical_category.dom_char)
  using ccpf apply blast
  by simp

lemma reverse_dom_char : "partial_magma.arr pointed_set_comp f \<Longrightarrow>
        Some (Id' (fst (snd (the f)))) = 
        partial_magma.dom pointed_set_comp f"
  by (simp add: dom_char)

lemma cod_char : "partial_magma.arr pointed_set_comp f \<Longrightarrow>
         partial_magma.cod pointed_set_comp f = 
         Some (Id' (snd (snd (the f))))"
  unfolding pointed_set_comp_def
  apply (subst classical_category.cod_char)
  using ccpf apply blast
  by simp

lemma reverse_cod_char : "partial_magma.arr pointed_set_comp f \<Longrightarrow>
         Some (Id' (snd (snd (the f)))) =
         partial_magma.cod pointed_set_comp f"
  by (simp add: cod_char)


lemma seq_char : "partial_magma.arr pointed_set_comp f \<Longrightarrow>
                  partial_magma.arr pointed_set_comp g \<Longrightarrow>
                  partial_magma.dom pointed_set_comp g =
                  partial_magma.cod pointed_set_comp f \<Longrightarrow>
     fst (snd (the g)) = snd (snd (the f))"
proof-
  assume arr_f : "partial_magma.arr pointed_set_comp f"
  assume arr_g : "partial_magma.arr pointed_set_comp g"
  assume seq : "partial_magma.dom pointed_set_comp g =
                  partial_magma.cod pointed_set_comp f"

  have "Some (Id' (fst (snd (the g)))) = Some (Id' ( snd (snd (the f))))"
    apply (subst reverse_dom_char)
    apply (simp add: arr_g)
    apply (subst reverse_cod_char)
     apply (simp add: arr_f)
    using seq.
  then show "fst (snd (the g)) = snd (snd (the f))"
    unfolding Id'_def by simp
qed

lemma ide_char : "partial_magma.ide pointed_set_comp f =
              (Arr' (the f) \<and> (f = Some (Id' (Dom' (the f)))))"
  unfolding pointed_set_comp_def
  using classical_category.ide_char [OF ccpf].
  


lemma comp_char : "partial_magma.arr pointed_set_comp f \<Longrightarrow>
             partial_magma.arr pointed_set_comp g \<Longrightarrow>
             partial_magma.dom pointed_set_comp g = partial_magma.cod pointed_set_comp f \<Longrightarrow>
          pointed_set_comp g f = Some (Comp' (the g) (the f))"
  unfolding pointed_set_comp_def
  apply (subst classical_category.comp_char)
  using ccpf apply blast
proof-
  have H1: "CC.arr f \<longrightarrow>
    CC.arr g \<longrightarrow>
    CC.dom g = CC.cod f \<longrightarrow>
    f \<noteq> None \<and> g \<noteq> None"
    apply (subst classical_category.arr_char)
    using ccpf apply blast
    apply (subst classical_category.arr_char)
    using ccpf apply blast
    by simp

    have H2: "CC.arr f \<longrightarrow>
    CC.arr g \<longrightarrow>
    CC.dom g = CC.cod f \<longrightarrow> CC.Seq (the g) (the f)"
    apply (subst classical_category.dom_char)
    using ccpf apply blast
    apply (subst classical_category.cod_char)
    using ccpf apply blast
    apply auto
    using CC.arr_char apply blast
    using CC.arr_char apply blast
    unfolding Id'_def by auto

  from H1 and H2 show "CC.arr f \<Longrightarrow>
    CC.arr g \<Longrightarrow>
    CC.dom g = CC.cod f \<Longrightarrow>
    (if f \<noteq> None \<and> g \<noteq> None \<and> CC.Seq (the g) (the f) then Some (the g \<cdot> the f) else None) =
    Some (the g \<cdot> the f)"
    by auto
qed


definition FiniteArr' where
  "FiniteArr' t \<equiv> partial_magma.arr pointed_set_comp t \<and>
                  finite (snd (Dom' (the t))) \<and>
                  finite (snd (Cod' (the t)))"


lemma finite_subcat : "subcategory pointed_set_comp FiniteArr'"
  unfolding subcategory_def
  apply (simp add: is_category)
  unfolding subcategory_axioms_def apply auto
proof-
  fix f
  assume "FiniteArr' f"
  then show arr_f: "partial_magma.arr pointed_set_comp f"
    unfolding FiniteArr'_def by simp
  then have arr_f2 : "Arr' (the f)" using arr_char by blast
  from \<open>FiniteArr' f\<close> have dom_fin : "finite (snd (Dom' (the f)))"
    unfolding FiniteArr'_def by simp
  from \<open>FiniteArr' f\<close> have cod_fin : "finite (snd (Cod' (the f)))"
    unfolding FiniteArr'_def by simp
  show "FiniteArr' (partial_magma.dom pointed_set_comp f)"
    unfolding FiniteArr'_def
    apply (simp add: arr_f category.arr_dom pointed_set.is_category)
    using arr_f apply (simp add: dom_char)
    unfolding Id'_def apply simp
    by (simp add: dom_fin)
  show "FiniteArr' (partial_magma.cod pointed_set_comp f)"
    unfolding FiniteArr'_def
    apply (simp add: arr_f category.arr_cod pointed_set.is_category)
    using arr_f apply (simp add: cod_char)
    unfolding Id'_def apply simp
    by (simp add: cod_fin)
  term f
  fix g :: "(('b \<Rightarrow> 'b) \<times> ('b \<times> 'b set) \<times> 'b \<times> 'b set) option"
  assume "FiniteArr' g"
  then have arr_g: "partial_magma.arr pointed_set_comp g"
    unfolding FiniteArr'_def by simp
  then have arr_g2: "Arr' (the g)" using arr_char by blast
  from \<open>FiniteArr' g\<close> have cod_fin_g : "finite (snd (Cod' (the g)))"
    unfolding FiniteArr'_def by simp
  assume seq: "partial_magma.cod pointed_set_comp f = partial_magma.dom pointed_set_comp g"
  then have "Some (Id' (Cod' (the f))) = Some (Id' (Dom' (the g)))"
    using arr_f apply (simp add: cod_char)
    using arr_g by (simp add: dom_char)
  then have seq2: "Cod' (the f) = Dom' (the g)"
    unfolding Id'_def by simp
  show "FiniteArr' (pointed_set_comp g f)"
    unfolding FiniteArr'_def apply auto
    using arr_f arr_g seq apply (simp add: category.seqI pointed_set.is_category)
    using arr_f arr_g seq apply (simp add: comp_char)
    using arr_f2 arr_g2 seq2 apply simp
    apply (simp add: dom_fin)
    using arr_f arr_g seq apply (simp add: comp_char)
    using arr_f2 arr_g2 seq2 apply simp
    by (simp add: cod_fin_g)
qed


definition pointed_finite_subcat where
  "pointed_finite_subcat \<equiv> subcategory.comp pointed_set_comp FiniteArr'"

lemma finite_subcat_is_category : "category pointed_finite_subcat"
  unfolding pointed_finite_subcat_def
  using subcategory.is_category [OF finite_subcat]
  by simp


end


section "Colimit over finite sets"

definition generated_equiv_rel where
  "generated_equiv_rel A R x y = (\<forall> Q. equiv A {(x,y). Q x y} \<longrightarrow> (\<forall>x y. R x y \<longrightarrow> Q x y) \<longrightarrow> Q x y)"

lemma generated_equiv_rel_equiv : assumes "{(x,y). R x y} \<subseteq> A \<times> A"
  shows "equiv A {(x,y). generated_equiv_rel A R x y}"
  unfolding equiv_def refl_on_def sym_def trans_def
  apply safe
proof-
  define Q where "Q = (\<lambda>x y. x \<in> A \<and> y \<in> A)"
  have Q_equiv: "equiv A {(x,y). Q x y}"
    unfolding Q_def equiv_def refl_on_def sym_def trans_def by simp
  have RQ: "(\<forall>x y. R x y \<longrightarrow> Q x y)"
    unfolding Q_def
    using \<open>{(x,y). R x y} \<subseteq> A \<times> A\<close> by auto
  fix a b
  assume "generated_equiv_rel A R a b"
  then have "Q a b"
    unfolding generated_equiv_rel_def
    using Q_equiv RQ by blast
  then show "a \<in> A" unfolding Q_def by simp
  from \<open>Q a b\<close> show "b \<in> A" unfolding Q_def by simp
next
  fix x
  assume "x \<in> A"
  show "generated_equiv_rel A R x x"
    unfolding generated_equiv_rel_def equiv_def refl_on_def
    using \<open>x \<in> A\<close> by simp
next
  show "\<And>x y. generated_equiv_rel A R x y \<Longrightarrow> generated_equiv_rel A R y x"
    unfolding generated_equiv_rel_def apply auto
    unfolding equiv_def sym_def by blast
  show "\<And>x y z.
       generated_equiv_rel A R x y \<Longrightarrow> generated_equiv_rel A R y z \<Longrightarrow> generated_equiv_rel A R x z"
    unfolding generated_equiv_rel_def apply auto
    unfolding equiv_def trans_def by blast
qed


definition pointed_finset_triangle where
  "pointed_finset_triangle X S T = (pointed_finset X S \<and> pointed_finset X T \<and> (snd S) \<subseteq> (snd T))"

definition finset_arrow_collection where
  "finset_arrow_collection X A F = (\<forall>S T. pointed_finset_triangle X S T 
             \<longrightarrow> Arr' (F S T) \<and> Dom' (F S T) = A S \<and> Cod' (F S T) = A T)"

definition functor_from_finsets where
  "functor_from_finsets X A F = (finset_arrow_collection X A F \<and>
             (\<forall> S. pointed_finset X S \<longrightarrow> (F S S) = Id' (A S)) \<and>
             (\<forall>S T U. pointed_finset_triangle X S T \<and> pointed_finset_triangle X T U
             \<longrightarrow> (F T U) \<cdot> (F S T) = F S U))" 

definition colimit_prerelation where
  "colimit_prerelation X A F x y = (\<exists> S T a b. pointed_finset_triangle X S T \<and>
                               a \<in> snd (A S) \<and> b \<in> snd (A T) \<and>
                               x = fst (cop_finset_inclusion X A S) a \<and> 
                               y = fst (cop_finset_inclusion X A T) b \<and> 
                               fst (F S T) a = b)"


definition colimit_relation where
  "colimit_relation X A F = (generated_equiv_rel (snd (coproductOverFinsets X A)) 
          (colimit_prerelation X A F))" 

lemma colimit_relation_equiv : 
  assumes A_obj: "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A S)"
  shows  "equiv (snd (coproductOverFinsets X A))
     {(x, y). colimit_relation X A F x y}"
  unfolding colimit_relation_def
  apply (rule_tac generated_equiv_rel_equiv)
  unfolding colimit_prerelation_def apply auto
proof-
  fix s S t T a
  assume "pointed_finset_triangle X (s, S) (t, T)"
  then have pfs : "pointed_finset X (s, S)"
    unfolding pointed_finset_triangle_def
    by simp
  from \<open>pointed_finset_triangle X (s, S) (t, T)\<close>
  have pft : "pointed_finset X (t, T)"
    unfolding pointed_finset_triangle_def
    by simp
  assume "a \<in> snd (A (s, S))"
  then have a_in_dom: "a \<in> snd (Dom' (cop_finset_inclusion X A (s, S)))"
    using cop_finset_inclusion_dom [OF A_obj pfs] by simp
  assume "fst (F (s, S) (t, T)) a \<in> snd (A (t, T))"
  then have fa_in_dom : "fst (F (s, S) (t, T)) a \<in> snd (Dom' (cop_finset_inclusion X A (t, T)))"
    using cop_finset_inclusion_dom [OF A_obj pft] by simp

  show "fst (cop_finset_inclusion X A (s, S)) a \<in>
          snd (coproductOverFinsets X A)"
    apply (subst reverse_equality [OF cop_finset_inclusion_cod [OF A_obj pfs]])
    using cop_finset_inclusion_arr [OF A_obj pfs]
    unfolding Arr'_def setcat.Arr_def
    using a_in_dom by auto
  show "fst (cop_finset_inclusion X A (t, T)) (fst (F (s, S) (t, T)) a) \<in>
          snd (coproductOverFinsets X A)"
    apply (subst reverse_equality [OF cop_finset_inclusion_cod [OF A_obj pft]])
    using cop_finset_inclusion_arr [OF A_obj pft]
    unfolding Arr'_def setcat.Arr_def
    using fa_in_dom by auto
qed





definition colimitOverFinsets :: "'a LC pointed_set \<Rightarrow> ('a LC pointed_set \<Rightarrow> 'a LC pointed_set) \<Rightarrow> 
                           ('a LC pointed_set \<Rightarrow> 'a LC pointed_set \<Rightarrow> 'a LC parr) \<Rightarrow> 'a LC pointed_set" where
  "colimitOverFinsets X A F = 
         quotient_by_equiv_rel
         (coproductOverFinsets X A)
          (colimit_relation X A F)"

lemma colimitOverFinsets_obj : 
  assumes cocone : "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A S)"
     and "Obj' X"
  shows "Obj' (colimitOverFinsets X A F)"
  unfolding colimitOverFinsets_def
proof-
  have arr_proj: "Arr' (quotient_proj (coproductOverFinsets X A)
          (colimit_relation X A F))" 
    apply (rule_tac quot_proj_arr)
    by (rule_tac cop_finset_obj [OF cocone \<open>Obj' X\<close>])
  have "Obj' (Cod' (quotient_proj (coproductOverFinsets X A) (colimit_relation X A F)))"
    using classical_category.Obj_Cod [OF ccpf arr_proj].
  then show "Obj'
     (quotient_by_equiv_rel (coproductOverFinsets X A)
       (colimit_relation X A F))"
    by simp
qed


definition colim_finset_inclusion :: "'a LC pointed_set \<Rightarrow> ('a LC pointed_set \<Rightarrow> 'a LC pointed_set) \<Rightarrow> 
            ('a LC pointed_set \<Rightarrow> 'a LC pointed_set \<Rightarrow> 'a LC parr) \<Rightarrow>'a LC pointed_set \<Rightarrow> 'a LC parr" where
   "colim_finset_inclusion X A F S = Comp' (quotient_proj (coproductOverFinsets X A) (colimit_relation X A F))
                                (cop_finset_inclusion X A S)"

definition colim_finset_UP_map :: "'a LC pointed_set \<Rightarrow> ('a LC pointed_set \<Rightarrow> 'a LC parr) \<Rightarrow> 
            ('a LC pointed_set \<Rightarrow> 'a LC pointed_set \<Rightarrow> 'a LC parr) \<Rightarrow> 'a LC pointed_set \<Rightarrow> 'a LC parr" where
  "colim_finset_UP_map X cocone F Z = Comp' (coprod_finset_UP_map X cocone Z) 
          (quotient_section (coproductOverFinsets X (\<lambda>k. Dom' (cocone k))) 
          (colimit_relation X (\<lambda>k. Dom' (cocone k)) F))"







lemma colim_finset_inclusion_arr : assumes
      cocone_obj: "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A S)"
   and "pointed_finset X S" 
      shows "Arr' (colim_finset_inclusion X A F S)"
  unfolding colim_finset_inclusion_def
  apply (rule_tac comp_arr)
    apply (rule_tac quot_proj_arr)
    apply (rule_tac cop_finset_obj [OF cocone_obj pointed_finset_obj [OF \<open>pointed_finset X S\<close>]])
   apply (rule_tac cop_finset_inclusion_arr [OF cocone_obj \<open>pointed_finset X S\<close>])
  apply (subst cop_finset_inclusion_cod [OF cocone_obj \<open>pointed_finset X S\<close>])
  by simp


lemma colim_finset_inclusion_dom: 
  assumes cocone_obj: "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A S)"
  and "pointed_finset X S" 
  shows "Dom' (colim_finset_inclusion X A F S) = A S"
  unfolding colim_finset_inclusion_def
  apply (subst dom_comp)
     apply (rule_tac cop_finset_inclusion_arr)
  using cocone_obj apply simp
  using \<open>pointed_finset X S\<close> apply simp
    apply (rule_tac quot_proj_arr)
  apply (rule_tac cop_finset_obj)
  using cocone_obj apply simp
  using pointed_finset_obj [OF \<open>pointed_finset X S\<close>] apply simp
  using cop_finset_inclusion_cod [OF cocone_obj \<open>pointed_finset X S\<close>] apply simp
  using cop_finset_inclusion_dom [OF cocone_obj \<open>pointed_finset X S\<close>].

lemma colim_finset_inclusion_cod: 
  assumes cocone_obj: "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A S)"
  and "pointed_finset X S" 
  shows "Cod' (colim_finset_inclusion X A F S) = colimitOverFinsets X A F"
  unfolding colim_finset_inclusion_def
  apply (subst cod_comp)
     apply (rule_tac cop_finset_inclusion_arr)
  using cocone_obj apply simp
  using \<open>pointed_finset X S\<close> apply simp
    apply (rule_tac quot_proj_arr)
  apply (rule_tac cop_finset_obj)
  using cocone_obj apply simp
  using pointed_finset_obj [OF \<open>pointed_finset X S\<close>] apply simp
  using cop_finset_inclusion_cod [OF cocone_obj \<open>pointed_finset X S\<close>] apply simp
  unfolding colimitOverFinsets_def by simp



lemma colim_finset_UP_map_arr : assumes
      cocone_obj: "\<forall>S. pointed_finset X S \<longrightarrow> 
                 Arr' (cocone S) \<and> Dom' (cocone S) = A S \<and> Cod' (cocone S) = Z"
     and "Obj' X" "Obj' Z" 
   shows "Arr' (colim_finset_UP_map X cocone F Z)"
  unfolding colim_finset_UP_map_def
  apply (rule_tac comp_arr)
    apply (rule_tac coprod_finset_UP_map_arr)
  using cocone_obj apply simp
  using \<open>Obj' X\<close> apply simp
  using \<open>Obj' Z\<close> apply simp
   apply (rule_tac quot_sec_arr)
    apply (rule_tac colimit_relation_equiv)
  using cocone_obj
  unfolding Arr'_def apply blast
   apply (rule_tac cop_finset_obj)
  using cocone_obj unfolding Arr'_def apply blast
  using \<open>Obj' X\<close> apply simp
  apply (subst coprod_finset_UP_map_dom)
  using cocone_obj apply simp
  using \<open>Obj' X\<close> apply simp
  using \<open>Obj' Z\<close> apply simp
  by simp


lemma colim_relation_x_in_coprod :
  assumes "colimit_prerelation X D F x y"
  and D_obj : "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (D S)"
  shows "x \<in> snd (coproductOverFinsets X D) \<and>
         y \<in> snd (coproductOverFinsets X D)"
proof
  obtain S T a b where ST_def: "pointed_finset_triangle X S T \<and>
     a \<in> snd (D S) \<and>
     b \<in> snd (D T) \<and>
     x = fst (cop_finset_inclusion X D S) a \<and>
     y = fst (cop_finset_inclusion X D T) b \<and> fst (F S T) a = b"
    using \<open>colimit_prerelation X D F x y\<close>
    unfolding colimit_prerelation_def by auto
  from ST_def show "x \<in> snd (coproductOverFinsets X D)"
  proof-
    have a_in_dom: "a \<in> snd (Dom' (cop_finset_inclusion X D S))"
      apply (subst cop_finset_inclusion_dom)
      apply (simp add: D_obj)
      using ST_def
      unfolding pointed_finset_triangle_def apply simp
      using ST_def by simp
    have pfs : "pointed_finset X S"
      using ST_def
      unfolding pointed_finset_triangle_def by simp
    show "x \<in> snd (coproductOverFinsets X D)"
      apply (simp add: ST_def)
      apply (subst reverse_equality [OF cop_finset_inclusion_cod])
        apply (simp add: D_obj)
      using pfs apply simp
      using cop_finset_inclusion_arr [OF D_obj pfs]
      unfolding Arr'_def setcat.Arr_def
      using a_in_dom by auto
  qed
  from ST_def show "y \<in> snd (coproductOverFinsets X D)" 
  proof-
    have b_in_dom: "b \<in> snd (Dom' (cop_finset_inclusion X D T))"
      apply (subst cop_finset_inclusion_dom)
      apply (simp add: D_obj)
      using ST_def
      unfolding pointed_finset_triangle_def apply simp
      using ST_def by simp
    have pft : "pointed_finset X T"
      using ST_def
      unfolding pointed_finset_triangle_def by simp
    show "y \<in> snd (coproductOverFinsets X D)"
      apply (simp add: ST_def)
      apply (subst reverse_equality [OF cop_finset_inclusion_cod])
        apply (simp add: D_obj)
      using pft apply simp
      using cop_finset_inclusion_arr [OF D_obj pft]
      unfolding Arr'_def setcat.Arr_def
      using b_in_dom by auto
  qed
qed



lemma colim_relation_up_map_eq : 
  assumes 
      cocone_obj: "\<forall>S. pointed_finset X S \<longrightarrow> Arr' (cocone S) \<and> 
                       Cod' (cocone S) = Z" 
  and cocone_arr: "\<forall> S T. pointed_finset_triangle X S T \<longrightarrow>
                   cocone T \<cdot> (F S T) = cocone S"
  and    "colimit_prerelation X (\<lambda>k. Dom' (cocone k)) F x y"
  and functoriality: "finset_arrow_collection X (\<lambda>k. Dom' (cocone k)) F"
  and "Obj' X" "Obj' Z" 
shows "fst (coprod_finset_UP_map X cocone Z) x =
       fst (coprod_finset_UP_map X cocone Z) y"
proof-
  define D where "D = (\<lambda>k. Dom' (cocone k))"
  have "colimit_prerelation X D F x y"
    unfolding D_def
    using \<open>colimit_prerelation X (\<lambda>k. Dom' (cocone k)) F x y\<close>.
  have D_obj : "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (D S)"
    unfolding D_def
    using cocone_obj
    unfolding Arr'_def by blast

  obtain S T a b where ST_def: "pointed_finset_triangle X S T \<and>
     a \<in> snd (D S) \<and>
     b \<in> snd (D T) \<and>
     x = fst (cop_finset_inclusion X D S) a \<and>
     y = fst (cop_finset_inclusion X D T) b \<and> fst (F S T) a = b"
    using \<open>colimit_prerelation X D F x y\<close>
    unfolding colimit_prerelation_def by auto
  from ST_def have "x \<in> snd (coproductOverFinsets X D)"
    using colim_relation_x_in_coprod [OF \<open>colimit_prerelation X D F x y\<close> D_obj]
    by simp
  then have x_in_cop: "pointed_finset X (cop_finset_index x) \<and>
    cop_finset_value x \<in> snd (D (cop_finset_index x)) \<and>
    fst (cop_finset_inclusion X D (cop_finset_index x)) (cop_finset_value x) = x"
    unfolding D_def
    apply (rule_tac x_in_cop_finset_char)
    using cocone_obj unfolding Arr'_def apply blast
    using \<open>Obj' X\<close> by simp
  from ST_def have "y \<in> snd (coproductOverFinsets X D)" 
    using colim_relation_x_in_coprod [OF \<open>colimit_prerelation X D F x y\<close> D_obj]
    by simp
  then have y_in_cop: "pointed_finset X (cop_finset_index y) \<and>
    cop_finset_value y \<in> snd (D (cop_finset_index y)) \<and>
    fst (cop_finset_inclusion X D (cop_finset_index y)) (cop_finset_value y) = y"
    unfolding D_def
    apply (rule_tac x_in_cop_finset_char)
    using cocone_obj unfolding Arr'_def apply blast
    using \<open>Obj' X\<close> by simp

  have inc_eq_x: " fst (cop_finset_inclusion X D (cop_finset_index x)) (cop_finset_value x) = x"
    using x_in_cop by simp

  have inc_eq_y: " fst (cop_finset_inclusion X D (cop_finset_index y)) (cop_finset_value y) = y"
    using y_in_cop by simp

  have comp_char_x_lemma : "Arr' (cop_finset_inclusion X D (cop_finset_index x)) \<and>
            Arr' (coprod_finset_UP_map X cocone Z) \<and>
            snd (snd (cop_finset_inclusion X D (cop_finset_index x))) =
            fst (snd (coprod_finset_UP_map X cocone Z))"
    apply safe
      apply (rule_tac cop_finset_inclusion_arr)
    unfolding D_def
    using cocone_obj Arr'_def apply blast
    using x_in_cop apply simp
     apply (rule_tac coprod_finset_UP_map_arr)
    using cocone_obj apply simp
    using \<open>Obj' X\<close> apply simp
    using \<open>Obj' Z\<close> apply simp
    apply (subst cop_finset_inclusion_cod)
    using cocone_obj Arr'_def apply blast
    using x_in_cop apply simp
    apply (subst coprod_finset_UP_map_dom)
    using cocone_obj apply simp
    using \<open>Obj' X\<close> \<open>Obj' Z\<close> by simp_all

  have comp_char_y_lemma : "Arr' (cop_finset_inclusion X D (cop_finset_index y)) \<and>
            Arr' (coprod_finset_UP_map X cocone Z) \<and>
            snd (snd (cop_finset_inclusion X D (cop_finset_index y))) =
            fst (snd (coprod_finset_UP_map X cocone Z))"
    apply safe
      apply (rule_tac cop_finset_inclusion_arr)
    unfolding D_def
    using cocone_obj Arr'_def apply blast
    using y_in_cop apply simp
     apply (rule_tac coprod_finset_UP_map_arr)
    using cocone_obj apply simp
    using \<open>Obj' X\<close> apply simp
    using \<open>Obj' Z\<close> apply simp
    apply (subst cop_finset_inclusion_cod)
    using cocone_obj Arr'_def apply blast
    using y_in_cop apply simp
    apply (subst coprod_finset_UP_map_dom)
    using cocone_obj apply simp
    using \<open>Obj' X\<close> \<open>Obj' Z\<close> by simp_all

  have in_dom_x : "cop_list_value x
    \<in> snd (Dom' (cop_finset_inclusion X D
                       (cop_finset_index x)))"
    apply (subst cop_finset_inclusion_dom)
    unfolding D_def
    using cocone_obj Arr'_def apply blast
    using x_in_cop apply simp
    using x_in_cop unfolding D_def by simp

  have in_dom_y : "cop_list_value y
    \<in> snd (Dom' (cop_finset_inclusion X D
                       (cop_finset_index y)))"
    apply (subst cop_finset_inclusion_dom)
    unfolding D_def
    using cocone_obj Arr'_def apply blast
    using y_in_cop apply simp
    using y_in_cop unfolding D_def by simp

  have comp_char_x: "fst (coprod_finset_UP_map X cocone Z) 
  (fst (cop_finset_inclusion X D (cop_finset_index x)) (cop_finset_value x)) =
        fst ((coprod_finset_UP_map X cocone Z) \<cdot> 
       (cop_finset_inclusion X D (cop_finset_index x))) (cop_finset_value x)"
    unfolding Comp'_def
    using comp_char_x_lemma in_dom_x by simp

  have comp_char_y: "fst (coprod_finset_UP_map X cocone Z) 
  (fst (cop_finset_inclusion X D (cop_finset_index y)) (cop_finset_value y)) =
        fst ((coprod_finset_UP_map X cocone Z) \<cdot> 
       (cop_finset_inclusion X D (cop_finset_index y))) (cop_finset_value y)"
    unfolding Comp'_def
    using comp_char_y_lemma in_dom_y by simp

  have UP: "Arr' (coprod_finset_UP_map X cocone Z) \<and>
  fst (snd (coprod_finset_UP_map X cocone Z)) =
  coproductOverFinsets X (\<lambda>B. fst (snd (cocone B))) \<and>
  snd (snd (coprod_finset_UP_map X cocone Z)) = Z \<and>
  (\<forall>S. pointed_finset X S \<longrightarrow>
       coprod_finset_UP_map X cocone Z \<cdot> cop_finset_inclusion X (\<lambda>B. fst (snd (cocone B))) S =
       cocone S)"
    apply (rule_tac coprod_finset_UP_existence)
    using cocone_obj \<open>Obj' X\<close> \<open>Obj' Z\<close> by simp_all
  then have UP_eq_x : "coprod_finset_UP_map X cocone Z \<cdot> cop_finset_inclusion X D (cop_finset_index x) =
                  cocone (cop_finset_index x)"
    unfolding D_def
    using x_in_cop by simp

  from UP have UP_eq_y : "coprod_finset_UP_map X cocone Z \<cdot> cop_finset_inclusion X D (cop_finset_index y) =
                  cocone (cop_finset_index y)"
    unfolding D_def
    using y_in_cop by simp

  have "cocone T \<cdot> F S T = cocone S"
    using cocone_arr ST_def by blast

  have F_comp_char : "Arr' (F S T) \<and> Arr' (cocone T) \<and> snd (snd (F S T)) = fst (snd (cocone T))"
    apply safe
    using functoriality unfolding finset_arrow_collection_def
    using ST_def apply blast
    using cocone_obj ST_def
    unfolding pointed_finset_triangle_def apply blast
    using functoriality
    unfolding finset_arrow_collection_def
    using ST_def
    unfolding pointed_finset_triangle_def by blast

  have "fst (snd (F S T)) = fst (snd (cocone S))"
    using functoriality
    unfolding finset_arrow_collection_def
    using ST_def by blast

  show "fst (coprod_finset_UP_map X cocone Z) x = fst (coprod_finset_UP_map X cocone Z) y"
    apply (subst reverse_equality [OF inc_eq_x])
    apply (subst comp_char_x)
    apply (subst UP_eq_x)
    apply (subst \<open>cop_finset_index x = S\<close>)
    apply (subst reverse_equality [OF \<open>cocone T \<cdot> F S T = cocone S\<close>])
    unfolding Comp'_def
    using F_comp_char val_in_dom apply simp
    using ST_def apply simp
    apply (rule_tac reverse_equality)
    apply (subst reverse_equality [OF inc_eq_y])
    apply (subst comp_char_y)
    apply (subst UP_eq_y)
    using ST_def by simp
qed

lemma coprod_colim_quot_cocone: assumes
      cocone_obj: "\<forall>S. pointed_finset X S \<longrightarrow> 
                 Arr' (cocone S) \<and> Cod' (cocone S) = Z"
  and cocone_arr: "\<forall> S T. pointed_finset_triangle X S T \<longrightarrow>
                   cocone T \<cdot> (F S T) = cocone S"
  and functoriality: "finset_arrow_collection X (\<lambda>k. Dom' (cocone k)) F"
  and "Obj' X" "Obj' Z" 
shows "Arr' (coprod_finset_UP_map X cocone Z) \<and>
                 Dom' (coprod_finset_UP_map X cocone Z) = (coproductOverFinsets X (\<lambda>k. Dom' (cocone k))) \<and>
                 Cod' (coprod_finset_UP_map X cocone Z) = Z \<and>
                 (\<forall>x y. colimit_relation X (\<lambda>k. Dom' (cocone k)) F x y 
    \<longrightarrow> fst (coprod_finset_UP_map X cocone Z) x = fst (coprod_finset_UP_map X cocone Z) y)"
  using coprod_finset_UP_existence [OF cocone_obj \<open>Obj' X\<close> \<open>Obj' Z\<close>] apply simp
proof-
  define cop_f where "cop_f = coprod_finset_UP_map X cocone Z"
  define A where "A = coproductOverFinsets X (\<lambda>k. Dom' (cocone k))"
  define R where "R = colimit_relation X (\<lambda>k. Dom' (cocone k)) F"

  have R_equiv : "equiv (snd A) {(x, y). R x y}"
    unfolding A_def R_def
    apply (rule_tac colimit_relation_equiv)
    using cocone_obj
    unfolding Arr'_def by blast


  define Q where "Q = (\<lambda>x y. x \<in> snd A \<and> y \<in> snd A \<and> fst cop_f x = fst cop_f y)" 

  have Q_equiv : "equiv (snd A) {(x,y). Q x y}"
    unfolding Q_def equiv_def refl_on_def sym_def trans_def by auto
  have QR : "(\<forall>x y. colimit_prerelation X (\<lambda>k. Dom' (cocone k)) F x y \<longrightarrow> Q x y)" 
    unfolding Q_def apply auto
    using colimit_prerelation_def A_def apply blast
    using colimit_prerelation_def A_def apply blast
    unfolding cop_f_def
    apply (rule_tac colim_relation_up_map_eq)
    using cocone_obj apply simp
    using cocone_arr apply simp
    apply simp
    using functoriality apply simp
    using \<open>Obj' X\<close> apply simp
    using \<open>Obj' Z\<close> by simp
  show "\<forall>x y. R x y \<longrightarrow> fst cop_f x = fst cop_f y" 
    unfolding R_def colimit_relation_def generated_equiv_rel_def apply auto
  proof-
    fix x y
    assume "\<forall>Q. equiv (snd (coproductOverFinsets X (\<lambda>k. Dom' (cocone k)))) {(x, y). Q x y} \<longrightarrow>
               (\<forall>x y. colimit_prerelation X (\<lambda>k. Dom' (cocone k)) F x y \<longrightarrow> Q x y) \<longrightarrow> Q x y"
    then have "equiv (snd (coproductOverFinsets X (\<lambda>k. Dom' (cocone k)))) {(x, y). Q x y} \<Longrightarrow>
               (\<forall>x y. colimit_prerelation X (\<lambda>k. Dom' (cocone k)) F x y \<longrightarrow> Q x y) \<Longrightarrow> Q x y" by auto
    then have "Q x y" using Q_equiv QR unfolding A_def by simp
    then show "fst cop_f x = fst cop_f y" unfolding Q_def by simp
  qed
qed


lemma colim_finset_UP_existence :  assumes
      cocone_obj: "\<forall>S. pointed_finset X S \<longrightarrow> 
                 Arr' (cocone S) \<and> Cod' (cocone S) = Z"
  and cocone_arr: "\<forall> S T. pointed_finset_triangle X S T \<longrightarrow>
                   cocone T \<cdot> (F S T) = cocone S"
  and functoriality: "finset_arrow_collection X (\<lambda>k. Dom' (cocone k)) F"
  and "Obj' X" "Obj' Z" 
shows "Arr' (colim_finset_UP_map X cocone F Z) \<and>
       Dom' (colim_finset_UP_map X cocone F Z) = colimitOverFinsets X (\<lambda>k. Dom' (cocone k)) F \<and>
       Cod' (colim_finset_UP_map X cocone F Z) = Z \<and>
       (\<forall>S. pointed_finset X S \<longrightarrow> 
   (colim_finset_UP_map X cocone F Z) \<cdot> (colim_finset_inclusion X (\<lambda>k. Dom' (cocone k)) F S) = cocone S)"
proof-
  define D where "D = (\<lambda>k. Dom' (cocone k))"

  have D_obj : "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (D S)"
    unfolding D_def
    using cocone_obj unfolding Arr'_def by auto

  define cop_f where "cop_f = coprod_finset_UP_map X cocone Z"
  have cop_f_prop: "Arr' cop_f \<and>
  Dom' cop_f = coproductOverFinsets X D \<and>
  Cod' cop_f = Z \<and>
  (\<forall>S. pointed_finset X S \<longrightarrow>
       cop_f \<cdot> cop_finset_inclusion X D S =
       cocone S)"
    unfolding cop_f_def D_def
    using coprod_finset_UP_existence [OF cocone_obj \<open>Obj' X\<close> \<open>Obj' Z\<close>].

  define A where "A = coproductOverFinsets X D"
  define R where "R = colimit_relation X D F"

  have "Obj' A"
    unfolding A_def
    apply (rule_tac cop_finset_obj)
    using D_obj apply simp
    using \<open>Obj' X\<close> by simp

  have R_equiv : "equiv (snd A) {(x, y). R x y}"
    unfolding A_def R_def D_def
    using colimit_relation_equiv.

  have arr_sec: "Arr' (quotient_section A R)"
    apply (rule_tac quot_sec_arr)
    using R_equiv \<open>Obj' A\<close> by simp_all

  have cop_finset_obj: "Obj' (coproductOverFinsets X D)"
    apply (rule_tac cop_finset_obj)
    using D_obj apply simp
    using \<open>Obj' X\<close> by simp

  have quotient_cocone : "Arr' cop_f \<and>
                 Dom' cop_f = A \<and>
                 Cod' cop_f = Z \<and>
                 (\<forall>x y. R x y \<longrightarrow> fst cop_f x = fst cop_f y)"
    using coprod_colim_quot_cocone [OF cocone_obj cocone_arr functoriality \<open>Obj' X\<close> \<open>Obj' Z\<close>]
    unfolding cop_f_def A_def R_def D_def.

  define f where "f = cop_f \<cdot> quotient_section A R" 

  from quotient_UP_existence [OF R_equiv quotient_cocone \<open>Obj' A\<close>]
  have f_prop: "Arr' f \<and>
       fst (snd f) = quotient_by_equiv_rel A R \<and> snd (snd f) = Z \<and> f \<cdot> quotient_proj A R = cop_f"
    unfolding f_def.

  have f_is_UP_map : "f = colim_finset_UP_map X cocone F Z"
    unfolding f_def cop_f_def colim_finset_UP_map_def A_def R_def D_def
    by (rule_tac refl)


  have "Arr' f \<and>
        Dom' f = colimitOverFinsets X D F \<and>
        Cod' f = Z \<and>
        (\<forall>S. pointed_finset X S \<longrightarrow> f \<cdot> colim_finset_inclusion X D F S = cocone S)"
    using f_prop
    unfolding colimitOverFinsets_def A_def R_def apply safe
  proof-
    fix a A
    assume "pointed_finset X (a, A)"

    have arr_inc: " Arr' (colim_finset_inclusion X D F (a, A))"
      apply (rule_tac colim_finset_inclusion_arr)
      using D_obj apply simp
      using \<open>pointed_finset X (a, A)\<close>.

    have sec_inc_comp_char : 
           "Arr' (quotient_section (coproductOverFinsets X D) R) \<and>
             Arr' (colim_finset_inclusion X (\<lambda>k. fst (snd (cocone k))) F (a, A)) \<and>
            fst (snd (quotient_section (coproductOverFinsets X D) R)) =
    snd (snd (colim_finset_inclusion X (\<lambda>k. fst (snd (cocone k))) F (a, A)))"
      apply safe
      using arr_sec unfolding A_def apply simp
      using arr_inc unfolding D_def apply simp
      apply (subst colim_finset_inclusion_cod)
      using D_obj D_def apply simp
      using \<open>pointed_finset X (a, A)\<close> apply simp
      unfolding colimitOverFinsets_def R_def D_def by simp

    have arr_sec_inc: "Arr'
     (quotient_section (coproductOverFinsets X D) R \<cdot>
      colim_finset_inclusion X (\<lambda>k. fst (snd (cocone k))) F (a, A))"
      apply (rule_tac comp_arr)
      using sec_inc_comp_char apply blast
      using sec_inc_comp_char apply blast
      using sec_inc_comp_char by blast


    show "f \<cdot> colim_finset_inclusion X D F (a, A) = cocone (a, A)"
      unfolding colim_finset_inclusion_def
      apply (subst reverse_equality [OF classical_category.Comp_assoc [OF ccpf]])
           apply (rule_tac cop_finset_inclusion_arr [OF D_obj \<open>pointed_finset X (a, A)\<close>])
          apply (rule_tac quot_proj_arr [OF cop_finset_obj])
      using f_prop apply simp
      using cop_finset_inclusion_cod [OF D_obj \<open>pointed_finset X (a, A)\<close>] apply simp
      using f_prop A_def R_def apply simp
    proof-
      show "(f \<cdot> quotient_proj (coproductOverFinsets X D) (colimit_relation X D F)) \<cdot>
    cop_finset_inclusion X D (a, A) =
    cocone (a, A)"
        unfolding reverse_equality [OF A_def] reverse_equality [OF R_def]
        using f_prop apply simp
        using cop_f_prop \<open>pointed_finset X (a, A)\<close> by simp
    qed
  qed

  then show "Arr' (colim_finset_UP_map X cocone F Z) \<and>
    fst (snd (colim_finset_UP_map X cocone F Z)) =
    colimitOverFinsets X (\<lambda>k. fst (snd (cocone k))) F \<and>
    snd (snd (colim_finset_UP_map X cocone F Z)) = Z \<and>
    (\<forall>S. pointed_finset X S \<longrightarrow>
         colim_finset_UP_map X cocone F Z \<cdot>
         colim_finset_inclusion X (\<lambda>k. fst (snd (cocone k))) F S =
         cocone S)"
    unfolding reverse_equality [OF D_def]
              reverse_equality [OF f_is_UP_map].
qed


lemma colim_finset_UP_uniqueness : assumes
      cocone_obj: "\<forall>S. pointed_finset X S \<longrightarrow> 
                 Arr' (cocone S) \<and> Cod' (cocone S) = Z"
  and cocone_arr: "\<forall> S T. pointed_finset_triangle X S T \<longrightarrow>
                   cocone T \<cdot> (F S T) = cocone S"
  and functoriality: "finset_arrow_collection X (\<lambda>k. Dom' (cocone k)) F"
  and "Obj' X" "Obj' Z" 

  shows "\<And>f. Arr' f \<and>
         fst (snd f) = colimitOverFinsets X (\<lambda>k. fst (snd (cocone k))) F \<and>
         snd (snd f) = Z \<and>
         (\<forall>S. pointed_finset X S \<longrightarrow>
              f \<cdot> colim_finset_inclusion X (\<lambda>k. fst (snd (cocone k))) F S = cocone S) \<Longrightarrow>
         f = colim_finset_UP_map X cocone F Z"
proof-
  fix f
  assume f_prop: "Arr' f \<and>
         fst (snd f) = colimitOverFinsets X (\<lambda>k. fst (snd (cocone k))) F \<and>
         snd (snd f) = Z \<and>
         (\<forall>S. pointed_finset X S \<longrightarrow>
              f \<cdot> colim_finset_inclusion X (\<lambda>k. fst (snd (cocone k))) F S = cocone S)"

  define D where "D = (\<lambda>k. Dom' (cocone k))"

  have D_obj : "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (D S)"
    unfolding D_def
    using cocone_obj unfolding Arr'_def by auto

  define cop_f where "cop_f = coprod_finset_UP_map X cocone Z"
  have cop_f_prop: "Arr' cop_f \<and>
  Dom' cop_f = coproductOverFinsets X D \<and>
  Cod' cop_f = Z \<and>
  (\<forall>S. pointed_finset X S \<longrightarrow>
       cop_f \<cdot> cop_finset_inclusion X D S =
       cocone S)"
    unfolding cop_f_def D_def
    using coprod_finset_UP_existence [OF cocone_obj \<open>Obj' X\<close> \<open>Obj' Z\<close>].

  define A where "A = coproductOverFinsets X D"
  define R where "R = colimit_relation X D F"

  have "Obj' A"
    unfolding A_def
    apply (rule_tac cop_finset_obj)
    using D_obj apply simp
    using \<open>Obj' X\<close> by simp

  have R_equiv : "equiv (snd A) {(x, y). R x y}"
    unfolding A_def R_def D_def
    using colimit_relation_equiv.

  have arr_sec: "Arr' (quotient_section A R)"
    apply (rule_tac quot_sec_arr)
    using R_equiv \<open>Obj' A\<close> by simp_all

  have cop_finset_obj: "Obj' (coproductOverFinsets X D)"
    apply (rule_tac cop_finset_obj)
    using D_obj apply simp
    using \<open>Obj' X\<close> by simp

  have quotient_cocone : "Arr' cop_f \<and>
                 Dom' cop_f = A \<and>
                 Cod' cop_f = Z \<and>
                 (\<forall>x y. R x y \<longrightarrow> fst cop_f x = fst cop_f y)"
    using coprod_colim_quot_cocone [OF cocone_obj cocone_arr functoriality \<open>Obj' X\<close> \<open>Obj' Z\<close>]
    unfolding cop_f_def A_def R_def D_def.

  show "f = colim_finset_UP_map X cocone F Z"
    unfolding colim_finset_UP_map_def
              reverse_equality [OF cop_f_def]
              reverse_equality [OF D_def]
              reverse_equality [OF A_def]
              reverse_equality [OF R_def]
    apply (rule_tac quotient_UP_uniqueness [OF R_equiv quotient_cocone \<open>Obj' A\<close>])
    using f_prop unfolding colimitOverFinsets_def
              reverse_equality [OF D_def]
              reverse_equality [OF A_def]
              reverse_equality [OF R_def] apply safe
  proof-
    show "f \<cdot> quotient_proj A R = cop_f"
      unfolding cop_f_def A_def R_def D_def
      apply (rule_tac coprod_finset_UP_uniqueness [OF cocone_obj \<open>Obj' X\<close> \<open>Obj' Z\<close>])
      unfolding reverse_equality [OF cop_f_def]
                reverse_equality [OF D_def]
                reverse_equality [OF A_def]
                reverse_equality [OF R_def] apply safe
    proof-
      have arr_f: "Arr' f" using f_prop by simp
      have arr_proj: "Arr' (quotient_proj A R)" using quot_proj_arr [OF \<open>Obj' A\<close>].
      have seq: "Dom' f = Cod' (quotient_proj A R)"
        using f_prop unfolding A_def R_def D_def colimitOverFinsets_def by simp
      show "Arr' (f \<cdot> quotient_proj A R)"
        using comp_arr [OF arr_f arr_proj seq].
      show "fst (snd (f \<cdot> quotient_proj A R)) = A"
        using dom_comp [OF arr_proj arr_f reverse_equality [OF seq]] by simp
      show "snd (snd (f \<cdot> quotient_proj A R)) = Z"
        using cod_comp [OF arr_proj arr_f reverse_equality [OF seq]] f_prop by simp
      fix y Y
      assume "pointed_finset X (y, Y)"
      have arr_inc : "Arr' (cop_finset_inclusion X D (y, Y))"
        using cop_finset_inclusion_arr [OF D_obj \<open>pointed_finset X (y, Y)\<close>].
      have inc_proj_seq : "snd (snd (cop_finset_inclusion X D (y, Y))) = fst (snd (quotient_proj A R))"
        using cop_finset_inclusion_cod [OF D_obj \<open>pointed_finset X (y, Y)\<close>]
        unfolding A_def by simp
      show "(f \<cdot> quotient_proj A R) \<cdot> cop_finset_inclusion X D (y, Y) = cocone (y, Y)"
        apply (subst classical_category.Comp_assoc [OF ccpf arr_inc arr_proj arr_f inc_proj_seq reverse_equality [OF seq]])
        unfolding A_def R_def
                  reverse_equality [OF colim_finset_inclusion_def]
                  D_def
        using f_prop \<open>pointed_finset X (y, Y)\<close> by simp
    qed
  qed
qed




lemma colim_finset_UP : assumes
      cocone_obj: "\<forall>S. pointed_finset X S \<longrightarrow> 
                 Arr' (cocone S) \<and> Cod' (cocone S) = Z"
  and cocone_arr: "\<forall> S T. pointed_finset_triangle X S T \<longrightarrow>
                   cocone T \<cdot> (F S T) = cocone S"
  and functoriality: "finset_arrow_collection X (\<lambda>k. Dom' (cocone k)) F"
  and "Obj' X" "Obj' Z" 
    shows "\<exists>! f. Arr' f \<and> Dom' f = colimitOverFinsets X (\<lambda>k. Dom' (cocone k)) F \<and> Cod' f = Z \<and>
            (\<forall>S. pointed_finset X S \<longrightarrow> f \<cdot> (colim_finset_inclusion X (\<lambda>k. Dom' (cocone k)) F S) = cocone S)"
proof
  show "Arr' (colim_finset_UP_map X cocone F Z) \<and>
    fst (snd (colim_finset_UP_map X cocone F Z)) = colimitOverFinsets X (\<lambda>k. fst (snd (cocone k))) F \<and>
    snd (snd (colim_finset_UP_map X cocone F Z)) = Z \<and>
    (\<forall>S. pointed_finset X S \<longrightarrow> (colim_finset_UP_map X cocone F Z) \<cdot> 
     colim_finset_inclusion X (\<lambda>k. fst (snd (cocone k))) F S = cocone S)"
    using colim_finset_UP_existence [OF cocone_obj cocone_arr functoriality \<open>Obj' X\<close> \<open>Obj' Z\<close>].
  show "\<And>f. Arr' f \<and>
         fst (snd f) = colimitOverFinsets X (\<lambda>k. fst (snd (cocone k))) F \<and>
         snd (snd f) = Z \<and>
         (\<forall>S. pointed_finset X S \<longrightarrow>
              f \<cdot> colim_finset_inclusion X (\<lambda>k. fst (snd (cocone k))) F S = cocone S) \<Longrightarrow>
         f = colim_finset_UP_map X cocone F Z"
    using colim_finset_UP_uniqueness [OF cocone_obj cocone_arr functoriality \<open>Obj' X\<close> \<open>Obj' Z\<close>].
qed


lemma (in classical_category) seqE:
  assumes "seq g f" 
  shows "Arr (the f) \<and> Arr (the g) \<and> Dom (the g) = Cod (the f)"
  apply (rule_tac seqE [OF \<open>seq g f\<close>])
  unfolding arr_char dom_char cod_char
  apply auto
proof-
  fix a b
  assume "Arr a" "Arr b"
  assume "Id (Dom a) = Id (Cod b)"
  then have "Dom (Id (Dom a)) = Dom (Id (Cod b))" by simp
  then show "Dom a = Cod b"
    unfolding Dom_Id [OF Obj_Dom [OF \<open>Arr a\<close>]]
    unfolding Dom_Id [OF Obj_Cod [OF \<open>Arr b\<close>]].
qed



lemma colim_finset_inclusion_fst :
  assumes cocone_obj : "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A S)"
      and "pointed_finset X S"
and x_in_dom : "x \<in> snd (fst (snd (cop_finset_inclusion X A S)))"
shows "fst (colim_finset_inclusion X A F S) x =
       fst (quotient_proj (coproductOverFinsets X A) (colimit_relation X A F))
        (fst (cop_finset_inclusion X A S) x)"
  unfolding colim_finset_inclusion_def
proof-
  have comp_helper : "Arr' (the (Some (cop_finset_inclusion X A S))) \<and>
            Arr' (the (Some (
             (quotient_proj (coproductOverFinsets X A)
               (colimit_relation X A F))))) \<and>
            fst (snd (the (Some (
             (quotient_proj (coproductOverFinsets X A)
               (colimit_relation X A F)))))) = 
            snd (snd (the (Some (cop_finset_inclusion X A S))))"
    apply (rule_tac classical_category.seqE [OF ccpf])
    unfolding reverse_equality [OF pointed_set_comp_def]
    apply (subst comp_char)
    unfolding arr_char
    using cop_finset_inclusion_arr [OF cocone_obj \<open>pointed_finset X S\<close>]
       apply simp
    using quot_proj_arr [OF cop_finset_obj [OF cocone_obj 
          pointed_finset_obj [OF \<open>pointed_finset X S\<close>]]]
      apply simp
     apply (subst dom_char)
      apply (subst arr_char)
    using quot_proj_arr [OF cop_finset_obj [OF cocone_obj 
          pointed_finset_obj [OF \<open>pointed_finset X S\<close>]]]
      apply simp
     apply (subst cod_char)
      apply (subst arr_char)
    using cop_finset_inclusion_arr [OF cocone_obj \<open>pointed_finset X S\<close>]
      apply simp
    using cop_finset_inclusion_cod [OF cocone_obj \<open>pointed_finset X S\<close>]
     apply simp
    apply (subst reverse_equality [OF arr_char])
    unfolding Option.option.sel
    apply (subst reverse_equality [OF colim_finset_inclusion_def])
    unfolding arr_char
    apply simp
    using colim_finset_inclusion_arr [OF cocone_obj \<open>pointed_finset X S\<close>].

  define quot_proj_nosimp :: "'a LC \<times> 'a LC set
      \<Rightarrow> ('a LC \<Rightarrow> 'a LC \<Rightarrow> bool) \<Rightarrow> ('a LC \<Rightarrow> 'a LC) \<times> ('a LC \<times> 'a LC set) \<times> 'a LC \<times> 'a LC set"
    where "quot_proj_nosimp = quotient_proj"

  show "fst (quotient_proj (coproductOverFinsets X A) (colimit_relation X A F) \<cdot>
         cop_finset_inclusion X A S)
     x =
    fst (quotient_proj (coproductOverFinsets X A) (colimit_relation X A F))
     (fst (cop_finset_inclusion X A S) x)"
    unfolding Comp'_def
    using comp_helper
    unfolding reverse_equality [OF quot_proj_nosimp_def]
    by (simp add: x_in_dom)
qed




fun MkFunctor :: "'a comp \<Rightarrow> 'b comp \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "MkFunctor C D f a = 
                 (if partial_magma.arr C a 
                 then f a
                 else partial_magma.null D)"







context begin

interpretation C: category pointed_set_comp
  using is_category.

lemma comp_eq_char2:
  assumes arr_gf: "C.seq g f"
      and arr_h : "C.arr h"
      and dom_eq : "C.dom f = C.dom h"
      and cod_eq : "C.cod g = C.cod h"
   and EQ: "\<And>x. x \<in> snd (Dom' (the f)) \<Longrightarrow>
                x \<in> snd (Dom' (the h)) \<Longrightarrow>
               fst (the f) x \<in> snd (Dom' (the g)) \<Longrightarrow>
               fst (the g) (fst (the f) x) = fst (the h) x"
  shows "pointed_set_comp g f = h"
  apply (subst comp_char)
proof-
  show arr_f: "C.arr f"
    using C.seqE [OF arr_gf] by blast
  show arr_g: "C.arr g"
    using C.seqE [OF arr_gf] by blast
  show seq : "C.dom g = C.cod f"
    using C.seqE [OF arr_gf] by blast
  have "the g \<cdot> the f = the h"
    apply (rule_tac comp_eq_char)
    using arr_g
    unfolding arr_char apply simp
    using arr_f
    unfolding arr_char apply simp
    using arr_h
    unfolding arr_char apply simp
  proof-
    show dom_eq': "fst (snd (the f)) = fst (snd (the h))"
      using dom_eq
      unfolding dom_char [OF arr_f]
                dom_char [OF arr_h]
      by (simp add: Id'_def)
    show cod_eq': "snd (snd (the g)) = snd (snd (the h))"
      using cod_eq
      unfolding cod_char [OF arr_g]
                cod_char [OF arr_h]
      by (simp add: Id'_def)
    show seq': "fst (snd (the g)) = snd (snd (the f))"
      using seq
      unfolding cod_char [OF arr_f]
                dom_char [OF arr_g]
      by (simp add: Id'_def)
    fix x
    assume x_in_f : "x \<in> snd (fst (snd (the f)))"
    show "fst (the g) (fst (the f) x) = fst (the h) x"
      apply (rule_tac EQ)
      using x_in_f apply simp
      using x_in_f dom_eq' apply simp
    proof-
      have "Arr' (the f)"
        using arr_f
        unfolding arr_char by simp
      then show "fst (the f) x \<in> snd (fst (snd (the g)))"
        unfolding seq'
        unfolding Arr'_def
                  setcat.Arr_def
        using x_in_f by auto
    qed
  qed
  then show "Some (the g \<cdot> the f) = h"
    apply simp
    using \<open>C.arr h\<close>
    unfolding arr_char
    by simp
qed

        



end


end




end







