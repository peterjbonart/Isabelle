theory FinsetEquivalence
  imports Main
         "Category3.ProductCategory"
         "Category3.EquivalenceOfCategories"
         Gamma
         PointedSet
         SubcategoryFactorization
begin




context begin




interpretation pointed_set
  done

fun get_with_default :: "'a \<Rightarrow> 'a list \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "get_with_default x [] n = x" |
  "get_with_default x (a # as) 0 = a" |
  "get_with_default x (a # as) (Suc n) = get_with_default x as n" 

lemma get_get_with_def : "k < (length f) \<longrightarrow> get_with_default x f k = get f k"
  apply (rule_tac get.induct)
  by simp_all

lemma get_out_of_range : "k \<ge> (length f) \<longrightarrow> get_with_default x f k = x"
  apply (induction k arbitrary: f)
   apply auto
proof-
  fix k f
  have "get_with_default x f k =  get_with_default x f k" by simp
  assume ind: "(\<And>f. length f \<le> k \<longrightarrow> get_with_default x f k = x)"
  have "length f \<le> Suc k \<longrightarrow> get_with_default x f (Suc k) = x"
    apply (induction f)
     apply auto
    by (simp add: ind)
  then show "length f \<le> Suc k \<Longrightarrow> get_with_default x f (Suc k) = x" by simp
qed







fun interval :: "nat \<Rightarrow> 'a LC pointed_set" where
  "interval m = (K 0, {x. (\<exists>n. n < m \<and> x = K n)})"



lemma interval_obj : "n > 0 \<Longrightarrow> Obj' (interval n)"
  unfolding Obj'_def by simp



definition inclusionFunctor :: "gamma  \<Rightarrow> 'a LC parr option  " where
  "inclusionFunctor \<equiv> MkFunctor
                  pointed_fin_set.comp
                  pointed_set_comp
                  (\<lambda>f. Some (pointed_set.MkArr 
                   (interval (length (snd (the f))))
                   (interval (fst (the f)))
                   ((\<lambda>x. K (get (snd (the f)) (SOME n. K n = x))))))"


lemma pointed_fin_set_smash_arr : "partial_magma.arr pointed_fin_set.comp f \<Longrightarrow>
            pointed_fin_set.PointedArr' f \<and>
            f \<noteq> None \<and> fin_set.Arr' (the f)
            \<and> snd (the f) \<noteq> []
            \<and> get (snd (the f)) 0 = 0
            \<and> fst (the f) \<noteq> 0"
  apply safe
proof-
  fix f
  assume arr_f: "partial_magma.arr pointed_fin_set.comp f"
  have "partial_magma.arr pointed_fin_set.comp f \<longrightarrow>
       pointed_fin_set.PointedArr' f"
    unfolding pointed_fin_set.comp_def
    apply (subst subcategory.arr_char)
     apply (simp add: pointed_fin_set.is_subcategory)
    by simp
  from this and arr_f show p_arr_f: "pointed_fin_set.PointedArr' f" by simp
  have "pointed_fin_set.PointedArr' f \<longrightarrow>
        (f \<noteq> None \<and> fin_set.Arr' (the f))"
    unfolding pointed_fin_set.PointedArr'_def fin_set.comp_def
    apply (subst classical_category.arr_char)
    using fin_set.is_classical_category apply blast
    by simp
  from this and p_arr_f have f_arr_f : "(f \<noteq> None \<and> fin_set.Arr' (the f))" by simp
  from f_arr_f show "\<exists>y. f = Some y" by simp
  from f_arr_f show "fin_set.Arr' (the f)" by simp
  from p_arr_f show "snd (the f) = [] \<Longrightarrow> False" unfolding pointed_fin_set.PointedArr'_def by simp
  from p_arr_f show "get (snd (the f)) 0 = 0" unfolding pointed_fin_set.PointedArr'_def by simp

  show "0 < fst (the f)"
    using f_arr_f unfolding fin_set.Arr'_def \<open>get (snd (the f)) 0 = 0\<close> \<open>snd (the f) = [] \<Longrightarrow> False\<close>
    using p_arr_f pointed_fin_set.PointedArr'_def by auto
qed

lemma pointed_fin_set_unsmash_arr : "f \<noteq> None \<Longrightarrow> fin_set.Arr' (the f)
            \<Longrightarrow> snd (the f) \<noteq> []
            \<Longrightarrow> get (snd (the f)) 0 = 0
            \<Longrightarrow> fst (the f) \<noteq> 0 \<Longrightarrow>
            partial_magma.arr pointed_fin_set.comp f"
  unfolding pointed_fin_set.comp_def
  using pointed_fin_set.is_subcategory apply (simp add: subcategory.arr_char)
  unfolding pointed_fin_set.PointedArr'_def apply simp
  unfolding fin_set.comp_def
  using fin_set.is_classical_category by (simp add: classical_category.arr_char)



lemma inclusion_arr: "partial_magma.arr pointed_fin_set.comp f \<Longrightarrow>
         partial_magma.arr pointed_set_comp (inclusionFunctor f)"
proof-
  fix f
  assume arr_f: "partial_magma.arr pointed_fin_set.comp f"
  from arr_f and pointed_fin_set_smash_arr have p_arr_f: "pointed_fin_set.PointedArr' f" by simp
  from arr_f and pointed_fin_set_smash_arr have f_arr_f : "(f \<noteq> None \<and> fin_set.Arr' (the f))" by simp
  from p_arr_f have "snd (the f) \<noteq> []" unfolding pointed_fin_set.PointedArr'_def by simp
  from p_arr_f have "get (snd (the f)) 0 = 0" unfolding pointed_fin_set.PointedArr'_def by simp
  show "partial_magma.arr pointed_fin_set.comp f \<Longrightarrow>
         partial_magma.arr pointed_set_comp (inclusionFunctor f)"
    unfolding pointed_set_comp_def
    apply (subst classical_category.arr_char)
    using ccpf apply blast
    unfolding inclusionFunctor_def apply simp
    unfolding Arr'_def apply auto
    unfolding setcat.Arr_def pointed_set.MkArr_def apply auto
    using f_arr_f unfolding fin_set.Arr'_def apply simp
  proof-
    have "length (snd (the f)) > 0" by (simp add: \<open>snd (the f) \<noteq> []\<close>)
    then show "Obj' (K 0, {x. \<exists>n<length (snd (the f)). x = K n})" using interval_obj by auto
    have "fst (the f) > 0" using f_arr_f \<open>get (snd (the f)) 0 = 0\<close> \<open>0 < length (snd (the f))\<close>
      unfolding fin_set.Arr'_def by auto
    then show "Obj' (K 0, {x. \<exists>n<fst (the f). x = K n})" using interval_obj by auto
    show "get (snd (the f)) 0 = 0" using \<open>get (snd (the f)) 0 = 0\<close>.
    show "snd (the f) = [] \<Longrightarrow> undefined = K 0" by (simp add: \<open>snd (the f) \<noteq> []\<close>)
  qed
qed


lemma inclusion_id : "0<n \<Longrightarrow> inclusionFunctor (Some (fin_set.Id' n)) = Some (Id' (interval n))"
proof-
  assume "0<n"
  have arr_id: "partial_magma.arr pointed_fin_set.comp (Some (fin_set.Id' n))"
    unfolding pointed_fin_set.comp_def
    apply (subst subcategory.arr_char)
     apply (simp add: pointed_fin_set.is_subcategory)
    unfolding pointed_fin_set.PointedArr'_def apply auto
    unfolding fin_set.comp_def
      apply (subst classical_category.arr_char)
    using fin_set.is_classical_category apply blast
    apply simp
    using fin_set.is_classical_category apply (simp add: classical_category.Arr_Id)
    unfolding fin_set.Id'_def apply simp
     apply (subst get_rev_get)
      apply (simp_all add: \<open>0<n\<close>)
    by (metis \<open>0 < n\<close> less_numeral_extra(3) list.size(3) rev_get_length)
  have int_obj: "Obj' (K 0, {x. \<exists>na<n. x = K na})"
    using interval_obj \<open>0<n\<close> by auto
  have rev_nn: "rev_get n (\<lambda>k. k) \<noteq> []"
    by (metis \<open>0 < n\<close> less_numeral_extra(3) list.size(3) rev_get_length)
  show "inclusionFunctor (Some (fin_set.Id' n)) = Some (Id' (interval n)) "
    unfolding inclusionFunctor_def MkArr_def using arr_id apply simp
    apply (rule_tac fun_eq_char)
    unfolding Arr'_def setcat.Arr_def apply auto
    unfolding fin_set.Id'_def apply auto
                 apply (simp_all add: int_obj)
              apply (subst get_rev_get)
               apply (simp_all add: \<open>0<n\<close>)
             apply (simp_all add: rev_nn)
    unfolding Id'_def apply auto
       apply (simp_all add: int_obj)
    using \<open>0<n\<close> by simp
qed

lemma inclusion_dom : "partial_magma.arr pointed_fin_set.comp f \<Longrightarrow>
         partial_magma.dom pointed_set_comp (inclusionFunctor f) =
         inclusionFunctor (partial_magma.dom pointed_fin_set.comp f)"
proof-
  fix f
  assume arr_f: "partial_magma.arr pointed_fin_set.comp f"
  then have "snd (the f) \<noteq> []" by (simp add: pointed_fin_set_smash_arr)
  have dom_eq1: "partial_magma.dom pointed_set_comp (inclusionFunctor f) =
        Some (Id' (fst (snd (the (inclusionFunctor f)))))"
    apply (rule_tac dom_char)
    using arr_f by (simp add: inclusion_arr)

  have dom_eq2: "partial_magma.dom pointed_fin_set.comp f = 
        Some (fin_set.Id' (length (snd (the f))))"
    apply (rule_tac pointed_fin_set.dom_char)
    using arr_f.

  show "partial_magma.dom pointed_set_comp (inclusionFunctor f) =
         inclusionFunctor (partial_magma.dom pointed_fin_set.comp f)"
    apply (subst dom_eq1)
    apply (subst dom_eq2)
    apply (subst inclusion_id)
     apply (simp add: \<open>snd (the f) \<noteq> []\<close>)
    unfolding inclusionFunctor_def MkArr_def using arr_f by simp
qed

lemma inclusion_cod : "partial_magma.arr pointed_fin_set.comp f \<Longrightarrow>
         partial_magma.cod pointed_set_comp (inclusionFunctor f) =
         inclusionFunctor (partial_magma.cod pointed_fin_set.comp f)"
proof-
  fix f
  assume arr_f: "partial_magma.arr pointed_fin_set.comp f"
  then have "fst (the f) \<noteq> 0" by (simp add: pointed_fin_set_smash_arr)
  have cod_eq1: "partial_magma.cod pointed_set_comp (inclusionFunctor f) =
        Some (Id' (snd (snd (the (inclusionFunctor f)))))"
    apply (rule_tac cod_char)
    using arr_f by (simp add: inclusion_arr)

  have cod_eq2: "partial_magma.cod pointed_fin_set.comp f = 
        Some (fin_set.Id' (fst (the f)))"
    apply (rule_tac pointed_fin_set.cod_char)
    using arr_f.

  show "partial_magma.cod pointed_set_comp (inclusionFunctor f) =
         inclusionFunctor (partial_magma.cod pointed_fin_set.comp f)"
    apply (subst cod_eq1)
    apply (subst cod_eq2)
    apply (subst inclusion_id)
    using \<open>fst (the f) \<noteq> 0\<close> apply auto
    unfolding inclusionFunctor_def MkArr_def using arr_f by simp
qed




lemma inclusion_functor : "functor 
                  pointed_fin_set.comp
                  pointed_set_comp
                  inclusionFunctor"
  unfolding functor_def
  apply (simp add: is_category pointed_fin_set.is_category)
  unfolding functor_axioms_def apply safe
proof-
  fix f
  show " \<not> partial_magma.arr pointed_fin_set.comp f \<Longrightarrow>
         inclusionFunctor f = partial_magma.null pointed_set_comp"
    unfolding inclusionFunctor_def by simp
  assume arr_f: "partial_magma.arr pointed_fin_set.comp f"

  then show arr_inc_f: "partial_magma.arr pointed_set_comp (inclusionFunctor f)"
    using arr_f by (simp add: inclusion_arr)

  show "partial_magma.dom pointed_set_comp (inclusionFunctor f) =
         inclusionFunctor (partial_magma.dom pointed_fin_set.comp f)"
    apply (rule_tac inclusion_dom)
    using arr_f.

  show "partial_magma.cod pointed_set_comp (inclusionFunctor f) =
         inclusionFunctor (partial_magma.cod pointed_fin_set.comp f)"
    apply (rule_tac inclusion_cod)
    using arr_f.
next
  fix f g
  assume arr_gf: "partial_magma.arr pointed_fin_set.comp (pointed_fin_set.comp g f)"
  then have arr_f: "partial_magma.arr pointed_fin_set.comp f"
    by (meson category.seqE pointed_fin_set.is_category)
  from arr_gf have arr_g : "partial_magma.arr pointed_fin_set.comp g"
    by (meson category.seqE pointed_fin_set.is_category)
  from arr_gf have seq: "partial_magma.dom pointed_fin_set.comp g =
                         partial_magma.cod pointed_fin_set.comp f"
    by (meson category.seqE pointed_fin_set.is_category)
  from arr_f have arr_inc_f : "partial_magma.arr pointed_set_comp (inclusionFunctor f)"
    by (simp add: inclusion_arr)
  then have arr_inc_f' : "Arr' (the (inclusionFunctor f))" using arr_char by blast
  from arr_g have arr_inc_g : "partial_magma.arr pointed_set_comp (inclusionFunctor g)"
    by (simp add: inclusion_arr)
  then have arr_inc_g' : "Arr' (the (inclusionFunctor g))" using arr_char by blast
  from seq have seq_inc : "partial_magma.dom pointed_set_comp (inclusionFunctor g) =
                           partial_magma.cod pointed_set_comp (inclusionFunctor f)"
    apply (simp add: arr_g inclusion_dom)
    by (simp add: arr_f inclusion_cod)
  then have seq_inc' : "snd (snd (the (inclusionFunctor f))) = fst (snd (the (inclusionFunctor g)))"
    apply (subst seq_char)
    using arr_inc_f apply blast
    using arr_inc_g apply simp
    using arr_inc_g apply simp
    by simp
    
  have arr_inc_gf : "partial_magma.arr pointed_set_comp
           (pointed_set_comp (inclusionFunctor g) (inclusionFunctor f ))"
    by (simp add: arr_inc_f arr_inc_g seq_inc category.seqI pointed_set.is_category)

  show "inclusionFunctor (pointed_fin_set.comp g f) =
           pointed_set_comp (inclusionFunctor g) (inclusionFunctor f)"
    apply (subst comp_char)
       apply (simp_all add: arr_inc_f arr_inc_g seq_inc)
    apply (subst pointed_fin_set.comp_char)
       apply (simp_all add: arr_f arr_g seq)
  proof-
    have arr_gf2: "partial_magma.arr pointed_fin_set.comp (Some (fin_set.Comp' (the g) (the f)))"
      using pointed_fin_set.comp_char arr_f arr_g seq arr_gf by simp
    have arr_inc_gf2 : "partial_magma.arr pointed_set_comp (inclusionFunctor (Some (fin_set.Comp' (the g) (the f))))"
      using inclusion_arr arr_gf2 by blast
    have non_null : "inclusionFunctor (Some (fin_set.Comp' (the g) (the f))) \<noteq> None"
    using arr_inc_gf2 pointed_set.arr_char by blast

    have "the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f)))) =
          the (inclusionFunctor g) \<cdot> the (inclusionFunctor f)"
      apply (rule_tac fun_eq_char)
    proof-
      from arr_gf2 have "partial_magma.arr pointed_set_comp (inclusionFunctor (Some (fin_set.Comp' (the g) (the f))))"
        using inclusion_arr by blast
      then show "Arr' (the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f)))))"
        unfolding pointed_set_comp_def 
        using classical_category.arr_char ccpf by blast
      have "partial_magma.arr pointed_set_comp (Some (the (inclusionFunctor g) \<cdot> the (inclusionFunctor f)))"
        using arr_inc_gf by (simp add: arr_inc_f arr_inc_g pointed_set.comp_char seq_inc)
      then show "Arr' (the (inclusionFunctor g) \<cdot> the (inclusionFunctor f))"
        by (simp add: arr_char)

      have dom_eq1: "fst (snd (the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f)))))) =
    fst (snd (the (inclusionFunctor f)))"
        unfolding inclusionFunctor_def MkArr_def using arr_gf2 arr_f apply simp
        apply (subst fin_set.comp_length)
        by simp

      have "Some (Id' (fst (snd (the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f)))))))) =
         Some (Id' (fst (snd (the (inclusionFunctor g) \<cdot> the (inclusionFunctor f)))))"
        apply (subst dom_comp)
        apply (simp add: arr_inc_f')
          apply (simp add: arr_inc_g')
        apply (simp add: seq_inc')
        apply (subst dom_eq1)
        by simp
      
      then show "fst (snd (the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f)))))) =
    fst (snd (the (inclusionFunctor g) \<cdot> the (inclusionFunctor f)))"
        unfolding Id'_def by auto

      have cod_eq1: "snd (snd (the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f)))))) =
    snd (snd (the (inclusionFunctor g)))"
        unfolding inclusionFunctor_def MkArr_def using arr_gf2 arr_g apply simp
        unfolding fin_set.Comp'_def by simp

      have "Some (Id' (snd (snd (the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f)))))))) =
    Some (Id' (snd (snd (the (inclusionFunctor g) \<cdot> the (inclusionFunctor f)))))"
        apply (subst cod_comp)
        using arr_char arr_inc_f apply blast
        using arr_char arr_inc_g apply blast
         apply (subst seq_char)
        using arr_inc_f apply simp
        using arr_inc_g apply simp
        using seq_inc apply simp
         apply simp
        apply (subst cod_eq1)
        by simp

      then show "snd (snd (the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f)))))) =
    snd (snd (the (inclusionFunctor g) \<cdot> the (inclusionFunctor f)))"
        unfolding Id'_def by auto
      fix x
      assume " x \<in> snd (fst (snd (the (inclusionFunctor
                                  (Some (fin_set.Comp' (the g) (the f)))))))"
      then have "x \<in> snd (interval (length (snd (fin_set.Comp' (the g) (the f)))))" 
        unfolding inclusionFunctor_def MkArr_def
        using arr_gf2 by simp
      then have ex_n_gf : "\<exists>n< length (snd (fin_set.Comp' (the g) (the f))). x = K n" by simp
      then have ex_n_f : "\<exists>n< length (snd (the f)). x = K n" using fin_set.comp_length by simp
      have x_in_f: "x \<in> snd (fst (snd (the (inclusionFunctor f))))"
        unfolding inclusionFunctor_def MkArr_def using arr_f ex_n_f by simp
      from ex_n_f obtain n where n_def: "n < length (snd (the f)) \<and> x = K n" by blast
      have "(SOME n. K n = x) = n"
      proof
        show "K n = x" using n_def by simp
        show "\<And>na. K na = x \<Longrightarrow> na = n" using n_def by simp
      qed
      then have seq2: "get (snd (the f)) (SOME n. K n = x) < length (snd (the g))"
        apply simp
        using arr_f arr_g fin_set.Arr'_def fin_set.Id'_def n_def pointed_fin_set.cod_char pointed_fin_set.dom_char pointed_fin_set_smash_arr seq by fastforce
      
      show "fst (the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f))))) x =
         fst (the (inclusionFunctor g) \<cdot> the (inclusionFunctor f)) x"
        unfolding Comp'_def using arr_inc_f' arr_inc_g' seq_inc' x_in_f apply auto
      proof-
        show "fst (the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f))))) x =
    fst (the (inclusionFunctor g)) (fst (the (inclusionFunctor f)) x)"
          unfolding inclusionFunctor_def MkArr_def 
          using arr_g arr_f arr_gf2 ex_n_gf ex_n_f seq2 apply simp
          using n_def apply simp
          unfolding fin_set.Comp'_def
          by simp
      qed
    qed
    then have "Some (the (inclusionFunctor (Some (fin_set.Comp' (the g) (the f))))) =
    Some (the (inclusionFunctor g) \<cdot> the (inclusionFunctor f))" by simp
    then show "inclusionFunctor (Some (fin_set.Comp' (the g) (the f))) =
    Some (the (inclusionFunctor g) \<cdot> the (inclusionFunctor f))"
      by (simp add: non_null)
  qed
qed



interpretation "functor" 
                  pointed_fin_set.comp
                  pointed_set_comp
                  inclusionFunctor
  using inclusion_functor.



lemma eval_inclusion_functor : "A.arr f \<Longrightarrow>
       n < length (snd (the f)) \<Longrightarrow>
       x = K n \<Longrightarrow> fst (the (inclusionFunctor f)) x = K (get (snd (the f)) n)"
  unfolding inclusionFunctor_def MkArr_def by simp

    

lemma inclusion_dom2 : "A.arr f \<Longrightarrow> fst (snd (the (inclusionFunctor f))) = interval (fst (the (A.dom f)))"
  unfolding inclusionFunctor_def MkArr_def apply simp
  apply (subst pointed_fin_set.dom_char)
   apply simp
  unfolding fin_set.Id'_def by simp


lemma inclusion_cod2 : "A.arr f \<Longrightarrow> snd (snd (the (inclusionFunctor f))) = interval (fst (the (A.cod f)))"
  unfolding inclusionFunctor_def MkArr_def apply simp
  apply (subst pointed_fin_set.cod_char)
   apply simp
  unfolding fin_set.Id'_def by simp

lemma fully_faithful: "fully_faithful_functor 
                  pointed_fin_set.comp
                  pointed_set_comp
                  inclusionFunctor"
  unfolding fully_faithful_functor_def
  unfolding faithful_functor_def full_functor_def
  apply (simp add: inclusion_functor)
  apply (rule_tac conjI)
proof-

  (* We first prove faithfulness for a functor that is exactly like inclusionFunctor,
because Isabelle for some reason is incapable of proving
                       "inclusionFunctor f = inclusionFunctor g \<Longrightarrow>
                       inclusionFunctor f = inclusionFunctor g"
while it has no problems proving "inclusionLike f = inclusionLike g \<Longrightarrow>
                                  inclusionLike f = inclusionLike g" 
I have no idea why this is necessary, but it is.*)

  have faithful: "\<And> inclusionLike :: (nat \<times> nat list) option \<Rightarrow> 'b LC parr option. 
         (\<And>f x n. A.arr f \<Longrightarrow>
               n<length (snd (the f)) \<Longrightarrow> x = K n \<Longrightarrow>
               fst (the (inclusionLike f)) x =
               K (get (snd (the f)) n)) \<Longrightarrow>
         faithful_functor_axioms pointed_fin_set.comp inclusionLike"
    unfolding faithful_functor_axioms_def apply auto
  proof-
    fix inclusionLike :: "(nat \<times> nat list) option \<Rightarrow> 'b LC parr option"
    fix f g :: "(nat \<times> nat list) option"
    assume inc_eval : "(\<And>f x n.
           A.arr f \<Longrightarrow>
           n < length (snd (the f)) \<Longrightarrow>
           x = K n \<Longrightarrow> fst (the (inclusionLike f)) (K n) = K (get (snd (the f)) n))"
    assume arr_f: "A.arr f"
    assume arr_g: "A.arr g"
    assume dom_eq: "A.dom f = A.dom g"
    assume cod_eq: "A.cod f = A.cod g"
    assume inc_eq: "inclusionLike f = inclusionLike g"
    have "the f = the g"
    proof
      show fst_eq: "fst (the f) = fst (the g)"
        using arr_f arr_g cod_eq fin_set.Id'_def pointed_fin_set.cod_char by auto
      have length_eq: "length (snd (the f)) = length (snd (the g))"
        using arr_f arr_g dom_eq fin_set.Id'_def pointed_fin_set.dom_char by auto
      show "snd (the f) = snd (the g)"
        apply (rule_tac getFaithful)
         apply (simp add: length_eq)
      proof-
        fix n
        assume nlf : "n < length (snd (the f))"
        then have nlg : "n < length (snd (the g))" using length_eq by simp
        obtain x :: "'a LC" where x_def : "x = K n" by simp
        then have ex_n : "\<exists>n<length (snd (the f)). x = K n"
          using nlf by blast
        have eq1: "fst (the (inclusionLike f)) (K n) = K (get (snd (the f)) n)"
          apply (rule_tac inc_eval)
          by (simp_all add: arr_f nlf)
        have eq2: "fst (the (inclusionLike g)) (K n) = K (get (snd (the g)) n)"
          apply (rule_tac inc_eval)
          by (simp_all add: arr_g nlg x_def)
        from eq1 and eq2 and inc_eq have "K (get (snd (the f)) n) = K (get (snd (the g)) n)" by simp
        then show "get (snd (the f)) n = get (snd (the g)) n" by simp
      qed
    qed
    then show "f = g"
      by (simp add: arr_f arr_g option.expand pointed_fin_set_smash_arr)
  qed
  term inclusionFunctor
  show "faithful_functor_axioms pointed_fin_set.comp inclusionFunctor"
    apply (rule_tac faithful)
    using eval_inclusion_functor.

  show "full_functor_axioms pointed_fin_set.comp pointed_set_comp inclusionFunctor"
    unfolding full_functor_axioms_def apply auto
  proof
    fix a b g
    assume ide_a : "A.ide a"
    then have "0 < fst (the a)"
      using A.ideD(1) pointed_fin_set_smash_arr by blast
    from ide_a have arr_a : "A.arr a" by simp
    from ide_a have "fst (the a) = length (snd (the a))"
      by (metis A.ideD(2) arr_a fin_set.Id'_def option.sel pointed_fin_set.dom_char prod.collapse prod.simps(1))
    assume ide_b : "A.ide b"
    then have "0 < fst (the b)"
      using A.ideD(1) pointed_fin_set_smash_arr by blast
    from ide_b have arr_b : "A.arr b" by simp
    from ide_b have "fst (the b) = length (snd (the b))"
      by (metis A.ideD(2) arr_b fin_set.Id'_def option.sel pointed_fin_set.dom_char prod.collapse prod.simps(1))
    assume gab : "B.in_hom g (inclusionFunctor b) (inclusionFunctor a)"

    from gab have dom_g: "B.dom g = inclusionFunctor b" using category.in_homE by blast
    from gab have cod_g: "B.cod g = inclusionFunctor a" using category.in_homE by blast
    from gab have arr_g : "B.arr g" using category.in_homE by blast

    from dom_g have "Some (Id' (fst (snd (the g)))) = Some (Id' (interval (fst (the b))))"
      using arr_g apply (simp add: pointed_set.dom_char)
      unfolding inclusionFunctor_def MkArr_def using arr_b apply simp
      unfolding Id'_def using \<open>fst (the b) = length (snd (the b))\<close> by auto
    then have dom_g2: "fst (snd (the g)) = interval (fst (the b))"
      unfolding Id'_def by simp

    from cod_g have "Some (Id' (snd (snd (the g)))) = Some (Id' (interval (fst (the a))))"
      using arr_g apply (simp add: pointed_set.cod_char)
      unfolding inclusionFunctor_def MkArr_def using arr_a apply simp
      unfolding Id'_def using \<open>fst (the a) = length (snd (the a))\<close> by auto
    then have cod_g2: "snd (snd (the g)) = interval (fst (the a))"
      unfolding Id'_def by simp

    from arr_g have "fst (the g) (fst (fst (snd (the g)))) = fst (snd (snd (the g)))"
      unfolding pointed_set.arr_char unfolding Arr'_def by simp
    then have "fst (the g) (K 0) = K 0"
      using dom_g2 cod_g2 by simp

    define f where f_def: "f = Some (fst (the a),rev_get (fst (the b))
                           (\<lambda>n. (SOME m. fst (the g) (K n) = K m)))"
    show "A.in_hom f b a \<and> inclusionFunctor f = g"
      apply auto
    proof
      show arr_f: "A.arr f"
        apply (rule_tac pointed_fin_set_unsmash_arr)
        unfolding f_def apply simp_all
        unfolding fin_set.Arr'_def apply simp
           apply auto[1]
      proof-
        have "length (rev_get (fst (the b)) (\<lambda>n. SOME m. fst (the g) (K n) = K m)) \<noteq> length []"
          by (simp add: \<open>0 < fst (the b)\<close>)
        then show "rev_get (fst (the b)) (\<lambda>n. SOME m. fst (the g) (K n) = K m) \<noteq> []"
          by force
        show "get (rev_get (fst (the b)) (\<lambda>n. SOME m. fst (the g) (K n) = K m)) 0 = 0"
          using \<open>0 < fst (the b)\<close> apply simp
        proof
          show "fst (the g) (K 0) = K 0" using \<open>fst (the g) (K 0) = K 0\<close>.
          fix m
          show "fst (the g) (K 0) = K m \<Longrightarrow> m = 0"
            by (simp add: \<open>fst (the g) (K 0) = K 0\<close>)
        qed
        show "0 < fst (the a)" using \<open>0 < fst (the a)\<close>.
        fix n
        assume "n < fst (the b)"
        then have "K n \<in> snd (fst (snd (the g)))"
          by (simp add: dom_g2)
        then have "fst (the g) (K n) \<in> snd (snd (snd (the g)))"
          using arr_g by (simp add: arr_char pointed_set.maps_to_char)
        then have "fst (the g) (K n) \<in> {x. \<exists>m<fst (the a). x = K m}"
          by (simp add: cod_g2)
        then have "\<exists>m<fst (the a). fst (the g) (K n) = K m" by simp
        then obtain m where m_def: "m < fst (the a) \<and> fst (the g) (K n) = K m" by auto
        have m_some: "(SOME m. fst (the g) (K n) = K m) = m"
        proof
          show "fst (the g) (K n) = K m" using m_def by simp
          show "\<And>ma. fst (the g) (K n) = K ma \<Longrightarrow> ma = m" using m_def by simp
        qed
        show "(SOME m. fst (the g) (K n) = K m) < fst (the a)"
          apply (subst m_some)
          by (simp add: m_def)
      qed
      show dom_f: "A.dom f = b"
        using arr_f apply (simp add: pointed_fin_set.dom_char)
        unfolding f_def apply simp
      proof-
        have "Some (fin_set.Id' (fst (the b))) = A.cod b"
          using arr_b by (simp add: pointed_fin_set.cod_char)
        then show "Some (fin_set.Id' (fst (the b))) = b"
          by (simp add: ide_b)
      qed
      then have dom_f2: "fst (snd (the (inclusionFunctor f))) = interval (fst (the b))"
        using arr_f by (simp add: inclusion_dom2)

      show cod_f: "A.cod f = a"
        using arr_f apply (simp add: pointed_fin_set.cod_char)
        unfolding f_def apply simp
      proof-
        have "Some (fin_set.Id' (fst (the a))) = A.cod a"
          using arr_a by (simp add: pointed_fin_set.cod_char)
        then show "Some (fin_set.Id' (fst (the a))) = a"
          by (simp add: ide_a)
      qed
      then have cod_f2 : "snd (snd (the (inclusionFunctor f))) = interval (fst (the a))"
        using arr_f by (simp add: inclusion_cod2)
      have the_eq: "the (inclusionFunctor f) = the g"
        apply (rule_tac fun_eq_char)
        using arr_f pointed_set.arr_char apply auto[1]
        using arr_g pointed_set.arr_char apply auto[1]
        using dom_g2 dom_f2 apply simp
        using cod_g2 cod_f2 apply simp
        apply (simp add: dom_f2)
      proof-
        fix x :: "'c LC"
        assume ex_n : "\<exists>n<fst (the b). x = K n"
        then obtain n where n_def: "n < fst (the b) \<and> x = K n" by auto
        have "K n \<in> snd (fst (snd (the g)))" using dom_g2 n_def by simp
        then have "fst (the g) (K n) \<in> snd (snd (snd (the g)))" 
          using arr_g by (simp add: arr_char pointed_set.maps_to_char) 
        then have "fst (the g) (K n) \<in> {x. \<exists>m<fst (the a). x = K m}" using cod_g2 by simp
        then have ex_m : "\<exists>m<fst(the a). fst (the g) (K n) = K m" by simp
        then obtain m where m_def : "m < fst (the a) \<and> fst (the g) (K n) = K m" by auto
        have m_some: "(SOME m. fst (the g) (K n) = K m) = m"
        proof
          show "fst (the g) (K n) = K m" using m_def by simp
          show "\<And>ma. fst (the g) (K n) = K ma \<Longrightarrow> ma = m" using m_def by simp
        qed
        have eq: "fst (the (inclusionFunctor f)) x = K (get (snd (the f)) n)"
          apply (rule_tac eval_inclusion_functor)
            apply (simp add: arr_f)
          by (simp_all add: n_def f_def)
        show "fst (the (inclusionFunctor f)) x = fst (the g) x"
          apply (subst eq)
          unfolding f_def apply simp
          apply (simp add: n_def get_rev_get)
          using m_some m_def by simp
      qed
      from arr_f have "B.arr (inclusionFunctor f)" by blast
      then have inc_f_nn: "inclusionFunctor f \<noteq> None" 
        apply (simp add: arr_char)
        by blast
      from arr_g have g_nn: "g \<noteq> None"
        by (simp add: arr_char)
      from the_eq show "inclusionFunctor f = g"
        by (simp add: g_nn inc_f_nn option.expand)
    qed
  qed
qed

lemma interval_finite : "finite (snd (interval n))"
  by simp





lemma inclusion_factors_over_finite_sets :
   "factorization pointed_fin_set.comp pointed_set_comp inclusionFunctor FiniteArr'"
  unfolding factorization_def
  apply (simp add: pointed_fin_set.is_category)
  apply (simp add: is_category)
  apply (simp add: finite_subcat)
  apply (simp add: inclusion_functor)
  unfolding factorization_axioms_def
  apply auto
proof-
  fix a
  assume arr_a: "A.arr a"
  show "FiniteArr' (inclusionFunctor a)"
    unfolding FiniteArr'_def
    using arr_a by (simp add: inclusion_dom2 inclusion_cod2)
qed

lemma inclusion_functor_to_fin_set : 
     "functor pointed_fin_set.comp pointed_finite_subcat inclusionFunctor"
  unfolding pointed_finite_subcat_def
  apply (rule_tac factorization.is_functor)
  using inclusion_factors_over_finite_sets.


lemma inclusion_essentially_surjective:
    "essentially_surjective_functor
     pointed_fin_set.comp pointed_finite_subcat inclusionFunctor"
  unfolding essentially_surjective_functor_def
  apply (simp add: inclusion_functor_to_fin_set)
  unfolding essentially_surjective_functor_axioms_def
  apply auto
proof-
  fix b :: "'a LC parr option"
  assume fin_ide_b: "partial_magma.ide pointed_finite_subcat b"
  then have ide_b: "B.ide b"
    unfolding pointed_finite_subcat_def
    by (simp add: finite_subcat subcategory.ide_char)
  from fin_ide_b have "partial_magma.arr pointed_finite_subcat b"
    by (simp add: finite_subcat pointed_finite_subcat_def subcategory.ide_char)
  then have fin_arr_b : "FiniteArr' b"
    unfolding pointed_finite_subcat_def
    by (simp add: finite_subcat subcategory.arr_char)
  then have fin_b : "finite (snd (Dom' (the b)))"
    unfolding FiniteArr'_def by simp
  from fin_arr_b have arr_b : "Arr' (the b)"
    unfolding FiniteArr'_def
    using pointed_set.arr_char by blast

  have obj_b : "Obj' (Dom' (the b))"
    using dom_obj [OF arr_b].


  from pointed_finite_imp_nat_seg_image_inj_on [OF obj_b \<open>finite (snd (Dom' (the b)))\<close>]
  obtain n :: nat and f2 where f2n_def: "bij_betw f2 {i. i < n} (snd (fst (snd (the b)))) \<and> f2 0 = fst (fst (snd (the b)))" 
    by auto
  from obj_b have "fst (Dom' (the b)) \<in> snd (Dom' (the b))"
    unfolding Obj'_def.
  then have "fst (Dom' (the b)) \<in> f2 ` {i. i < n}"
    using f2n_def unfolding bij_betw_def by simp
  then obtain i where "i < n" by auto
  then have "n > 0" by simp
  show "\<exists>a. A.ide a \<and> category.isomorphic pointed_finite_subcat (inclusionFunctor a) b"
    apply (rule_tac exI)
  proof
    define a where "a = Some (fin_set.Id' n)"
    show "A.ide a"
      apply (subst pointed_fin_set.ide_char)
      unfolding a_def apply simp
      unfolding fin_set.Id'_def apply simp
      by (metis \<open>n>0\<close> list.size(3) less_numeral_extra(3) rev_get_length)
    show "category.isomorphic pointed_finite_subcat (inclusionFunctor (Some (fin_set.Id' n))) b"
      apply (subst category.isomorphic_def)
      unfolding pointed_finite_subcat_def
      using subcategory.is_category [OF finite_subcat] apply simp
      apply (rule_tac exI)
    proof
      term MkArr
      define \<phi> where "\<phi> = Some (MkArr (interval n) (Dom' (the b)) 
                   (\<lambda>x. f2 (SOME n. K n = x)))"
      define \<psi> where "\<psi> = Some (MkArr (Dom' (the b)) (interval n)
                   (\<lambda>x. K (SOME m. m<n \<and> f2 m = x)))"
      show \<phi>_in_hom: "partial_magma.in_hom (subcategory.comp pointed_set_comp FiniteArr') \<phi>
     (inclusionFunctor (Some (fin_set.Id' n))) b"
        apply (subst subcategory.in_hom_char [OF finite_subcat])
        apply auto
      proof-
        have "A.ide (Some (fin_set.Id' n))"
          apply (subst pointed_fin_set.ide_char)
          unfolding fin_set.Id'_def by (simp add: \<open>0<n\<close>)
        then have arr_id_n: "A.arr (Some (fin_set.Id' n))" by simp
        show "partial_magma.arr (subcategory.comp pointed_set_comp FiniteArr')
     (inclusionFunctor (Some (fin_set.Id' n)))"
          using functor.preserves_arr [OF inclusion_functor_to_fin_set arr_id_n]
          unfolding pointed_finite_subcat_def.
        show "partial_magma.arr (subcategory.comp pointed_set_comp FiniteArr') b"
          using \<open>partial_magma.arr pointed_finite_subcat b\<close> 
          unfolding pointed_finite_subcat_def.
        show arr_\<phi>: "partial_magma.arr (subcategory.comp pointed_set_comp FiniteArr') \<phi>"
          apply (subst subcategory.arr_char [OF finite_subcat])
          unfolding FiniteArr'_def apply auto
          unfolding pointed_set_comp_def
            apply (subst classical_category.arr_char [OF ccpf])
          unfolding Arr'_def apply safe
        proof-
          show "\<exists>y. \<phi> = Some y"
            unfolding \<phi>_def by blast
          show "setcat.Arr (forget (the \<phi>))"
            unfolding setcat.Arr_def \<phi>_def MkArr_def apply simp
          proof
            fix x
            assume "x \<in> {x. \<exists>m<n. x = K m}"
            then have ex_m : "\<exists>m < n. x = K m" by simp
            then obtain m where m_def: "m < n \<and> x = K m" by auto
            have some_m : "(SOME m. K m = x) = m"
            proof
              show "K m = x" using m_def by simp
              show "\<And>ma. K ma = x \<Longrightarrow> ma = m" using m_def by simp
            qed
            show "f2 (SOME m. K m = x) \<in> snd (fst (snd (the b)))"
              apply (subst some_m)
              using f2n_def m_def unfolding bij_betw_def by blast
          qed
          show "Obj' (fst (snd (the \<phi>)))"
            unfolding \<phi>_def MkArr_def apply simp
            using interval_obj [OF \<open>0<n\<close>] unfolding interval.simps.
          show "Obj' (snd (snd (the \<phi>)))"
            unfolding \<phi>_def MkArr_def apply simp
            using dom_obj [OF arr_b].
          show "fst (the \<phi>) (fst (fst (snd (the \<phi>)))) = fst (snd (snd (the \<phi>)))"
            unfolding \<phi>_def MkArr_def apply (simp add: \<open>0<n\<close>)
            using f2n_def by simp
          show "finite (snd (fst (snd (the \<phi>))))"
            unfolding \<phi>_def MkArr_def by simp
          show "finite (snd (snd (snd (the \<phi>))))"
            unfolding \<phi>_def MkArr_def apply simp
            using fin_b.
        qed
        then have "FiniteArr' \<phi>"
          using subcategory.arr_char [OF finite_subcat] by blast
        then have "B.arr \<phi>"
          unfolding FiniteArr'_def by simp
        show "B.in_hom \<phi> (inclusionFunctor (Some (fin_set.Id' n))) b"
          apply (rule_tac category.in_homI)
             apply (simp add: is_category)
            apply (simp add: \<open>B.arr \<phi>\<close>)
           apply (subst inclusion_id [OF \<open>0<n\<close>])
           apply (subst dom_char [OF \<open>B.arr \<phi>\<close>])
           apply (simp add: \<phi>_def MkArr_def)
          apply (subst cod_char [OF \<open>B.arr \<phi>\<close>])
          unfolding \<phi>_def MkArr_def apply simp
          using classical_category.ide_char [OF ccpf]
          using ide_b unfolding pointed_set_comp_def
          by (simp add: \<open>\<And>a. partial_magma.ide (classical_category.comp Arr' (\<lambda>t. fst (snd t)) (\<lambda>t. snd (snd t)) (\<cdot>)) a = (Arr' (the a) \<and> a = Some (Id' (fst (snd (the a)))))\<close>)
      qed
      have arr_\<phi>: "partial_magma.arr (subcategory.comp pointed_set_comp FiniteArr') \<phi>"
        using category.in_homE [OF subcategory.is_category[OF finite_subcat] \<phi>_in_hom]
        by blast
      then have fin_arr_\<phi>: "FiniteArr' \<phi>" 
        using subcategory.arr_char [OF finite_subcat] by blast
      then have "B.arr \<phi>"
        unfolding FiniteArr'_def by simp
      then have arr'_\<phi>: "Arr' (the \<phi>)"
        using arr_char by blast
      have \<psi>_in_hom : "partial_magma.in_hom (subcategory.comp pointed_set_comp FiniteArr') \<psi>
     b (inclusionFunctor (Some (fin_set.Id' n)))"
        apply (subst subcategory.in_hom_char [OF finite_subcat])
        apply auto
      proof-
        have "A.ide (Some (fin_set.Id' n))"
          apply (subst pointed_fin_set.ide_char)
          unfolding fin_set.Id'_def by (simp add: \<open>0<n\<close>)
        then have arr_id_n: "A.arr (Some (fin_set.Id' n))" by simp
        show "partial_magma.arr (subcategory.comp pointed_set_comp FiniteArr')
     (inclusionFunctor (Some (fin_set.Id' n)))"
          using functor.preserves_arr [OF inclusion_functor_to_fin_set arr_id_n]
          unfolding pointed_finite_subcat_def.
        show "partial_magma.arr (subcategory.comp pointed_set_comp FiniteArr') b"
          using \<open>partial_magma.arr pointed_finite_subcat b\<close> 
          unfolding pointed_finite_subcat_def.
        show "partial_magma.arr (subcategory.comp pointed_set_comp FiniteArr') \<psi>"
          apply (subst subcategory.arr_char [OF finite_subcat])
          unfolding FiniteArr'_def apply auto
          unfolding pointed_set_comp_def
            apply (subst classical_category.arr_char [OF ccpf])
          unfolding Arr'_def apply safe
        proof-
          show "\<exists>y. \<psi> = Some y"
            unfolding \<psi>_def by blast
          show "setcat.Arr (forget (the \<psi>))"
            unfolding setcat.Arr_def \<psi>_def MkArr_def apply simp
          proof
            fix x
            assume "x \<in> snd (Dom' (the b))"
            then have "x \<in> f2 ` {i. i < n}"
              using f2n_def unfolding bij_betw_def by simp
            then obtain i where i_def: "i<n \<and> f2 i = x" by auto
            have i_some : "(SOME m. m<n \<and> f2 m = x) = i"
            proof
              show "i < n \<and> f2 i = x" by (simp add: i_def)
              fix m
              assume m_def: "m < n \<and> f2 m = x"
              then have f2_eq: "f2 m = f2 i" by (simp add: i_def)
              have inj: "\<And> x y. x < n \<Longrightarrow> y < n \<Longrightarrow> (f2 x = f2 y \<Longrightarrow> x = y)"
                using f2n_def unfolding bij_betw_def inj_on_def by auto
              show "m = i"
                apply (rule_tac inj)
                by (simp_all add: m_def f2_eq i_def)
            qed
            show "K (SOME m. m < n \<and> f2 m = x) \<in> {x. \<exists>na<n. x = K na}"
              apply (subst i_some)
            proof
              show "\<exists>na<n. K i = K na"
              proof
                show "i < n \<and> K i = K i" by (simp add: i_def)
              qed
            qed
          qed
          show "Obj' (fst (snd (the \<psi>)))"
            unfolding \<psi>_def MkArr_def apply simp
            using dom_obj [OF arr_b].
          have b_pointed: "fst (fst (snd (the b))) \<in> snd (fst (snd (the b)))"
            using dom_obj [OF arr_b] unfolding Obj'_def.
          show "Obj' (snd (snd (the \<psi>)))"
            unfolding \<psi>_def MkArr_def apply simp
            using interval_obj [OF \<open>0<n\<close>] unfolding interval.simps.
          show "fst (the \<psi>) (fst (fst (snd (the \<psi>)))) = fst (snd (snd (the \<psi>)))"
            unfolding \<psi>_def MkArr_def apply (simp add: b_pointed)
          proof
            show "0 < n \<and> f2 0 = fst (fst (snd (the b)))"
              apply (simp add: \<open>0<n\<close>)
              using f2n_def by simp
            fix m
            assume m_def: "m < n \<and> f2 m = fst (fst (snd (the b)))"
            have inj: "\<And> x y. x < n \<Longrightarrow> y < n \<Longrightarrow> (f2 x = f2 y \<Longrightarrow> x = y)"
              using f2n_def unfolding bij_betw_def inj_on_def by auto
            show "m = 0"
              apply (rule_tac inj)
                apply (simp_all add: m_def \<open>0<n\<close>)
              using f2n_def by simp
          qed
          show "finite (snd (fst (snd (the \<psi>))))"
            unfolding \<psi>_def MkArr_def by (simp add: fin_b)
          show "finite (snd (snd (snd (the \<psi>))))"
            unfolding \<psi>_def MkArr_def by simp
        qed
        then have "FiniteArr' \<psi>"
          using subcategory.arr_char [OF finite_subcat] by blast
        then have "B.arr \<psi>"
          unfolding FiniteArr'_def by simp
        show "B.in_hom \<psi> b (inclusionFunctor (Some (fin_set.Id' n)))"
          apply (rule_tac category.in_homI)
             apply (simp add: is_category)
            apply (simp add: \<open>B.arr \<psi>\<close>)
           apply (subst dom_char [OF \<open>B.arr \<psi>\<close>])
          apply (simp add: \<psi>_def MkArr_def)
          using classical_category.ide_char [OF ccpf]
          using ide_b
           apply (simp add: pointed_set_comp_def \<open>\<And>a. partial_magma.ide (classical_category.comp Arr' (\<lambda>t. fst (snd t)) (\<lambda>t. snd (snd t)) (\<cdot>)) a = (Arr' (the a) \<and> a = Some (Id' (fst (snd (the a)))))\<close>)
          apply (subst inclusion_id [OF \<open>0<n\<close>])
          apply (subst cod_char [OF \<open>B.arr \<psi>\<close>])
          unfolding \<psi>_def MkArr_def by simp
      qed
      have arr_\<psi>: "partial_magma.arr (subcategory.comp pointed_set_comp FiniteArr') \<psi>"
        using category.in_homE [OF subcategory.is_category[OF finite_subcat] \<psi>_in_hom]
        by blast
      then have fin_arr_\<psi>: "FiniteArr' \<psi>" 
        using subcategory.arr_char [OF finite_subcat] by blast
      then have "B.arr \<psi>"
        unfolding FiniteArr'_def by simp
      then have arr'_\<psi>: "Arr' (the \<psi>)"
        using arr_char by blast
      have \<phi>_rev_def : "Some (MkArr (interval n) (fst (snd (the b))) (\<lambda>x. f2 (SOME n. K n = x))) = \<phi>" 
        unfolding \<phi>_def by simp
      show "category.iso (subcategory.comp pointed_set_comp FiniteArr')
     (Some (MkArr (interval n) (fst (snd (the b))) (\<lambda>x. f2 (SOME n. K n = x))))"
        apply (subst \<phi>_rev_def)
        apply (subst category.iso_def)
         apply (simp add: subcategory.is_category [OF finite_subcat])
      proof
        show "category.inverse_arrows (subcategory.comp pointed_set_comp FiniteArr') \<phi> \<psi>"
          apply (subst category.inverse_arrows_def)
           apply (simp add: subcategory.is_category [OF finite_subcat])
        proof
          have \<psi>\<phi>_in_hom: "partial_magma.in_hom (subcategory.comp pointed_set_comp FiniteArr')
   (subcategory.comp pointed_set_comp FiniteArr' \<psi> \<phi>)
                (inclusionFunctor (Some (fin_set.Id' n)))
                (inclusionFunctor (Some (fin_set.Id' n)))"
            apply (rule_tac category.comp_in_homI [OF subcategory.is_category [OF finite_subcat]])
            using \<phi>_in_hom apply blast
            using \<psi>_in_hom.
          then have arr_\<psi>\<phi> : "partial_magma.arr (subcategory.comp pointed_set_comp FiniteArr')
   (subcategory.comp pointed_set_comp FiniteArr' \<psi> \<phi>)"
            using category.in_homE [OF subcategory.is_category [OF finite_subcat] \<psi>\<phi>_in_hom]
            by blast

          have \<phi>\<psi>_in_hom : "partial_magma.in_hom (subcategory.comp pointed_set_comp FiniteArr')
   (subcategory.comp pointed_set_comp FiniteArr' \<phi> \<psi>) b b"
            apply (rule_tac category.comp_in_homI [OF subcategory.is_category [OF finite_subcat]])
            using \<psi>_in_hom apply blast
            using \<phi>_in_hom.
          then have arr_\<phi>\<psi> : "partial_magma.arr (subcategory.comp pointed_set_comp FiniteArr')
   (subcategory.comp pointed_set_comp FiniteArr' \<phi> \<psi>)"
            using category.in_homE [OF subcategory.is_category [OF finite_subcat] \<phi>\<psi>_in_hom]
            by blast
          have seq\<psi>\<phi>: "B.seq \<psi> \<phi>"
            apply (rule_tac category.seqI' [OF is_category])
            using \<phi>_in_hom
            using subcategory.in_hom_char [OF finite_subcat]
             apply blast
            using \<psi>_in_hom
            using subcategory.in_hom_char [OF finite_subcat]
            by blast
          have seq\<phi>\<psi>: "B.seq \<phi> \<psi>"
            apply (rule_tac category.seqI' [OF is_category])
            using \<psi>_in_hom
            using subcategory.in_hom_char [OF finite_subcat]
             apply blast
            using \<phi>_in_hom
            using subcategory.in_hom_char [OF finite_subcat]
            by blast

          show "partial_magma.ide (subcategory.comp pointed_set_comp FiniteArr')
     (subcategory.comp pointed_set_comp FiniteArr' \<psi> \<phi>)"
            apply (subst subcategory.ide_char [OF finite_subcat])
            apply (subst subcategory.arr_char [OF finite_subcat])
            apply auto
            using arr_\<psi>\<phi> subcategory.arr_char [OF finite_subcat] apply blast
            apply (subst ide_char)
            apply auto
          proof-
            have "FiniteArr'
   (subcategory.comp pointed_set_comp FiniteArr' \<psi> \<phi>)"
              using arr_\<psi>\<phi> subcategory.arr_char [OF finite_subcat] by blast
            then show arr'_\<psi>\<phi>: "Arr' (the
   (subcategory.comp pointed_set_comp FiniteArr' \<psi> \<phi>))"
              unfolding FiniteArr'_def
              using arr_char by blast
            have comp_\<psi>\<phi>: "(subcategory.comp pointed_set_comp FiniteArr' \<psi> \<phi>) =
                    Some (the \<psi> \<cdot> the \<phi>)"
              apply (subst subcategory.comp_char [OF finite_subcat])
              apply (simp add: arr_\<phi> arr_\<psi> seq\<psi>\<phi>)
              apply (subst comp_char)
              using arr_\<phi> subcategory.arr_char [OF finite_subcat] 
              unfolding FiniteArr'_def apply blast
              using arr_\<psi> subcategory.arr_char [OF finite_subcat] 
              unfolding FiniteArr'_def apply blast
              using seq\<psi>\<phi> apply blast
              by simp

            show "subcategory.comp pointed_set_comp FiniteArr' \<psi> \<phi> =
    Some (Id' (fst (snd (the (subcategory.comp pointed_set_comp FiniteArr' \<psi> \<phi>)))))"
              apply (subst comp_\<psi>\<phi>)
              apply (subst comp_\<psi>\<phi>)
              apply simp
              apply (rule_tac fun_eq_char)
            proof-
              show "Arr' (the \<psi> \<cdot> the \<phi>)"
                using arr'_\<psi>\<phi> comp_\<psi>\<phi> by simp
              then show "Arr' (Id' (fst (snd (the \<psi> \<cdot> the \<phi>))))"
                using classical_category.Arr_Id [OF ccpf dom_obj] by blast
              show "fst (snd (the \<psi> \<cdot> the \<phi>)) = fst (snd (Id' (fst (snd (the \<psi> \<cdot> the \<phi>)))))"
                unfolding Id'_def by simp
              have seq'\<psi>\<phi>: "snd (snd (the \<phi>)) = fst (snd (the \<psi>))"
                 apply (subst seq_char [OF \<open>B.arr \<phi>\<close> \<open>B.arr \<psi>\<close>])
                using seq\<psi>\<phi> apply blast
                by simp
              show "snd (snd (the \<psi> \<cdot> the \<phi>)) = snd (snd (Id' (fst (snd (the \<psi> \<cdot> the \<phi>)))))"
                unfolding Id'_def apply simp
                apply (subst dom_comp [OF arr'_\<phi> arr'_\<psi> seq'\<psi>\<phi>])
                apply (subst cod_comp [OF arr'_\<phi> arr'_\<psi> seq'\<psi>\<phi>])
                unfolding \<phi>_def \<psi>_def MkArr_def by simp
              fix x
              assume "x \<in> snd (fst (snd (the \<psi> \<cdot> the \<phi>)))"
              then have x_in_\<phi>: "x \<in> snd (fst (snd (the \<phi>)))"
                using dom_comp [OF arr'_\<phi> arr'_\<psi> seq'\<psi>\<phi>] by simp
              show "fst (the \<psi> \<cdot> the \<phi>) x = fst (Id' (fst (snd (the \<psi> \<cdot> the \<phi>)))) x"
                unfolding Comp'_def using arr'_\<phi> arr'_\<psi> seq'\<psi>\<phi> x_in_\<phi> apply simp
              proof-
                have "x \<in> snd (interval n)"
                  using x_in_\<phi> unfolding \<phi>_def MkArr_def by simp
                then have ex_m : "\<exists>m<n. x = K m" by simp
                then obtain m where m_def: "m < n \<and> x = K m" by auto
                then have "m \<in> {i. i<n}" by simp
                then have f2mb: "f2 m \<in> snd (fst (snd (the b)))"
                  using f2n_def unfolding bij_betw_def by blast 
                have m_some : "(SOME ma. ma < n \<and> f2 ma = f2 m) = m"
                proof
                  show "m < n \<and> f2 m = f2 m" by (simp add: m_def)
                  fix k
                  assume k_def: "k < n \<and> f2 k = f2 m" 
                  have inj: "\<And> x y. x < n \<Longrightarrow> y < n \<Longrightarrow> (f2 x = f2 y \<Longrightarrow> x = y)"
                    using f2n_def unfolding bij_betw_def inj_on_def by auto
                  show "k = m"
                    apply (rule_tac inj)
                    by (simp_all add: m_def k_def)
                qed
                show "fst (the \<psi>) (fst (the \<phi>) x) = fst (Id' (fst (snd (the \<phi>)))) x"
                  apply (subst m_def)
                  apply (subst m_def)
                  unfolding \<phi>_def MkArr_def using m_def apply simp
                  unfolding \<psi>_def MkArr_def using f2mb apply simp
                  apply (subst m_some)
                  unfolding Id'_def by simp
              qed
            qed
          qed
          show "partial_magma.ide (subcategory.comp pointed_set_comp FiniteArr')
     (subcategory.comp pointed_set_comp FiniteArr' \<phi> \<psi>)"
            apply (subst subcategory.ide_char [OF finite_subcat])
            apply (subst subcategory.arr_char [OF finite_subcat])
            apply auto
            using arr_\<phi>\<psi> subcategory.arr_char [OF finite_subcat] apply blast
            apply (subst ide_char)
            apply auto
          proof-
            have "FiniteArr'
   (subcategory.comp pointed_set_comp FiniteArr' \<phi> \<psi>)"
              using arr_\<phi>\<psi> subcategory.arr_char [OF finite_subcat] by blast
            then show arr'_\<phi>\<psi>: "Arr' (the
   (subcategory.comp pointed_set_comp FiniteArr' \<phi> \<psi>))"
              unfolding FiniteArr'_def
              using arr_char by blast
            have comp_\<phi>\<psi>: "(subcategory.comp pointed_set_comp FiniteArr' \<phi> \<psi>) =
                    Some (the \<phi> \<cdot> the \<psi>)"
              apply (subst subcategory.comp_char [OF finite_subcat])
              apply (simp add: arr_\<phi> arr_\<psi> seq\<phi>\<psi>)
              apply (subst comp_char)
              using arr_\<psi> subcategory.arr_char [OF finite_subcat] 
              unfolding FiniteArr'_def apply blast
              using arr_\<phi> subcategory.arr_char [OF finite_subcat] 
              unfolding FiniteArr'_def apply blast
              using seq\<phi>\<psi> apply blast
              by simp

            show "subcategory.comp pointed_set_comp FiniteArr' \<phi> \<psi> =
    Some (Id' (fst (snd (the (subcategory.comp pointed_set_comp FiniteArr' \<phi> \<psi>)))))"
              apply (subst comp_\<phi>\<psi>)
              apply (subst comp_\<phi>\<psi>)
              apply simp
              apply (rule_tac fun_eq_char)
            proof-
              show "Arr' (the \<phi> \<cdot> the \<psi>)"
                using arr'_\<phi>\<psi> comp_\<phi>\<psi> by simp
              then show "Arr' (Id' (fst (snd (the \<phi> \<cdot> the \<psi>))))"
                using classical_category.Arr_Id [OF ccpf dom_obj] by blast
              show "fst (snd (the \<phi> \<cdot> the \<psi>)) = fst (snd (Id' (fst (snd (the \<phi> \<cdot> the \<psi>)))))"
                unfolding Id'_def by simp
              have seq'\<phi>\<psi>: "snd (snd (the \<psi>)) = fst (snd (the \<phi>))"
                 apply (subst seq_char [OF \<open>B.arr \<psi>\<close> \<open>B.arr \<phi>\<close>])
                using seq\<phi>\<psi> apply blast
                by simp
              show "snd (snd (the \<phi> \<cdot> the \<psi>)) = snd (snd (Id' (fst (snd (the \<phi> \<cdot> the \<psi>)))))"
                unfolding Id'_def apply simp
                apply (subst dom_comp [OF arr'_\<psi> arr'_\<phi> seq'\<phi>\<psi>])
                apply (subst cod_comp [OF arr'_\<psi> arr'_\<phi> seq'\<phi>\<psi>])
                unfolding \<phi>_def \<psi>_def MkArr_def by simp
              fix x
              assume "x \<in> snd (fst (snd (the \<phi> \<cdot> the \<psi>)))"
              then have x_in_\<psi>: "x \<in> snd (fst (snd (the \<psi>)))"
                using dom_comp [OF arr'_\<psi> arr'_\<phi> seq'\<phi>\<psi>] by simp
              show "fst (the \<phi> \<cdot> the \<psi>) x = fst (Id' (fst (snd (the \<phi> \<cdot> the \<psi>)))) x"
                unfolding Comp'_def using arr'_\<psi> arr'_\<phi> seq'\<phi>\<psi> x_in_\<psi> apply simp
              proof-
                have x_in_b : "x \<in> snd (fst (snd (the b)))"
                  using x_in_\<psi> unfolding \<psi>_def MkArr_def by simp
                then have "x \<in> f2 ` {i. i < n}"
                  using f2n_def unfolding bij_betw_def by simp
                then obtain m where m_def : "m < n \<and> f2 m = x" by auto
                have m_some : "(SOME m. m < n \<and> f2 m = x) = m"
                proof
                  show "m < n \<and> f2 m = x" by (simp add: m_def)
                  fix k
                  assume k_def: "k < n \<and> f2 k = x"
                  have inj: "\<And> x y. x < n \<Longrightarrow> y < n \<Longrightarrow> (f2 x = f2 y \<Longrightarrow> x = y)"
                    using f2n_def unfolding bij_betw_def inj_on_def by auto
                  show "k = m"
                    apply (rule_tac inj)
                    by (simp_all add: k_def m_def)
                qed
                show "fst (the \<phi>) (fst (the \<psi>) x) = fst (Id' (fst (snd (the \<psi>)))) x"
                  unfolding \<psi>_def MkArr_def using x_in_\<psi> x_in_b apply simp
                  apply (subst m_some)
                  unfolding \<phi>_def MkArr_def using m_def apply simp
                  unfolding Id'_def by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed



theorem inclusion_ff_and_essurj: "fully_faithful_and_essentially_surjective_functor 
         pointed_finite_subcat
         pointed_fin_set.comp
         inclusionFunctor"
  unfolding fully_faithful_and_essentially_surjective_functor_def
  apply auto
  unfolding pointed_finite_subcat_def
  using subcategory.is_category [OF finite_subcat] apply simp
  using pointed_fin_set.is_category apply simp
   apply (rule_tac factorization.fully_faithful)
  using inclusion_factors_over_finite_sets apply simp
  using fully_faithful apply simp
  using inclusion_essentially_surjective
  unfolding pointed_finite_subcat_def.

theorem inclusion_equivalence: "equivalence_functor
         pointed_fin_set.comp
         pointed_finite_subcat
         inclusionFunctor"
  apply (rule_tac fully_faithful_and_essentially_surjective_functor.is_equivalence_functor)
  using inclusion_ff_and_essurj.


definition inclusion_inverse where
  "inclusion_inverse \<equiv> (SOME F. \<exists> \<eta> \<epsilon>. equivalence_of_categories
                         pointed_fin_set.comp pointed_finite_subcat F inclusionFunctor \<eta> \<epsilon>)"



lemma finset_equivalence: "\<exists>\<eta> \<epsilon>.  equivalence_of_categories
       pointed_fin_set.comp pointed_finite_subcat inclusion_inverse inclusionFunctor \<eta> \<epsilon>"
proof-
  have ex_F: "\<exists>F. (\<exists> \<eta> \<epsilon>.  equivalence_of_categories
       pointed_fin_set.comp pointed_finite_subcat F inclusionFunctor \<eta> \<epsilon>)"
    using equivalence_functor.induces_equivalence [OF inclusion_equivalence].
  show "(\<exists> \<eta> \<epsilon>.  equivalence_of_categories
       pointed_fin_set.comp pointed_finite_subcat inclusion_inverse
       inclusionFunctor \<eta> \<epsilon>)"
    unfolding inclusion_inverse_def
    using Hilbert_Choice.someI_ex [OF ex_F].
qed
    





end

end


