theory simplicialSet
  imports Main
         finitePointedSet
begin

locale simplex
begin


definition OrdArr where
  "OrdArr t \<equiv> (partial_magma.arr fin_set.comp t) \<and> (snd (the t) \<noteq> []) \<and> 
  (\<forall> i j. i \<le> j \<longrightarrow> j < (length (snd (the t))) \<longrightarrow> get (snd (the t)) i \<le> get (snd (the t)) j)"


interpretation subcategory fin_set.comp OrdArr
  unfolding subcategory_def apply (simp add: fin_set.is_category)
  unfolding subcategory_axioms_def apply auto
proof-
  show "\<And>f. OrdArr f \<Longrightarrow> partial_magma.arr fin_set.comp f"
    unfolding OrdArr_def by simp
  fix f
  assume "OrdArr f"
  from this have arr_f: "partial_magma.arr fin_set.comp f" by (simp add: OrdArr_def)
  from \<open>OrdArr f\<close> have f_nn: "snd (the f) \<noteq> []" by (simp add: OrdArr_def)
  from \<open>OrdArr f\<close> have f_monotone : " (\<forall>i j. i \<le> j \<longrightarrow> j < length (snd (the f)) \<longrightarrow> get (snd (the f)) i \<le> get (snd (the f)) j)" 
    by (simp add: OrdArr_def)

  have fst_f_nn : "fst (the f) \<noteq> 0"
  proof-
    have "partial_magma.arr fin_set.comp f \<longrightarrow> fin_set.Arr' (the f)"
      unfolding fin_set.comp_def apply (subst classical_category.arr_char)
      using fin_set.is_classical_category apply blast
      by simp
    then have "fin_set.Arr' (the f)" using arr_f by simp
    then have "get (snd (the f)) 0 < fst (the f)" unfolding fin_set.Arr'_def
      using f_nn by blast
    then show "fst (the f) \<noteq> 0" by auto
  qed

  have dom_f : "partial_magma.dom fin_set.comp f = Some (fin_set.Id' (length (snd (the f))))"
    unfolding fin_set.comp_def
    apply (subst classical_category.dom_char)
    using fin_set.is_classical_category apply blast
    using arr_f unfolding fin_set.comp_def by simp

  have dom_length: "length (snd (the (partial_magma.dom fin_set.comp f))) = length (snd (the f))"
    apply (simp add: dom_f)
    unfolding fin_set.Id'_def by simp

  show "OrdArr (partial_magma.dom fin_set.comp f)" 
    unfolding OrdArr_def apply auto
    using arr_f apply (simp add: category.arr_dom fin_set.is_category)
  proof-
    assume "snd (the (partial_magma.dom fin_set.comp f)) = []"
    then have "length (snd (the (partial_magma.dom fin_set.comp f))) = 0" by simp
    then show "False" by (simp add: dom_length f_nn)
  next
    fix i j
    assume "j < length (snd (the (partial_magma.dom fin_set.comp f)))"
    then have j_length: "j < length (snd (the f))" by (simp add: dom_length)
    assume "i \<le> j"
    then have i_length: "i < length (snd (the f))" using j_length by auto
    show "get (snd (the (partial_magma.dom fin_set.comp f))) i
           \<le> get (snd (the (partial_magma.dom fin_set.comp f))) j"
      apply (simp add: dom_f)
      unfolding fin_set.Id'_def apply simp
      using i_length j_length apply (simp add: get_rev_get)
      using \<open>i \<le> j\<close>.
  qed
  have cod_f : "partial_magma.cod fin_set.comp f = Some (fin_set.Id' (fst (the f)))"
    unfolding fin_set.comp_def
    apply (subst classical_category.cod_char)
    using fin_set.is_classical_category apply blast
    using arr_f unfolding fin_set.comp_def by simp
  have cod_length : "length (snd (the (partial_magma.cod fin_set.comp f))) = fst (the f)"
    apply (simp add: cod_f)
    unfolding fin_set.Id'_def by simp

  show "OrdArr (partial_magma.cod fin_set.comp f)"
    unfolding OrdArr_def apply auto
    using arr_f apply (simp add: category.arr_cod fin_set.is_category)
  proof-
    assume "snd (the (partial_magma.cod fin_set.comp f)) = []"
    then have "length (snd (the (partial_magma.cod fin_set.comp f))) = 0" by simp
    then have "fst (the f) = 0" by (simp add: cod_length)
    then show "False" by (simp add: fst_f_nn)
  next
    fix i j
    assume "j < length (snd (the (partial_magma.cod fin_set.comp f)))"
    then have j_length : "j < fst (the f)" by (simp add: cod_length)
    assume "i \<le> j"
    then have i_length : "i < fst (the f)" using j_length by auto
    then show "get (snd (the (partial_magma.cod fin_set.comp f))) i
           \<le> get (snd (the (partial_magma.cod fin_set.comp f))) j"
      apply (simp add: cod_f)
      unfolding fin_set.Id'_def apply simp
      apply (simp add: get_rev_get i_length j_length)
      using \<open>i \<le> j\<close>.
  qed
  fix g
  assume "OrdArr g"
  then have arr_g: "partial_magma.arr fin_set.comp g" by (simp add: \<open>\<And>f. OrdArr f \<Longrightarrow> partial_magma.arr fin_set.comp f\<close>)
  
  from \<open>OrdArr g\<close> have g_monotone : "(\<forall>i j. i \<le> j \<longrightarrow> j < length (snd (the g)) \<longrightarrow> get (snd (the g)) i \<le> get (snd (the g)) j)"
    by (simp add: OrdArr_def)
  have dom_g : "partial_magma.dom fin_set.comp g = Some (fin_set.Id' (length (snd (the g))))"
    unfolding fin_set.comp_def
    apply (subst classical_category.dom_char)
    using fin_set.is_classical_category apply blast
    using arr_g unfolding fin_set.comp_def by simp
  
  assume seq: "partial_magma.cod fin_set.comp f = partial_magma.dom fin_set.comp g"
  then have seq2: " fst (the f) = length (snd (the g))" apply (simp add: cod_f dom_g)
    unfolding fin_set.Id'_def by simp

  have arr_char: "\<And>f. partial_magma.arr fin_set.comp f \<longrightarrow> f \<noteq> None \<and>
        fin_set.Arr' (the f)"
    unfolding fin_set.comp_def
    apply (subst classical_category.arr_char)
    using fin_set.is_classical_category apply blast
    by simp
    

  have gf_comp: "fin_set.comp g f =  Some (fin_set.Comp' (the g) (the f))"
    unfolding fin_set.comp_def apply (subst classical_category.comp_char)
    using fin_set.is_classical_category apply blast
    using arr_f arr_g arr_char apply simp
    by (simp add: seq2)

  have comp_length : "length (snd (the (fin_set.comp g f))) = length (snd (the f))"
    apply (simp add: gf_comp)
    unfolding fin_set.Comp'_def by simp

  show " OrdArr (fin_set.comp g f)"
    unfolding OrdArr_def apply auto
      apply (simp add: arr_g arr_f category.seqI fin_set.is_category seq)
  proof-
    assume "snd (the (fin_set.comp g f)) = []"
    then have "length (snd (the (fin_set.comp g f))) = 0" by simp
    then have "length (snd (the f)) = 0" by (simp add: comp_length)
    then show "False" by (simp add: f_nn)
  next
    fix i j
    assume "j < length (snd (the (fin_set.comp g f)))"
    then have j_length_f : "j < length (snd (the f))" by (simp add: comp_length)
    assume "i \<le> j"
    then have i_length_f : "i < length (snd (the f))" using j_length_f by auto

    have fi_fj : "get (snd (the f)) i \<le> get (snd (the f)) j"
      apply (subst f_monotone)
      by (simp_all add: \<open>i \<le> j\<close> j_length_f)

    have j_length_g : "get (snd (the f)) j < length (snd (the g))"
    proof-
      have "fin_set.Arr' (the f)" using arr_f by (simp add: arr_char)
      then have "get (snd (the f)) j < fst (the f)" 
        unfolding fin_set.Arr'_def by (simp add: j_length_f)
      then show "get (snd (the f)) j < length (snd (the g))" by (simp add: seq2)
    qed

    show "get (snd (the (fin_set.comp g f))) i \<le> get (snd (the (fin_set.comp g f))) j"
      apply (simp add: gf_comp)
      unfolding fin_set.Comp'_def apply simp
      apply (simp add: get_rev_get i_length_f j_length_f)
      apply (subst g_monotone)
      by (simp_all add: fi_fj j_length_g)
  qed
qed



definition comp where "comp \<equiv> local.comp"


end


(*TODO: -Define complexes
        -The augmented free abelian group complex on a pointed simplicial set
        -Homology groups of a complex*)



end
