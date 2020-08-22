theory SimplicialSet
  imports Main
         Gamma
         PointedSet
         "Category3.DualCategory"
         SomeCategoryTheory
begin






locale simplex
begin


definition OrdArr where
  "OrdArr t \<equiv> (partial_magma.arr fin_set.comp t) \<and> (snd (the t) \<noteq> []) \<and> 
  (\<forall> i j. i \<le> j \<longrightarrow> j < (length (snd (the t))) \<longrightarrow> get (snd (the t)) i \<le> get (snd (the t)) j)"


interpretation S: subcategory fin_set.comp OrdArr
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
      using i_length j_length apply simp
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






definition d :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat list) option" where
  "d n k = Some (Suc n, rev_get n (\<lambda>x. if x < k then x else Suc x))"


definition comp where "comp \<equiv> dual_category.comp S.comp"

lemma is_category : "category comp"
  unfolding comp_def
  apply (rule_tac dual_category.is_category)
  unfolding dual_category_def
  using S.is_category.

lemma is_dual_category : "dual_category S.comp"
  unfolding dual_category_def
  using S.is_category.

lemma is_subcategory: "subcategory fin_set.comp OrdArr"
  using S.subcategory_axioms.


lemma arr_char: "partial_magma.arr comp f = OrdArr f"
  unfolding comp_def
  unfolding dual_category.arr_char [OF is_dual_category]
  unfolding S.arr_char
  by simp

lemma ide_char: "partial_magma.ide comp b = 
     (OrdArr b \<and> b = Some (fin_set.Id' (length (snd (the b)))))"
  unfolding comp_def
  unfolding dual_category.ide_char [OF is_dual_category]
  unfolding S.ide_char
  unfolding S.arr_char
  unfolding fin_set.ide_char
  apply auto
  unfolding OrdArr_def
  unfolding fin_set.arr_char
  by simp




lemma dom_char: "partial_magma.arr comp f \<Longrightarrow> 
                 partial_magma.dom comp f = Some (fin_set.Id' (fst (the f)))"
  unfolding comp_def
  unfolding dual_category.arr_char [OF is_dual_category]
  unfolding dual_category.dom_char [OF is_dual_category]
  unfolding S.cod_char
  apply simp
  unfolding S.arr_char OrdArr_def
  unfolding fin_set.comp_def
  unfolding classical_category.cod_char [OF fin_set.is_classical_category]
  by simp
lemma cod_char: "partial_magma.arr comp f \<Longrightarrow> 
                 partial_magma.cod comp f = Some (fin_set.Id' (length (snd (the f))))"
  unfolding comp_def
  unfolding dual_category.arr_char [OF is_dual_category]
  unfolding dual_category.cod_char [OF is_dual_category]
  unfolding S.dom_char
  apply simp
  unfolding S.arr_char OrdArr_def
  unfolding fin_set.comp_def
  unfolding classical_category.dom_char [OF fin_set.is_classical_category]
  by simp

lemma comp_char : assumes arr_gf: "partial_magma.seq comp g f" 
  shows "comp g f = Some (fin_set.Comp' (the f) (the g))"
  using arr_gf
  unfolding comp_def
  unfolding dual_category.arr_char [OF is_dual_category]
  unfolding dual_category.comp_char [OF is_dual_category]
  apply (subst S.comp_char)
  unfolding S.seq_char
  apply simp
  unfolding subcategory.arr_char [OF is_subcategory]
  unfolding OrdArr_def
  unfolding fin_set.comp_def
  unfolding classical_category.arr_char [OF fin_set.is_classical_category]
  unfolding classical_category.comp_char [OF fin_set.is_classical_category]
  by meson





lemma ide_D0: "partial_magma.ide comp (Some (1, [0]))"
  unfolding comp_def
  unfolding dual_category.ide_char [OF is_dual_category]
  unfolding subcategory.ide_char [OF is_subcategory]
  unfolding subcategory.arr_char [OF is_subcategory]
  unfolding OrdArr_def
  unfolding fin_set.comp_def
  unfolding classical_category.ide_char [OF fin_set.is_classical_category]
  unfolding classical_category.arr_char [OF fin_set.is_classical_category]
  apply simp
  unfolding fin_set.Arr'_def fin_set.Id'_def
  by simp

lemma ide_Dn : "n > 0 \<Longrightarrow> partial_magma.ide comp (Some (fin_set.Id' n))"
  unfolding comp_def
  unfolding dual_category.ide_char [OF is_dual_category]
  unfolding S.ide_char
  unfolding S.arr_char 
  unfolding OrdArr_def
  unfolding fin_set.comp_def
  unfolding classical_category.ide_char [OF fin_set.is_classical_category]
  unfolding classical_category.arr_char [OF fin_set.is_classical_category]
  apply (simp add: classical_category.Arr_Id [OF fin_set.is_classical_category])
  unfolding fin_set.Id'_def apply simp
proof-
  have "0 < n \<Longrightarrow> length (rev_get n (\<lambda>k. k)) \<noteq> length []"
    by simp
  then show "0 < n \<Longrightarrow> rev_get n (\<lambda>k. k) \<noteq> []"
    by force
qed


lemma d_in_hom : assumes "n > 0"
  shows "partial_magma.in_hom comp (d n k) (Some (fin_set.Id' (Suc n))) (Some (fin_set.Id' n))"
  unfolding local.comp_def
  unfolding dual_category.hom_char [OF is_dual_category]
  unfolding S.in_hom_char
  apply safe
  using ide_Dn [OF \<open>0 < n\<close>]
  unfolding local.comp_def
  unfolding dual_category.ide_char [OF is_dual_category] apply simp
  using ide_Dn
  unfolding local.comp_def
  unfolding dual_category.ide_char [OF is_dual_category] apply simp
proof-
  have "S.C.arr (d n k)"
    unfolding d_def
    unfolding fin_set.comp_def classical_category.arr_char [OF fin_set.is_classical_category]
    unfolding fin_set.Arr'_def by simp
  show "S.arr (d n k)"
    unfolding S.arr_char OrdArr_def
    using \<open>S.C.arr (d n k)\<close> 
    unfolding d_def apply simp
  proof
    have "length (rev_get n (\<lambda>x. if x < k then x else Suc x)) \<noteq> length []" 
      by (simp add: \<open>n > 0\<close>)
    then show "rev_get n (\<lambda>x. if x < k then x else Suc x) = [] \<Longrightarrow> False"
      by force
  qed
  show "S.C.in_hom (d n k) (Some (fin_set.Id' n)) (Some (fin_set.Id' (Suc n)))"
    apply (rule_tac S.C.in_homI)
    using \<open>S.C.arr (d n k)\<close> apply blast
    using \<open>S.C.arr (d n k)\<close>
    unfolding fin_set.comp_def
    unfolding classical_category.dom_char [OF fin_set.is_classical_category]
    apply (simp add: d_def)
    using \<open>S.C.arr (d n k)\<close>
    unfolding fin_set.comp_def
    unfolding classical_category.cod_char [OF fin_set.is_classical_category]
    by (simp add: d_def)
qed
 

end


context category 
begin

fun comp_list :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "comp_list [] d = d" |
  "comp_list (x # xs) d = C (comp_list xs (cod x)) x"

fun list_seq :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "list_seq [] d c = (ide d \<and> c = d)" |
  "list_seq (x # xs) d c = (arr x \<and> dom x = d \<and> (list_seq xs (cod x) c))"

lemma comp_list_in_hom :
  assumes  "list_seq xs d c"
  shows "in_hom (comp_list xs d) d c"
proof-
  have "list_seq xs d c \<longrightarrow> in_hom (comp_list xs d) d c"
    apply (induction xs arbitrary: d)
    by auto
  from this and assms show ?thesis by simp
qed

end

context simplex
begin

definition inc :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat list) option" where
  "inc k n = Some (n, [k])"

interpretation D: category comp
  using is_category.

lemma inc_in_hom : assumes "k < n"
  shows "D.in_hom (inc k n) (Some (fin_set.Id' n)) (Some (fin_set.Id' 1))"
  apply (rule_tac D.in_homI)
proof-
  show arr: "D.arr (inc k n)"
    unfolding arr_char OrdArr_def fin_set.arr_char
    apply (simp add: inc_def)
    unfolding fin_set.Arr'_def
    by (simp add: \<open>k < n\<close>)
  show "D.dom (inc k n) = Some (fin_set.Id' n)"
    apply (subst dom_char)
    using arr apply simp
    unfolding inc_def by simp
  show "D.cod (inc k n) = Some (fin_set.Id' 1)"
    apply (subst cod_char)
    using arr apply simp
    unfolding inc_def by simp
qed

lemma arr_to_inc : assumes f_in_hom: "D.in_hom f n (Some (fin_set.Id' 1))"
  shows "f = (inc (get (snd (the f)) 0) (fst (the n)))"
proof-
  define k where "k = get (snd (the f)) 0"
  show "f = inc k (fst (the n))"
    apply (rule_tac D.in_homE [OF f_in_hom])
    unfolding inc_def
    unfolding dom_char cod_char
    unfolding arr_char OrdArr_def fin_set.arr_char
    unfolding fin_set.Id'_def
    apply auto
    apply (rule_tac getFaithful)
     apply simp
    unfolding k_def
    by simp
qed

fun d_chain :: "nat list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat list) option list" where
  "d_chain xs n = rev_get (length xs) (\<lambda>k. (d (n - k) (get xs k)))"

lemma d_chain_arr :
  shows "length xs \<le> n \<Longrightarrow> D.list_seq (d_chain xs n) (Some (fin_set.Id' (Suc n))) 
          (Some (fin_set.Id' (Suc n - length xs)))"
  apply (induction xs arbitrary: n)
   apply (simp add: ide_Dn)
  apply simp
proof-
  fix a xs n
  assume ind : "(\<And>n. length xs \<le> n \<Longrightarrow>
             D.list_seq (rev_get (length xs) (\<lambda>k. d (n - k) (get xs k)))
              (Some (fin_set.Id' (Suc n))) (Some (fin_set.Id' (Suc n - length xs))))"
  assume "Suc (length xs) \<le> n"
  then have "n > 0" by simp
  from \<open>Suc (length xs) \<le> n\<close> have "length xs \<le> n - 1" by simp
  from this and ind have "D.list_seq (rev_get (length xs) (\<lambda>k. d ((n-1) - k) (get xs k)))
              (Some (fin_set.Id' (Suc (n-1)))) (Some (fin_set.Id' (Suc (n-1) - length xs)))"
    by blast
  then show "D.arr (d n a) \<and>
       D.dom (d n a) = Some (fin_set.Id' (Suc n)) \<and>
       D.list_seq (rev_get (length xs) (\<lambda>k. d (n - Suc k) (get xs k))) (D.cod (d n a))
        (Some (fin_set.Id' (n - length xs)))"
    apply (simp add: \<open>n > 0\<close>)
    unfolding D.in_hom_cod [OF d_in_hom [OF \<open>n > 0\<close>]]
    apply simp
    using d_in_hom [OF \<open>n > 0\<close>] by blast
qed




lemma inc0_to_d_chain: 
  shows "inc 0 (Suc n) = D.comp_list (d_chain (rev_get n Suc) n) (Some (fin_set.Id' (Suc n)))"
proof-
  have "length (rev_get n Suc) \<le> n" by simp
  then have in_hom: "D.in_hom (D.comp_list (d_chain (rev_get n Suc) n) (Some (fin_set.Id' (Suc n)))) 
                   (Some (fin_set.Id' (Suc n))) (Some (fin_set.Id' 1))"
    apply (rule_tac D.comp_list_in_hom)
    using d_chain_arr [OF \<open>length (rev_get n Suc) \<le> n\<close>]
    by simp
  then have arr : "D.arr (D.comp_list (d_chain (rev_get n Suc) n) (Some (fin_set.Id' (Suc n))))"
    by blast
  have EQ: "\<And>xs. (\<forall>k < length xs. 0 < get xs k) \<Longrightarrow> length xs = n \<Longrightarrow>
             (get (snd (the (D.comp_list (d_chain xs n)
                         (Some (fin_set.Id' (Suc n)))))) 0) = 0"
    apply (induction n)
     apply (simp add: fin_set.Id'_def)
  proof-
    fix n 
    fix xs :: "nat list"
    assume ind: "(\<And>xs. \<forall>k<length xs. 0 < get xs k \<Longrightarrow>
              length xs = n \<Longrightarrow>
              get (snd (the (D.comp_list (d_chain xs n) (Some (fin_set.Id' (Suc n))))))
               0 = 0)"
    assume "\<forall>k<length xs. 0 < get xs k"
    assume "length xs = Suc n"
    then have "xs \<noteq> []" by auto
    then obtain a ys where a_ys_def : "xs = a # ys" 
      apply (cases xs)
      by simp_all
    have "0 < length xs"
      using \<open>length xs = Suc n\<close> by simp
    then have "0 < get xs 0"
      using \<open>\<forall>k<length xs. 0 < get xs k\<close> by simp
    then have "0 < a"
      unfolding a_ys_def by simp
    have EQ: "(get (snd (the (D.comp_list (rev_get (length ys) (\<lambda>k. d (n - k) (get ys k)))
                      (D.cod (d (Suc n) a))))) 0) = 0"
      apply (subst D.in_hom_cod [OF d_in_hom])
       apply simp
      unfolding reverse_equality [OF d_chain.simps]
      apply (rule_tac ind)
      using \<open>\<forall>k<length xs. 0 < get xs k\<close>
      unfolding a_ys_def apply auto
      using \<open>length xs = Suc n\<close>
      unfolding a_ys_def by simp
    have in_hom: "D.in_hom
     (D.comp_list (rev_get (length ys) (\<lambda>k. d (n - k) (get ys k)))
       (Some (fin_set.Id' (Suc n))))
     (Some (fin_set.Id' (Suc n))) 
     (Some (fin_set.Id' (Suc n - length ys)))"
      apply (rule_tac D.comp_list_in_hom)
      unfolding reverse_equality [OF d_chain.simps]
      apply (rule_tac d_chain_arr)
      using \<open>length xs = Suc n\<close>
      unfolding a_ys_def by simp

    have seq : "D.seq
     (D.comp_list (rev_get (length ys) (\<lambda>k. d (n - k) (get ys k)))
       (D.cod (d (Suc n) a)))
     (d (Suc n) a)"
      apply (rule_tac D.seqI')
      using d_in_hom apply blast
      apply (subst D.in_hom_cod [OF d_in_hom])
       apply simp
      using in_hom.
    have length_nn: "0 < length
         (snd (the (D.comp_list (rev_get (length ys) (\<lambda>k. d (n - k) (get ys k)))
                     (D.cod (d (Suc n) a)))))"
      apply (subst D.in_hom_cod [OF d_in_hom])
       apply simp
      apply (rule_tac D.in_homE [OF in_hom])
      unfolding arr_char OrdArr_def
      by simp

    show "get (snd (the (D.comp_list (d_chain xs (Suc n))
         (Some (fin_set.Id' (Suc (Suc n))))))) 0 = 0"
      apply simp
      unfolding a_ys_def
      apply simp
      apply (subst comp_char [OF seq])
      unfolding fin_set.Comp'_def
      apply simp
      apply (subst get_rev_get)
      unfolding EQ
      using length_nn apply simp
      unfolding d_def
      using \<open>0 < a \<close>by simp
  qed
  show "inc 0 (Suc n) = D.comp_list (d_chain (rev_get n Suc) n) (Some (fin_set.Id' (Suc n)))"
    apply (subst arr_to_inc [OF in_hom])
    apply (subst EQ)
    by (simp_all add: fin_set.Id'_def)
qed


lemma inc_to_d_chain:
   "k \<le> n \<Longrightarrow> \<exists>xs. length xs = n \<and> inc k (Suc n) = D.comp_list (d_chain xs n) (Some (fin_set.Id' (Suc n)))"
  apply (induction k arbitrary: n)
   apply (subst inc0_to_d_chain)
   apply (rule_tac exI)
proof-
  fix n
  show "length (rev_get n Suc) = n \<and>
         D.comp_list (d_chain (rev_get n Suc) n) (Some (fin_set.Id' (Suc n))) =
         D.comp_list (d_chain (rev_get n Suc) n) (Some (fin_set.Id' (Suc n)))"
    by simp
next
  fix k n
  assume ind : "(\<And>n. k \<le> n \<Longrightarrow>
                \<exists>xs. length xs = n \<and> inc k (Suc n) =
                D.comp_list (d_chain xs n) (Some (fin_set.Id' (Suc n))))"
  assume "Suc k \<le> n"
  then have "k \<le> n - 1" by auto
  from \<open>Suc k \<le> n\<close> have "0 < n" by simp
  obtain xs where "length xs = (n-1) \<and> inc k (Suc (n-1)) =
                D.comp_list (d_chain xs (n-1)) (Some (fin_set.Id' (Suc (n-1))))"
    using ind [OF \<open>k \<le> n - 1\<close>] by auto
  then have xs_def: "length xs = (n-1) \<and> inc k n =
                D.comp_list (d_chain xs (n-1)) (Some (fin_set.Id' n))"
    using \<open>0 < n\<close> by simp
  have EQ: "inc (Suc k) (Suc n) = comp (inc k n) (d n k)"
    apply (subst comp_char)
     apply (rule_tac D.seqI')
      apply (rule_tac d_in_hom [OF \<open>0 < n\<close>])
     apply (rule_tac inc_in_hom)
    using \<open>Suc k \<le> n\<close> apply simp
    unfolding fin_set.Comp'_def inc_def d_def
    apply simp
    apply (subst get_rev_get)
    using \<open>Suc k \<le> n\<close> apply simp
    by simp
  show "\<exists>xs. length xs = n \<and> inc (Suc k) (Suc n) =
                D.comp_list (d_chain xs n) (Some (fin_set.Id' (Suc n)))"
  proof
    show "length (k # xs) = n \<and> inc (Suc k) (Suc n) =
           D.comp_list (d_chain (k # xs) n) (Some (fin_set.Id' (Suc n)))"
      apply simp
      apply (subst conjunct1 [OF xs_def])
      apply (subst EQ)
      apply (simp add: \<open>0 < n\<close>)
      apply (subst conjunct2 [OF xs_def])
      apply (subst D.in_hom_cod [OF d_in_hom])
      using \<open>0 < n\<close> apply simp
      by simp
  qed
qed



lemma in_hom_get_bound :
  assumes in_hom: "D.in_hom f (Some (fin_set.Id' a)) (Some (fin_set.Id' b))" 
  and "k < b"
shows "get (snd (the f)) k < a"
proof-
  from in_hom have arr: "D.arr f"
    by blast
  then have bound_rule: "(\<And>n. n<length (snd (the f)) \<Longrightarrow> get (snd (the f)) n < fst (the f))"
    unfolding arr_char OrdArr_def fin_set.arr_char fin_set.Arr'_def
    by simp
  have "get (snd (the f)) k < fst (the f)"
    apply (rule_tac bound_rule)
    using \<open>k < b\<close>
    using D.in_hom_cod [OF in_hom]
    unfolding cod_char [OF arr]
    unfolding fin_set.Id'_def
    by simp
  then show "get (snd (the f)) k < a"
    using D.in_hom_dom [OF in_hom]
    unfolding dom_char [OF arr]
    unfolding fin_set.Id'_def
    by simp
qed





lemma simplicial_identity_d_d : 
  assumes "i < j"
  and "0 < n"
  shows "comp (d n i) (d (Suc n) j) =
         comp (d n (j - 1)) (d (Suc n) i)"
  apply (subst comp_char)
   apply (rule_tac D.seqI')
  using d_in_hom apply blast
   apply (rule_tac d_in_hom)
  using \<open>0 < n\<close> apply simp
  apply (subst comp_char)
   apply (rule_tac D.seqI')
  using d_in_hom apply blast
   apply (rule_tac d_in_hom)
  using \<open>0 < n\<close> apply simp
  unfolding fin_set.Comp'_def
  apply auto
   apply (simp add: d_def)
  apply (rule_tac getFaithful)
   apply (simp add: d_def)
  apply simp
  apply (subst get_rev_get)
   apply (simp add: d_def)
proof-
  define m where "m = Suc n"
  fix k
  assume "k < length (snd (the (d n i)))"
  then have "k < n"
    unfolding d_def by simp
  then have "k < m"
    unfolding m_def by simp
  from \<open>k < n\<close> have "Suc k < m"
    unfolding m_def by simp

  show "get (snd (the (d (Suc n) j)))
           (get (snd (the (d n i))) k) =
          get (snd (the (d (Suc n) i)))
           (get (snd (the (d n (j - Suc 0)))) k)"
    unfolding reverse_equality [OF m_def]
    unfolding d_def
    apply (simp add: \<open>k < n\<close> \<open>k < m\<close> \<open>Suc k < m\<close>)
    using \<open>i < j\<close> by auto
qed



end




locale pointed_simplicial_set =
  X: "functor" simplex.comp pointed_set.pointed_set_comp X
  for X :: "(nat \<times> nat list) option \<Rightarrow> 'a pointed_set.parr option"
begin

lemma is_functor: "functor simplex.comp pointed_set.pointed_set_comp X"
  using X.functor_axioms.


interpretation simplex.


definition simplices :: "nat \<Rightarrow> 'a pointed_set" where
  "simplices n = pointed_set.Dom' (the (X (Some (fin_set.Id' (Suc n)))))"

lemma simplices_obj : "pointed_set.Obj' (simplices n)"
  using X.preserves_ide [OF ide_Dn]
  unfolding simplices_def
  unfolding pointed_set.ide_char
  unfolding pointed_set.Arr'_def
  by simp

definition pi0prerelation :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "pi0prerelation x y = (x \<in> snd (simplices 0) \<and> y \<in> snd (simplices 0) \<and>
                     (\<exists> z \<in> snd (simplices 1). 
                      fst (the (X (d 1 0))) z = x \<and>
                      fst (the (X (d 1 1))) z = y ))"

definition pi0relation :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "pi0relation = generated_equiv_rel (snd (simplices 0)) pi0prerelation"





end



end
