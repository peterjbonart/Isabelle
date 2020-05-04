theory H_Ab
  imports Main
         "HOL-Algebra.Group"
         pointedSet
begin


lemma fmap_length : "length (fmap f xs) = length xs"
  by simp

lemma fmap_preserves_inj : assumes xs_ys_eq: "fmap f xs = fmap f ys" 
and f_inj: "(\<And>x y. f x = f y \<Longrightarrow> x = y)"
  shows "xs = ys"
proof-
  show "xs = ys"
    apply (rule_tac getFaithful)
  proof-
    from xs_ys_eq have "length (fmap f xs) = length (fmap f ys)"
      by simp
    then show "length xs = length ys" using fmap_length by simp
    fix n
    assume "n < length xs"
    then have "n < length ys"
      using \<open>length xs = length ys\<close> by simp
    have eq_x: "get (rev_get (length xs) (\<lambda>n. f (get xs n))) n = f (get xs n)"
      by (simp add: get_rev_get [OF \<open>n < length xs\<close>])
    have eq_y: "get (rev_get (length ys) (\<lambda>n. f (get ys n))) n = f (get ys n)"
      by (simp add: get_rev_get [OF \<open>n < length ys\<close>])
    have "get (rev_get (length xs) (\<lambda>n. f (get xs n))) n = get (rev_get (length ys) (\<lambda>n. f (get ys n))) n"
      using xs_ys_eq by simp
    from this and eq_x and eq_y have "f (get xs n) = f (get ys n)" by simp
    then show "get xs n = get ys n"
      apply (rule_tac f_inj)
      by simp
  qed
qed



lemma fmap_image : assumes xs_in_S: "\<forall>k < length xs . get xs k \<in> f ` S"
  shows "\<exists> as. xs = fmap f as \<and> (\<forall>k < length xs. get as k \<in> S)"
proof
  define as where "as = rev_get (length xs) (\<lambda>k. (SOME a. get xs k = f a \<and> a \<in> S))"
  have length_eq : "length as = length xs" unfolding as_def by simp
  show "xs = fmap f as \<and> (\<forall>k<length xs. get as k \<in> S)"
    apply auto
     apply (rule_tac getFaithful)
    unfolding as_def apply simp
     apply simp_all
  proof-
    fix k
    assume "k < length xs"
    define P where "P = (\<lambda>a. get xs k = f a \<and> a \<in> S)"
    have ex_a: "\<exists>a. P a"
      unfolding P_def
      using xs_in_S \<open>k < length xs\<close> by auto
    have p_a: "P (SOME a. P a)"
      using someI_ex [OF ex_a].
    from p_a show "get xs k = f (SOME a. get xs k = f a \<and> a \<in> S)"
      unfolding P_def by simp
    from p_a show "(SOME a. get xs k = f a \<and> a \<in> S) \<in> S"
      unfolding P_def by simp
  qed
qed


context comm_group
begin


definition merge_with_zeros :: "'a list \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a list" where
  "merge_with_zeros xs P = rev_get (length xs) (\<lambda>k. if P k then (get xs k) else \<one>)"

lemma merge_with_zeros_length [simp]: "length (merge_with_zeros xs P) = length xs"
  unfolding merge_with_zeros_def by simp

lemma merge_with_zeros_add : "merge_with_zeros (a # as) P = 
     (if P 0 then a else \<one>) # (merge_with_zeros as (\<lambda>i. P (Suc i)))"
  unfolding merge_with_zeros_def
  apply (rule_tac getFaithful)
   apply (simp add: app_length)
proof-
  fix n
  assume "n < length (rev_get (length (a # as)) (\<lambda>k. if P k then get (a # as) k else \<one>))"
  then have "n < length (a # as)" by (simp add: app_length)
  have "n < length (a # as) \<Longrightarrow> get (rev_get (length (a # as)) (\<lambda>k. if P k then get (a # as) k else \<one>)) n =
         get ((if P 0 then a else \<one>) # rev_get (length as) (\<lambda>k. if P (Suc k) then get as k else \<one>)) n"
    apply (subst get_rev_get [OF \<open>n < length (a # as)\<close>])
    apply (induction n)
     apply simp
    by simp
  then show "get (rev_get (length (a # as)) (\<lambda>k. if P k then get (a # as) k else \<one>)) n =
         get ((if P 0 then a else \<one>) # rev_get (length as) (\<lambda>k. if P (Suc k) then get as k else \<one>)) n"
    using \<open>n < length (a # as)\<close> by simp
qed
    

fun sum :: "'a list \<Rightarrow> 'a" where
  "sum [] = \<one>" |
  "sum (x # xs) = (\<otimes>) x (sum xs)"

lemma zero_sum: "\<forall>k < length xs. get xs k = \<one> \<Longrightarrow> sum xs = \<one>"
  apply (induction xs)
   apply simp
proof-
  fix a xs
  assume ind: "(\<forall>k<length xs. get xs k = \<one> \<Longrightarrow> local.sum xs = \<one>)"
  assume hyp: "\<forall>k<length (a # xs). get (a # xs) k = \<one>"
  from hyp have "\<forall>k<length xs. get xs k = \<one>" by auto
  then have sum_1: "local.sum xs = \<one>" using ind by simp
  from hyp have a_1: "a = \<one>" by auto
  show "local.sum (a # xs) = \<one>"
    using sum_1 a_1 by simp
qed






lemma one_sum :" (i < length xs \<and> (\<forall>k < length xs. k \<noteq> i \<longrightarrow> get xs k = \<one>)) \<and> 
          get xs i \<in> carrier G \<Longrightarrow> sum xs = get xs i"
  apply (induction xs arbitrary: i)
   apply simp
  apply auto
proof-
  fix a xs i
  assume ind: "(\<And>i. i < length xs \<and> (\<forall>k<length xs. k \<noteq> i \<longrightarrow> get xs k = \<one>) \<and>
             get xs i \<in> carrier G \<Longrightarrow> local.sum xs = get xs i)"
  assume in_G: "get (a # xs) i \<in> carrier G"
  assume "i < Suc (length xs)"
  assume hyp: "\<forall>k<Suc (length xs). k \<noteq> i \<longrightarrow> get (a # xs) k = \<one>" 
  have "i > 0 \<or> i = 0" by auto
  then show "a \<otimes> local.sum xs = get (a # xs) i"
  proof
    assume "i > 0"
    then have "i = Suc (i-1)" by simp
    then obtain j where j_def: "i = Suc j" by auto 
    have j_in_G: "get xs j \<in> carrier G"
      using j_def in_G by simp
    have "j < length xs \<and> (\<forall>k<length xs. k \<noteq> j \<longrightarrow> get xs k = \<one>) \<and> get xs j \<in> carrier G"
      apply safe
      using j_def \<open>i < Suc (length xs)\<close> apply simp
      using j_def hyp apply auto
      using j_in_G.
    then have sum_eq: "local.sum xs = get xs j"
      using ind by simp
    from \<open>i > 0\<close> have a_eq: "a = \<one>"
      using hyp by auto
    have "\<And>x. x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x" by simp
    show "a \<otimes> local.sum xs = get (a # xs) i"
      apply (subst a_eq)
      apply (subst sum_eq)
      using j_in_G apply simp
      using j_def by simp
  next
    assume "i = 0"
    have "local.sum xs = \<one>"
      apply (rule_tac zero_sum)
      using hyp \<open>i = 0\<close> by auto
    then show "a \<otimes> local.sum xs = get (a # xs) i"
      using in_G \<open>i = 0\<close> by simp
  qed
qed

lemma sum_carrier : "\<forall>k < length xs. get xs k \<in> carrier G \<Longrightarrow> sum xs \<in> carrier G"
  apply (induction xs)
   apply simp
proof-
  fix a xs
  assume ind: " (\<forall>k<length xs. get xs k \<in> carrier G \<Longrightarrow> local.sum xs \<in> carrier G)"
  assume hyp: "\<forall>k<length (a # xs). get (a # xs) k \<in> carrier G"
  have "\<forall>k<length xs. get xs k \<in> carrier G"
    using hyp by auto
  then have sum_in_G: "local.sum xs \<in> carrier G"
    apply (rule_tac ind) 
    by simp
  from hyp have "get (a # xs) 0 \<in> carrier G"
    by blast
  then have a_in_G: "a \<in> carrier G"
    by simp
  show "local.sum (a # xs) \<in> carrier G"
    using a_in_G sum_in_G by simp
qed

lemma binary_sum_sum : "\<forall>k < length ys. get ys k \<in> carrier G \<Longrightarrow> 
             \<forall>k < length xs. get xs k \<in> carrier G \<Longrightarrow>
                 length xs = length ys \<Longrightarrow>
               sum (rev_get (length xs) (\<lambda>k. get xs k \<otimes> get ys k)) = sum xs \<otimes> sum ys"
  apply (induction xs arbitrary: ys)
   apply simp
  apply simp
proof-
  fix a xs ys
  assume ind : "(\<And>ys. \<forall>k<length ys. get ys k \<in> carrier G \<Longrightarrow>
              \<forall>k<length ys. get xs k \<in> carrier G \<Longrightarrow>
              length xs = length ys \<Longrightarrow>
              local.sum (rev_get (length ys) (\<lambda>k. get xs k \<otimes> get ys k)) =
              local.sum xs \<otimes> local.sum ys)"
  assume ys_in_G : "\<forall>k<length ys. get ys k \<in> carrier G"
  assume a_xs_in_G : "\<forall>k<length ys. get (a # xs) k \<in> carrier G"
  assume "Suc (length xs) = length ys"
  then have "ys \<noteq> []" by auto
  then obtain b zs where b_zs_def : "ys = b # zs" 
    using sum.cases by blast

  have xs_in_G: "(\<forall>k<length xs. get xs k \<in> carrier G)"
    using a_xs_in_G 
    unfolding reverse_equality [OF \<open>Suc (length xs) = length ys\<close>]
    by auto
  have zs_in_G: "(\<forall>k<length zs. get zs k \<in> carrier G)"
    using ys_in_G unfolding b_zs_def by auto[1]
  have length_eq : "length xs = length zs"
    using \<open>Suc (length xs) = length ys\<close>
    unfolding b_zs_def by simp

  have ind_eq: "local.sum (rev_get (length zs) (\<lambda>k. get xs k \<otimes> get zs k)) =
              local.sum xs \<otimes> local.sum zs"
    apply (rule_tac ind)
      apply (rule_tac zs_in_G)
    unfolding reverse_equality [OF length_eq]
    using xs_in_G by simp_all

  have a_in_G : "a \<in> carrier G"
    using a_xs_in_G \<open>Suc (length xs) = length ys\<close>
    unfolding b_zs_def by auto
  have b_in_G : "b \<in> carrier G"
    using ys_in_G
    unfolding b_zs_def by auto
  have xs_sum_in_G: "sum xs \<in> carrier G"
    using sum_carrier [OF xs_in_G].
  have zs_sum_in_G: "sum zs \<in> carrier G"
    using sum_carrier [OF zs_in_G].

  show "local.sum (rev_get (length ys) (\<lambda>k. get (a # xs) k \<otimes> get ys k)) =
       a \<otimes> local.sum xs \<otimes> local.sum ys"
    using a_in_G b_in_G xs_sum_in_G zs_sum_in_G
    unfolding b_zs_def apply simp
    apply (subst ind_eq)
    using m_assoc m_comm
    by simp
qed


definition push_forward :: "nat \<times> nat list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "push_forward ns xs = rev_get (fst ns) (\<lambda>k. sum (merge_with_zeros xs (\<lambda>i. get (snd ns) i = k)))"


lemma push_forward_length [simp]: "length (push_forward ns as) = fst ns"
  unfolding push_forward_def by simp

lemma push_forward_sum : 
  "\<And> ns. fin_set.Arr' ns \<Longrightarrow> (\<forall>k < length as. get as k \<in> carrier G) 
\<Longrightarrow> length (snd ns) = length as \<Longrightarrow> sum (push_forward ns as) = sum as"
  apply (induction as)
   apply (simp add: push_forward_def)
   apply (subst zero_sum)
    apply simp
  unfolding merge_with_zeros_def
    apply simp
   apply simp
proof-
  fix a as 
  fix ns :: "nat \<times> nat list"
  assume ind: " (\<And>ns. fin_set.Arr' ns \<Longrightarrow>
              \<forall>k<length as. get as k \<in> carrier G \<Longrightarrow>
              length (snd ns) = length as \<Longrightarrow> local.sum (push_forward ns as) = local.sum as)"
  assume "fin_set.Arr' ns" 
  assume aas_in_G: "\<forall>k<length (a # as). get (a # as) k \<in> carrier G"
  then have as_in_G: "\<forall>k < length as. get as k \<in> carrier G" by auto
  from aas_in_G have a_in_G: "a \<in> carrier G" by auto
  assume length_eq: "length (snd ns) = length (a # as)"
  then have "0 < length (snd ns)" by simp
  then have "get (snd ns) 0 < fst ns"
    using \<open>fin_set.Arr' ns\<close>
    unfolding fin_set.Arr'_def by simp
  have a_sum_eq: "a = sum (rev_get (fst ns)
       (\<lambda>k. (if get (snd ns) 0 = k then a else \<one>)))"
    apply (subst one_sum)
     apply auto
    using \<open>get (snd ns) 0 < fst ns\<close> apply simp
    apply (subst get_rev_get)
    using \<open>get (snd ns) 0 < fst ns\<close> apply simp
    using a_in_G apply simp
    apply (subst get_rev_get)
    using \<open>get (snd ns) 0 < fst ns\<close> apply simp
    by simp

  from \<open>0 < length (snd ns)\<close>
  have "snd ns \<noteq> []" by simp
  then obtain m ms where ms_def: "snd ns = m # ms" 
    using list.exhaust by auto
  have as_sum_eq: "local.sum (push_forward (fst ns, ms) as) = local.sum as"
    apply (rule_tac ind)
    using \<open>fin_set.Arr' ns\<close>
    unfolding fin_set.Arr'_def ms_def apply auto[1]
    using as_in_G apply simp
    using length_eq apply simp
    unfolding ms_def by simp

  have eq1: " (rev_get (length (rev_get (fst ns) (\<lambda>k. if get (snd ns) 0 = k then a else \<one>)))
       (\<lambda>k. get (rev_get (fst ns) (\<lambda>k. if get (snd ns) 0 = k then a else \<one>)) k \<otimes>
            get (push_forward (fst ns, ms) as) k)) = 
           (rev_get (fst ns)
       (\<lambda>k. (if get (snd ns) 0 = k then a else \<one>) \<otimes>
            local.sum (merge_with_zeros as (\<lambda>i. get (snd ns) (Suc i) = k))))"
    apply (rule_tac getFaithful)
     apply simp
    apply simp
    unfolding push_forward_def apply simp
    unfolding ms_def by simp

  show "local.sum (push_forward ns (a # as)) = local.sum (a # as)"
    unfolding push_forward_def
    apply (subst merge_with_zeros_add)
    apply simp
    apply (rule_tac reverse_equality)
    apply (subst a_sum_eq)
    apply (subst reverse_equality [OF as_sum_eq])
    apply (subst reverse_equality [OF binary_sum_sum])
  proof-
    show "\<forall>k<length (push_forward (fst ns, ms) as). get (push_forward (fst ns, ms) as) k \<in> carrier G"
      unfolding push_forward_def merge_with_zeros_def
      apply simp
      apply auto
      apply (rule_tac sum_carrier)
      apply simp
      using as_in_G by simp
    show "\<forall>k<length (rev_get (fst ns) (\<lambda>k. if get (snd ns) 0 = k then a else \<one>)).
       get (rev_get (fst ns) (\<lambda>k. if get (snd ns) 0 = k then a else \<one>)) k \<in> carrier G"
      apply simp
      using a_in_G by simp
    show "length (rev_get (fst ns) (\<lambda>k. if get (snd ns) 0 = k then a else \<one>)) = length (push_forward (fst ns, ms) as)"
      unfolding push_forward_def by simp
    show "local.sum
     (rev_get (length (rev_get (fst ns) (\<lambda>k. if get (snd ns) 0 = k then a else \<one>)))
       (\<lambda>k. get (rev_get (fst ns) (\<lambda>k. if get (snd ns) 0 = k then a else \<one>)) k \<otimes>
            get (push_forward (fst ns, ms) as) k)) =
    local.sum
     (rev_get (fst ns)
       (\<lambda>k. (if get (snd ns) 0 = k then a else \<one>) \<otimes>
            local.sum (merge_with_zeros as (\<lambda>i. get (snd ns) (Suc i) = k))))"
      apply (subst eq1)
      by simp
  qed
qed


lemma push_forward_carrier : 
  assumes as_in_G: "\<forall>k < length as. get as k \<in> carrier G"
  and "k < fst f"
shows "get (push_forward f as) k \<in> carrier G"
  unfolding push_forward_def
  apply (simp add: get_rev_get [OF \<open>k < fst f\<close>])
  apply (rule_tac sum_carrier)
  apply (simp add: merge_with_zeros_def)
  using as_in_G by simp

lemma push_forward_merge_with_zero : 
      "push_forward ns (merge_with_zeros as (\<lambda>k. (P (get (snd ns) k)))) =
       merge_with_zeros (push_forward ns as) P"
  apply (rule_tac getFaithful)
   apply simp
  apply simp
  apply (subst push_forward_def)
  apply (rule_tac reverse_equality)
  apply (subst merge_with_zeros_def)
  apply simp
  apply auto
proof-
  fix n
  assume "n < fst ns"
  assume "P n"
  have list_eq: "rev_get (length as) (\<lambda>k. if get (snd ns) k = n then get as k else \<one>) =
              (rev_get (length as) (\<lambda>k. if get (snd ns) k = n
        then get (rev_get (length as) (\<lambda>k. if P (get (snd ns) k) then get as k else \<one>)) k else \<one>))"
    apply (rule_tac getFaithful)
     apply simp
    by (simp add: \<open>P n\<close>)
  show "get (push_forward ns as) n =
         local.sum (merge_with_zeros (merge_with_zeros as (\<lambda>k. P (get (snd ns) k))) (\<lambda>i. get (snd ns) i = n))"
    unfolding merge_with_zeros_def push_forward_def 
    apply (simp add: get_rev_get [OF \<open>n < fst ns\<close>])
    apply (subst list_eq)
    by simp
next
  fix n
  assume "n < fst ns"
  assume "\<not> P n"
  show "\<one> = local.sum (merge_with_zeros 
      (merge_with_zeros as (\<lambda>k. P (get (snd ns) k))) (\<lambda>i. get (snd ns) i = n))"
    apply (rule_tac reverse_equality [OF zero_sum])
    apply simp
    unfolding merge_with_zeros_def
    by (simp add: \<open>\<not> P n\<close>)
qed


lemma merge_with_zeros_carrier : assumes as_in_G: "\<forall>k<length as. get as k \<in> carrier G"
  shows "\<forall>k < length (merge_with_zeros as P). get (merge_with_zeros as P) k \<in> carrier G"
  apply simp
  unfolding merge_with_zeros_def
  by (simp add: as_in_G)


lemma push_forward_sum_with_prop : assumes
    "fin_set.Arr' ns"
 and as_in_G: "\<forall>k<length as. get as k \<in> carrier G"
 and "length (snd ns) = length as"
    shows "sum (merge_with_zeros as (\<lambda>k. (P (get (snd ns) k)))) =
         sum (merge_with_zeros (push_forward ns as) P)"
  apply (subst reverse_equality [OF push_forward_merge_with_zero])
  apply (subst push_forward_sum 
        [OF \<open>fin_set.Arr' ns\<close> 
         merge_with_zeros_carrier [OF as_in_G]])
  using \<open>length (snd ns) = length as\<close> apply simp
  by simp



lemma push_forward_id : assumes "length as = n" 
   and as_in_G: "\<forall>k < length as. get as k \<in> carrier G"
  shows "push_forward (fin_set.Id' n) as = as"
  unfolding push_forward_def
  apply (rule_tac getFaithful)
   apply (simp add: fin_set.Id'_def \<open>length as = n\<close>)
  apply simp
  unfolding fin_set.Id'_def 
  apply simp
  unfolding merge_with_zeros_def
proof-
  fix m
  assume "m < n"
  have eq1: "rev_get (length as) (\<lambda>k. if get (rev_get n (\<lambda>k. k)) k = m then get as k else \<one>) =
        rev_get (length as) (\<lambda>k. if k = m then get as k else \<one>)"
    apply (rule_tac getFaithful)
     apply simp
    by (simp add: \<open>m < n\<close> \<open>length as = n\<close>)
  show "local.sum (rev_get (length as) (\<lambda>k. if get (rev_get n (\<lambda>k. k)) k = m then get as k else \<one>)) =
          get as m"
    apply (subst eq1)
    apply (subst one_sum)
     apply safe
    unfolding \<open>length as = n\<close>
    using \<open>m < n\<close> apply simp
      apply simp
    using \<open>m < n\<close> apply simp
    using as_in_G
    unfolding \<open>length as = n\<close> apply simp
    using \<open>m < n\<close> by simp
qed

lemma push_forward_comp : 
  assumes "length (snd g) = length as"
   and "fin_set.Arr' g"
  and as_in_G: "\<forall>k<length as. get as k \<in> carrier G" 
   shows "push_forward (fin_set.Comp' f g) as =
            push_forward f (push_forward g as)"
  apply (subst push_forward_def)
  apply (subst push_forward_def)
  apply (rule_tac getFaithful)
   apply (simp add: fin_set.Comp'_def)
  apply simp
  apply (subst get_rev_get)
   apply (simp add: fin_set.Comp'_def)
proof-
  fix n
  assume "n < fst (fin_set.Comp' f g)"
  then have "n < fst f"
    unfolding fin_set.Comp'_def by simp
  have eq1: "merge_with_zeros as (\<lambda>i. get (rev_get (length (snd g)) (\<lambda>n. get (snd f) (get (snd g) n))) i = n)
             = merge_with_zeros as (\<lambda>i. get (snd f) (get (snd g) i) = n)"
    apply (rule_tac getFaithful)
     apply simp
    apply simp
    unfolding merge_with_zeros_def
              \<open>length (snd g) = length as\<close>
    by simp


  show "local.sum (merge_with_zeros as (\<lambda>i. get (snd (fin_set.Comp' f g)) i = n)) =
         local.sum (merge_with_zeros (push_forward g as) (\<lambda>i. get (snd f) i = n))"
    unfolding fin_set.Comp'_def apply simp
    apply (subst eq1)
    by (rule_tac push_forward_sum_with_prop 
           [OF \<open>fin_set.Arr' g\<close> as_in_G \<open>length (snd g) = length as\<close>])
qed





end




section "Abelian Groups to Gammaset"

locale GroupToGammaset =
  G: comm_group G
  for G:: "('a,'b) monoid_scheme"
begin


interpretation pointed_set.


definition A :: "'a LC pointed_set" where 
  "A = (Just \<one>\<^bsub>G\<^esub>, Just ` (carrier G))"

lemma lacan: "Obj' A"
  unfolding A_def Obj'_def by simp

definition A_tothe :: "nat \<Rightarrow> 'a LC pointed_set" where
  "A_tothe n = pointed_product (rev_get n (\<lambda>k. A))"

lemma A_tothe_obj : "Obj' (A_tothe n)"
  unfolding A_tothe_def
  apply (rule_tac pointed_product_obj)
  apply simp
  using lacan by simp

lemma x_in_A_tothe_char : "x \<in> snd (A_tothe n) \<Longrightarrow> \<exists> xs. x = Join xs \<and>
             length xs = n \<and>
             (\<forall>k < n. get xs k \<in> snd A)"
  unfolding A_tothe_def by simp

lemma xs_in_A_char : assumes xs_def:  "x = Join xs \<and> length xs = n \<and>
             (\<forall>k < n. get xs k \<in> snd A)"
  shows "\<exists> as. xs = fmap Just as \<and> (\<forall>k<length xs. get as k \<in> carrier G) \<and>
                (SOME as. Join (fmap Just as) = x) = as" 
proof-
  have H: "\<forall>k < length xs. get xs k \<in> Just ` (carrier G)"
    using xs_def
    unfolding A_def by simp
  from fmap_image [OF H] obtain as where as_def : "xs = fmap Just as \<and> (\<forall>k<length xs. get as k \<in> carrier G)"
    by auto
  show "\<exists>as. xs = fmap Just as \<and> (\<forall>k<length xs. get as k \<in> carrier G)\<and>
                (SOME as. Join (fmap Just as) = x) = as"
  proof
    show "xs = fmap Just as \<and> (\<forall>k<length xs. get as k \<in> carrier G) \<and> (SOME as. Join (fmap Just as) = x) = as"
      apply (simp add: as_def)
    proof
      show as_eq: "Join (rev_get (length as) (\<lambda>n. Just (get as n))) = x"
        using as_def xs_def by simp
      fix bs
      assume "Join (rev_get (length bs) (\<lambda>n. Just (get bs n))) = x"
      then have fmap_eq: "fmap Just bs = fmap Just as"
        using as_eq by auto
      show "bs = as"
        using fmap_preserves_inj[OF fmap_eq] 
        by simp
    qed
  qed
qed


definition H_on_arrow :: "gamma \<Rightarrow> 'a LC \<Rightarrow> 'a LC" where
  "H_on_arrow f x = Join (fmap Just (G.push_forward (the f) (SOME as. Join (fmap Just as) = x)))"




definition HFunctor :: "gamma \<Rightarrow> 'a LC parr option" where
  "HFunctor = MkFunctor fin_set.comp pointed_set_comp
               (\<lambda>f. Some (MkArr (A_tothe (fin_set.Dom' (the f))) 
                                (A_tothe (fin_set.Cod' (the f))) 
                                (H_on_arrow f)))"


lemma HFunctor_arr: assumes arr_f : "partial_magma.arr fin_set.comp f"
  shows "partial_magma.arr pointed_set_comp (HFunctor f)"
  unfolding pointed_set_comp_def
  apply (subst classical_category.arr_char [OF ccpf])
  apply (subst HFunctor_def)
  apply (simp add: arr_f)
  unfolding Arr'_def setcat.Arr_def apply auto
proof-
  show "fst (the (HFunctor f)) \<in> extensional (snd (fst (snd (the (HFunctor f)))))"
    unfolding HFunctor_def
    using arr_f apply simp
    unfolding MkArr_def by simp
  fix x
  assume "x \<in> snd (fst (snd (the (HFunctor f))))"
  then have x_in_dom: "x \<in> snd (A_tothe (length (snd (the f))))"
    unfolding HFunctor_def
    using arr_f apply simp
    unfolding MkArr_def by simp
  obtain xs where xs_def: "x = Join xs \<and>
             length xs = length (snd (the f)) \<and>
             (\<forall>n<length (snd (the f)).
                 get xs n \<in> snd A)"
    using x_in_A_tothe_char [OF x_in_dom]
    by auto
  obtain as where as_def: "xs = fmap Just as \<and> (\<forall>k<length xs. get as k \<in> carrier G) \<and> 
                   (SOME as. Join (fmap Just as) = x) = as"
    using xs_in_A_char [OF xs_def] 
    by auto
  then have some_as : "(SOME as. Join (fmap Just as) = x) = as" by simp
  from as_def have as_in_G: "(\<forall>k<length as. get as k \<in> carrier G)"
    by simp

  have pf_in_G: "\<forall>n<fst (the f). get (G.push_forward (the f) as) n \<in> carrier G"
    apply auto
    unfolding G.push_forward_def
    apply simp
    apply (rule_tac G.sum_carrier)
    unfolding G.merge_with_zeros_def
    apply simp
    using as_in_G by simp

  show "fst (the (HFunctor f)) x \<in> snd (snd (snd (the (HFunctor f))))"
    unfolding HFunctor_def
    apply (simp add: arr_f)
    unfolding MkArr_def apply (simp add: x_in_dom)
    unfolding H_on_arrow_def
    apply (subst some_as)
    unfolding A_tothe_def apply simp
    unfolding A_def apply simp
    using pf_in_G by simp
next
  show "Obj' (fst (snd (the (HFunctor f))))"
    unfolding HFunctor_def MkArr_def
    using arr_f apply simp
    using A_tothe_obj.
  show "Obj' (snd (snd (the (HFunctor f))))"
    unfolding HFunctor_def MkArr_def
    using arr_f apply simp
    using A_tothe_obj.
  show "fst (the (HFunctor f)) (fst (fst (snd (the (HFunctor f))))) = fst (snd (snd (the (HFunctor f))))"
    unfolding HFunctor_def MkArr_def
    using arr_f A_tothe_obj
    unfolding Obj'_def apply simp
  proof-
    have fst_A_eq: "\<And>n. Join (fmap Just (rev_get n (\<lambda>k. \<one>\<^bsub>G\<^esub>))) = fst (A_tothe n)"
      unfolding A_tothe_def apply simp
      apply (rule_tac getFaithful)
       apply simp
      apply simp
      unfolding A_def by simp
    have some_eq: "(SOME as. Join (fmap Just as) = fst (A_tothe (length (snd (the f))))) =
                      rev_get (length (snd (the f))) (\<lambda>k. \<one>\<^bsub>G\<^esub>)"
    proof
      show "Join (fmap Just (rev_get (length (snd (the f))) (\<lambda>k. \<one>\<^bsub>G\<^esub>))) = fst (A_tothe (length (snd (the f))))"
        using fst_A_eq.
      fix as
      assume "Join (fmap Just as) = fst (A_tothe (length (snd (the f))))"
      then have fmap_eq: "fmap Just as = fmap Just (rev_get (length (snd (the f))) (\<lambda>k. \<one>\<^bsub>G\<^esub>))"
        unfolding reverse_equality [OF fst_A_eq] by simp
      show "as = rev_get (length (snd (the f))) (\<lambda>k. \<one>\<^bsub>G\<^esub>)" 
        using fmap_preserves_inj [OF fmap_eq] by simp
    qed
    have eq1: "(G.push_forward (the f) (rev_get (length (snd (the f))) (\<lambda>k. \<one>\<^bsub>G\<^esub>))) = 
            (rev_get (fst (the f)) (\<lambda>k. \<one>\<^bsub>G\<^esub>))"
      unfolding G.push_forward_def
      apply (rule_tac getFaithful)
       apply simp
      apply simp
      apply (rule_tac G.zero_sum)
      unfolding G.merge_with_zeros_def
      by simp
    show "H_on_arrow f (fst (A_tothe (length (snd (the f))))) = fst (A_tothe (fst (the f)))"
      unfolding H_on_arrow_def
      apply (subst some_eq)
      apply (subst reverse_equality [OF fst_A_eq])
      using eq1 by simp
  qed
qed

lemma HFunctor_Id: "the (HFunctor (Some (fin_set.Id' n))) = Id' (A_tothe n)"
  apply (rule_tac fun_eq_char)
proof-
  have "fin_set.Arr' (fin_set.Id' n)"
    using classical_category.Arr_Id [OF fin_set.is_classical_category]
    by simp
  then have arr_id: "partial_magma.arr fin_set.comp (Some (fin_set.Id' n))"
    unfolding fin_set.comp_def
    using classical_category.arr_char [OF fin_set.is_classical_category]
    by simp
  then have "partial_magma.arr pointed_set_comp (HFunctor (Some (fin_set.Id' n)))"
    apply (rule_tac HFunctor_arr)
    by simp
  then show "Arr' (the (HFunctor (Some (fin_set.Id' n))))"
    using classical_category.arr_char [OF ccpf]
    unfolding reverse_equality [OF pointed_set_comp_def]
    by blast
  show "Arr' (Id' (A_tothe n))"
    using classical_category.Arr_Id [OF ccpf A_tothe_obj].
  show "fst (snd (the (HFunctor (Some (fin_set.Id' n))))) = fst (snd (Id' (A_tothe n)))"
    unfolding HFunctor_def MkArr_def 
    using arr_id apply simp
    unfolding Id'_def fin_set.Id'_def by simp
  show "snd (snd (the (HFunctor (Some (fin_set.Id' n))))) = snd (snd (Id' (A_tothe n)))"
    unfolding HFunctor_def MkArr_def 
    using arr_id apply simp
    unfolding Id'_def fin_set.Id'_def by simp
  fix x
  assume "x \<in> snd (fst (snd (the (HFunctor (Some (fin_set.Id' n))))))"
  then have x_in_dom : "x \<in> snd (A_tothe (length (snd (fin_set.Id' n))))"
    unfolding HFunctor_def MkArr_def
    using arr_id by simp
  then obtain xs where xs_def: "x = Join xs \<and>
         length xs = length (snd (fin_set.Id' n)) \<and> (\<forall>k<length (snd (fin_set.Id' n)). get xs k \<in> snd A)"
    using x_in_A_tothe_char [OF x_in_dom] by auto
  then obtain as where as_def: "xs = fmap Just as \<and> (\<forall>k<length xs. get as k \<in> carrier G) \<and> (SOME as. Join (fmap Just as) = x) = as"
    using xs_in_A_char [OF xs_def] by auto
  then have some_eq : "(SOME as. Join (fmap Just as) = x) = as" by simp
  have "n = length as"
    using xs_def
    unfolding fin_set.Id'_def
    using as_def by simp

  show "fst (the (HFunctor (Some (fin_set.Id' n)))) x = fst (Id' (A_tothe n)) x"
    unfolding HFunctor_def MkArr_def
    apply (simp add: arr_id x_in_dom)
    unfolding H_on_arrow_def some_eq
    apply simp
    apply (subst G.push_forward_id)
    using as_def xs_def apply (simp add: fin_set.Id'_def)
    using as_def apply simp
    using x_in_dom
    unfolding fin_set.Id'_def Id'_def apply simp
    apply (simp add: xs_def)
    by (simp add: as_def \<open>n = length as\<close>)
qed


lemma HFunctor_dom : assumes arr_f : "partial_magma.arr fin_set.comp f" 
  shows "partial_magma.dom pointed_set_comp (HFunctor f) =
                      HFunctor (partial_magma.dom fin_set.comp f)"
proof-
  have arr_id : "\<And>n. partial_magma.arr fin_set.comp (Some (fin_set.Id' n))"
    unfolding fin_set.comp_def
    apply (subst classical_category.arr_char [OF fin_set.is_classical_category])
    using classical_category.Arr_Id [OF fin_set.is_classical_category]
    by simp

  show "partial_magma.dom pointed_set_comp (HFunctor f) = HFunctor (partial_magma.dom fin_set.comp f)"
    unfolding pointed_set_comp_def
    apply (subst classical_category.dom_char [OF ccpf])
    unfolding reverse_equality [OF pointed_set_comp_def]
    apply (simp add: HFunctor_arr [OF arr_f])
    unfolding fin_set.comp_def
    apply (subst classical_category.dom_char [OF fin_set.is_classical_category])
    unfolding reverse_equality [OF fin_set.comp_def]
    apply (simp add: arr_f)
    apply (subst HFunctor_def)
    unfolding MkArr_def apply (simp add: arr_f)
    apply (subst reverse_equality [OF HFunctor_Id])
    unfolding HFunctor_def by (simp add: arr_id)
qed

lemma HFunctor_cod : assumes arr_f : "partial_magma.arr fin_set.comp f" 
  shows "partial_magma.cod pointed_set_comp (HFunctor f) =
                      HFunctor (partial_magma.cod fin_set.comp f)"
proof-
  have arr_id : "\<And>n. partial_magma.arr fin_set.comp (Some (fin_set.Id' n))"
    unfolding fin_set.comp_def
    apply (subst classical_category.arr_char [OF fin_set.is_classical_category])
    using classical_category.Arr_Id [OF fin_set.is_classical_category]
    by simp

  show "partial_magma.cod pointed_set_comp (HFunctor f) = HFunctor (partial_magma.cod fin_set.comp f)"
    unfolding pointed_set_comp_def
    apply (subst classical_category.cod_char [OF ccpf])
    unfolding reverse_equality [OF pointed_set_comp_def]
    apply (simp add: HFunctor_arr [OF arr_f])
    unfolding fin_set.comp_def
    apply (subst classical_category.cod_char [OF fin_set.is_classical_category])
    unfolding reverse_equality [OF fin_set.comp_def]
    apply (simp add: arr_f)
    apply (subst HFunctor_def)
    unfolding MkArr_def apply (simp add: arr_f)
    apply (subst reverse_equality [OF HFunctor_Id])
    unfolding HFunctor_def by (simp add: arr_id)
qed


lemma HFunctor_comp: assumes arr_f: "partial_magma.arr fin_set.comp f" 
                  and arr_g: "partial_magma.arr fin_set.comp g"
  and seq: "partial_magma.dom fin_set.comp g = partial_magma.cod fin_set.comp f"
  shows "the (HFunctor (Some (fin_set.Comp' (the g) (the f)))) =
                      (the (HFunctor g) \<cdot> the (HFunctor f))"
  apply (rule_tac fun_eq_char)
proof-
  have gf_comp_eq: "Some (fin_set.Comp' (the g) (the f)) = fin_set.comp g f"
    using fin_set.comp_char [OF arr_f arr_g seq] by simp

  have arr_gf: "partial_magma.arr fin_set.comp (fin_set.comp g f)"
    using category.seqI [OF fin_set.is_category arr_f arr_g seq].

  have arr_hgf: "partial_magma.arr pointed_set_comp (HFunctor (fin_set.comp g f))"
    apply (rule_tac HFunctor_arr)
    using category.seqI [OF fin_set.is_category arr_f arr_g seq].
  then show "Arr' (the (HFunctor (Some (fin_set.Comp' (the g) (the f)))))"
    apply (subst gf_comp_eq)
    using arr_char by blast
  have arr_hf : "partial_magma.arr pointed_set_comp (HFunctor f)"
    using HFunctor_arr [OF arr_f].
  have arr_hg : "partial_magma.arr pointed_set_comp (HFunctor g)"
    using HFunctor_arr [OF arr_g].
  have h_seq : "partial_magma.dom pointed_set_comp (HFunctor g) = 
                partial_magma.cod pointed_set_comp (HFunctor f)"
    unfolding HFunctor_dom [OF arr_g]
              HFunctor_cod [OF arr_f]
    using seq by simp
  have arr_hgf2 : "partial_magma.arr pointed_set_comp (pointed_set_comp (HFunctor g) (HFunctor f))"
    using category.seqI [OF is_category arr_hf arr_hg h_seq].
  have "Arr' (the (Some (the (HFunctor g) \<cdot> the (HFunctor f))))"
    apply (subst reverse_equality [OF comp_char [OF arr_hf arr_hg h_seq]])
    using arr_char arr_hgf2 by blast
  then show "Arr' (the (HFunctor g) \<cdot> the (HFunctor f))"
    by simp

  have "(if partial_magma.arr fin_set.comp f then Some (fin_set.Id' (fst (the f))) else None) =
        (if partial_magma.arr fin_set.comp g then Some (fin_set.Id' (length (snd (the g)))) else None)"
    unfolding fin_set.comp_def
    apply (subst reverse_equality [OF classical_category.dom_char [OF fin_set.is_classical_category]])
    apply (subst reverse_equality [OF classical_category.cod_char [OF fin_set.is_classical_category]])
    unfolding reverse_equality [OF fin_set.comp_def]
    using seq by simp
  then have "Some (fin_set.Id' (fst (the f))) = Some (fin_set.Id' (length (snd (the g))))"
    using arr_f arr_g by simp
  then have Seq': "(fst (the f)) = length (snd (the g))"
    unfolding fin_set.Id'_def by simp

  have Arr'_hf: "Arr' (the (HFunctor f))"
    using arr_hf arr_char by blast
  have Arr'_hg: "Arr' (the (HFunctor g))"
    using arr_hg arr_char by blast
  have h_Seq' : "snd (snd (the (HFunctor f))) = fst (snd (the (HFunctor g)))"
  proof-
    have "Some (Id' (snd (snd (the (HFunctor f))))) = Some (Id' (fst (snd (the (HFunctor g)))))"
      apply (subst reverse_equality [OF dom_char [OF arr_hg]])
      apply (subst reverse_equality [OF cod_char [OF arr_hf]])
      using h_seq by simp
    then show "snd (snd (the (HFunctor f))) = fst (snd (the (HFunctor g)))"
      unfolding Id'_def by simp
  qed

  show "fst (snd (the (HFunctor (Some (fin_set.Comp' (the g) (the f)))))) =
    fst (snd (the (HFunctor g) \<cdot> the (HFunctor f)))"
    apply (subst gf_comp_eq)
    apply (subst dom_comp [OF Arr'_hf Arr'_hg h_Seq'])
    unfolding HFunctor_def MkArr_def apply (simp add: arr_gf arr_f)
    apply (subst reverse_equality [OF gf_comp_eq])
    unfolding fin_set.Comp'_def by simp
  show "snd (snd (the (HFunctor (Some (fin_set.Comp' (the g) (the f)))))) =
    snd (snd (the (HFunctor g) \<cdot> the (HFunctor f)))"
    apply (subst gf_comp_eq)
    apply (subst cod_comp [OF Arr'_hf Arr'_hg h_Seq'])
    unfolding HFunctor_def MkArr_def apply (simp add: arr_gf arr_g)
    apply (subst reverse_equality [OF gf_comp_eq])
    unfolding fin_set.Comp'_def by simp
  fix x
  assume "x \<in> snd (fst (snd (the (HFunctor (Some (fin_set.Comp' (the g) (the f)))))))"
  then have x_in_dom : "x \<in> snd (fst (snd (the (HFunctor f))))"
    unfolding HFunctor_def MkArr_def gf_comp_eq apply (simp add: arr_gf arr_f)
    unfolding reverse_equality [OF gf_comp_eq] fin_set.Comp'_def 
    by simp
  then have x_in_A_f: "x \<in> snd (A_tothe (length (snd (the f))))"
    unfolding HFunctor_def MkArr_def by (simp add: arr_f)
  then have x_in_A_gf: "x \<in> snd (A_tothe (length (snd (fin_set.Comp' (the g) (the f)))))"
    unfolding fin_set.Comp'_def by simp
  have Hf_x_in_dom: "H_on_arrow f x \<in> snd (A_tothe (length (snd (the g))))"
  proof-
    have "fst (forget (the (HFunctor f)))
  \<in>  (fst (snd (forget (the (HFunctor f)))) \<rightarrow> snd (snd (forget (the (HFunctor f)))))"
      using Arr'_hf
      unfolding Arr'_def setcat.Arr_def by auto
    then have "fst (forget (the (HFunctor f))) x \<in> snd (snd (forget (the (HFunctor f))))"
      using x_in_dom by auto
    then show "H_on_arrow f x \<in> snd (A_tothe (length (snd (the g))))"
      unfolding HFunctor_def MkArr_def apply (simp add: arr_f x_in_A_f)
      using Seq' by simp
  qed

  have eq1: "fst (the (HFunctor (Some (fin_set.Comp' (the g) (the f))))) x =
             H_on_arrow (Some (fin_set.Comp' (the g) (the f))) x"
    unfolding gf_comp_eq HFunctor_def MkArr_def
    using arr_gf x_in_A_gf 
    unfolding reverse_equality [OF gf_comp_eq] by simp

  have eq2: "fst (the (HFunctor g)) (fst (the (HFunctor f)) x) = H_on_arrow g (H_on_arrow f x)"
    using x_in_dom
    unfolding HFunctor_def MkArr_def by (simp add: arr_f arr_g Hf_x_in_dom)

  have some_eq : "(SOME as.
             Join (fmap Just as) = Join (fmap Just (G.push_forward (the f) (SOME as. Join (fmap Just as) = x)))) =
           G.push_forward (the f) (SOME as. Join (fmap Just as) = x)"
  proof
    show "Join (fmap Just (G.push_forward (the f) (SOME as. Join (fmap Just as) = x))) =
    Join (fmap Just (G.push_forward (the f) (SOME as. Join (fmap Just as) = x)))"
      by simp
    fix as
    assume "Join (fmap Just as) = Join (fmap Just (G.push_forward (the f) (SOME as. Join (fmap Just as) = x)))"
    then have fmap_eq: "fmap Just as = fmap Just (G.push_forward (the f) (SOME as. Join (fmap Just as) = x))" by simp
    then show "as = G.push_forward (the f) (SOME as. Join (fmap Just as) = x)"
      using fmap_preserves_inj [OF fmap_eq] by simp
  qed

  show "fst (the (HFunctor (Some (fin_set.Comp' (the g) (the f))))) x = fst (the (HFunctor g) \<cdot> the (HFunctor f)) x"
    unfolding Comp'_def apply (simp add: Arr'_hf Arr'_hg h_Seq' x_in_dom)
    apply (subst eq1)
    apply (subst eq2)
    unfolding H_on_arrow_def
    apply (subst some_eq)
    apply (subst reverse_equality [OF G.push_forward_comp])
  proof-
    obtain xs where xs_def: "x = Join xs \<and>
   length xs = length (snd (the f)) \<and> (\<forall>k<length (snd (the f)). get xs k \<in> snd A)"
      using x_in_A_tothe_char [OF x_in_A_f] by auto
    obtain as where as_def : "xs = fmap Just as \<and>
     (\<forall>k<length xs. get as k \<in> carrier G) \<and> (SOME as. Join (fmap Just as) = x) = as"
      using xs_in_A_char [OF xs_def] by auto
    show "length (snd (the f)) = length (SOME as. Join (fmap Just as) = x)"
      using xs_def as_def by simp
    show "fin_set.Arr' (the f)"
      using classical_category.arr_char [OF fin_set.is_classical_category]
      unfolding reverse_equality [OF fin_set.comp_def]
      using arr_f by simp
    show "\<forall>k<length (SOME as. Join (fmap Just as) = x). get (SOME as. Join (fmap Just as) = x) k \<in> carrier G"
      using as_def by simp
    show "Join
     (fmap Just (G.push_forward (the (Some (fin_set.Comp' (the g) (the f)))) (SOME as. Join (fmap Just as) = x))) =
    Join (fmap Just (G.push_forward (fin_set.Comp' (the g) (the f)) (SOME as. Join (fmap Just as) = x)))"
      by simp
  qed
qed



lemma "functor fin_set.comp pointed_set_comp HFunctor"
  unfolding functor_def
  apply (simp add: fin_set.is_category is_category)
  unfolding functor_axioms_def
  apply auto
proof-
  fix f
  show "\<not> partial_magma.arr fin_set.comp f \<Longrightarrow> HFunctor f = partial_magma.null pointed_set_comp"
    unfolding HFunctor_def by simp
  assume arr_f : "partial_magma.arr fin_set.comp f" 
  show arr_hf: "partial_magma.arr pointed_set_comp (HFunctor f)"
    using HFunctor_arr [OF arr_f].
  have arr_id : "\<And>n. partial_magma.arr fin_set.comp (Some (fin_set.Id' n))"
    unfolding fin_set.comp_def
    apply (subst classical_category.arr_char [OF fin_set.is_classical_category])
    using classical_category.Arr_Id [OF fin_set.is_classical_category]
    by simp

  show "partial_magma.dom pointed_set_comp (HFunctor f) = HFunctor (partial_magma.dom fin_set.comp f)"
    unfolding pointed_set_comp_def
    apply (subst classical_category.dom_char [OF ccpf])
    unfolding reverse_equality [OF pointed_set_comp_def]
    apply (simp add: arr_hf)
    unfolding fin_set.comp_def
    apply (subst classical_category.dom_char [OF fin_set.is_classical_category])
    unfolding reverse_equality [OF fin_set.comp_def]
    apply (simp add: arr_f)
    apply (subst HFunctor_def)
    unfolding MkArr_def apply (simp add: arr_f)
    apply (subst reverse_equality [OF HFunctor_Id])
    unfolding HFunctor_def by (simp add: arr_id)
  show "partial_magma.cod pointed_set_comp (HFunctor f) = HFunctor (partial_magma.cod fin_set.comp f)"
    unfolding pointed_set_comp_def
    apply (subst classical_category.cod_char [OF ccpf])
    unfolding reverse_equality [OF pointed_set_comp_def]
    apply (simp add: arr_hf)
    unfolding fin_set.comp_def
    apply (subst classical_category.cod_char [OF fin_set.is_classical_category])
    unfolding reverse_equality [OF fin_set.comp_def]
    apply (simp add: arr_f)
    apply (subst HFunctor_def)
    unfolding MkArr_def apply (simp add: arr_f)
    apply (subst reverse_equality [OF HFunctor_Id])
    unfolding HFunctor_def by (simp add: arr_id)
next
  fix g f
  assume arr_gf: "partial_magma.arr fin_set.comp (fin_set.comp g f)"
  from arr_gf have gf_prop: "partial_magma.arr fin_set.comp f \<and>
                    partial_magma.arr fin_set.comp g \<and>
      partial_magma.dom fin_set.comp g = partial_magma.cod fin_set.comp f"
    using category.seqE [OF fin_set.is_category arr_gf] by blast

  have arr_hf: "partial_magma.arr pointed_set_comp (HFunctor f)"
    apply (rule_tac HFunctor_arr)
    using gf_prop by simp
  have arr_hg: "partial_magma.arr pointed_set_comp (HFunctor g)"
    apply (rule_tac HFunctor_arr)
    using gf_prop by simp
  have h_seq: "partial_magma.dom pointed_set_comp (HFunctor g) =
               partial_magma.cod pointed_set_comp (HFunctor f)"
    apply (subst HFunctor_dom)
    using gf_prop apply simp
    apply (subst HFunctor_cod)
    using gf_prop by simp_all

  have arr_hgf: "partial_magma.arr pointed_set_comp (pointed_set_comp (HFunctor g) (HFunctor f))"
    apply (rule_tac category.seqI [OF is_category])
    using arr_hf arr_hg h_seq by simp_all
    
  have gf_comp_eq: "fin_set.comp g f = Some (fin_set.Comp' (the g) (the f))"
    apply (rule_tac category.seqE [OF fin_set.is_category arr_gf])
    using fin_set.comp_char.
  have hgf_comp_eq : "pointed_set_comp (HFunctor g) (HFunctor f) =
                      Some (Comp' (the (HFunctor g)) (the (HFunctor f)))"
    apply (rule_tac category.seqE [OF is_category arr_hgf])
    using comp_char.
  show "HFunctor (fin_set.comp g f) = pointed_set_comp (HFunctor g) (HFunctor f)"
    apply (subst gf_comp_eq)
    apply (subst hgf_comp_eq)
    apply (subst reverse_equality [OF HFunctor_comp])
    using gf_prop apply simp_all
    unfolding HFunctor_def MkArr_def
    using arr_gf 
    unfolding reverse_equality [OF gf_comp_eq] 
    by simp
qed
    

end


end
