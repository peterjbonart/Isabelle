theory FiniteSum
  imports Main
         "HOL-Algebra.Group"
         PointedSet
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



section "Finite set sums"


lemma finite_induct' : 
  assumes "finite x"
  shows "P {} \<Longrightarrow> 
        (\<And>A a. finite A \<Longrightarrow> P A \<Longrightarrow> a \<notin> A \<Longrightarrow> P (insert a A)) 
         \<Longrightarrow> P x"
  apply (rule_tac finite.induct [OF assms])
   apply simp
proof-
  fix A a
  assume "P A"
  assume "finite A"
  assume step: "(\<And>A a. finite A \<Longrightarrow> P A \<Longrightarrow> a \<notin> A \<Longrightarrow> P (insert a A))"
  have "a \<in> A \<or> a \<notin> A" by auto
  then show "P (insert a A)"
  proof
    assume "a \<in> A"
    then have "insert a A = A" by auto
    then show "P (insert a A)"
      by (simp add: \<open>P A\<close>)
  next
    show "a \<notin> A \<Longrightarrow> P (insert a A)"
      apply (rule_tac step)
      using \<open>finite A\<close> \<open>P A\<close> by simp_all
  qed
qed


context pointed_set
begin



lemma finite_set_length_insert : 
  assumes "a \<notin> A" "A \<noteq> {}" "finite A"
  shows  "(finite_set_length (a, insert a A)) =
     Suc (finite_set_length (SOME x. x \<in> A, A))"
  apply (subst finite_set_length_def)
proof-
  define n where "n = finite_set_length (SOME x. x \<in> A, A)"
  define f where "f = finite_set_interval_bijection (SOME x. x \<in> A, A)"
  have A_snd: "A = snd (SOME x. x \<in> A, A)" by simp
  have f_bij: "bij_betw f {i. i < n} A"
    apply (subst A_snd)
    unfolding f_def n_def
    apply (rule_tac conjunct1 [OF finite_set_interval_bijection_char])
    unfolding Obj'_def
    using \<open>A \<noteq> {}\<close> some_in_eq apply auto[1]
    using \<open>finite A\<close> by simp
  have a_notin_f : "a \<notin> f ` {i. i < n}"
    using f_bij
    unfolding bij_betw_def
    using \<open>a \<notin> A\<close> by simp
  define g where "g = (\<lambda>k. if k = 0 then a else f (k -1))"
  have g_prop: "bij_betw g {i. i < Suc n} (snd (a, insert a A)) \<and>
            g 0 = fst (a, insert a A)"
    unfolding bij_betw_def
    apply auto
  proof-
    show "inj_on g {i. i < Suc n}"
      unfolding inj_on_def
      apply auto
    proof-
      fix x y
      assume "x < Suc n"
      assume "y < Suc n"
      assume "g x = g y"
      have "x = 0 \<or> x \<noteq> 0" by auto
      then show "x = y"
      proof
        assume "x = 0"
        then have "a = g y"
          using \<open>g x = g y\<close>
          unfolding g_def
          by simp
        then have "y \<noteq> 0 \<Longrightarrow> False"
        proof-
          assume "y \<noteq> 0"
          then have "a \<in> f ` {i . i < n}"
            unfolding \<open>a = g y\<close>
            unfolding g_def
            apply simp
            using \<open>y < Suc n\<close> by auto
          then show "False"
            using a_notin_f
            by simp
        qed
        then show "x = y"
          unfolding \<open>x = 0\<close> by auto
      next
        assume "x \<noteq> 0"
        then have "x - 1 < n"
          using \<open>x < Suc n\<close> by simp
        from \<open>x \<noteq> 0\<close> have "g y = f (x - 1)"
          using \<open>g x = g y\<close>
          unfolding g_def
          by simp
        have "g y \<in> f ` {i . i < n}"
          unfolding \<open>g y = f (x - 1)\<close>
          using \<open>x - 1 < n\<close> by simp
        then have "a \<noteq> g y"
          using a_notin_f 
          by auto
        then have "y \<noteq> 0"
          unfolding g_def
          by presburger
        have "x - 1 = y - 1"
          using \<open>g x = g y\<close>
          unfolding g_def
          using \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> apply simp
          using f_bij
          unfolding bij_betw_def inj_on_def
          using \<open>x - 1 < n\<close> \<open>y < Suc n\<close> by auto
        then show "x = y"
          using \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> by simp
      qed
    qed
    show "\<And>xa. g xa \<notin> A \<Longrightarrow> xa < Suc n \<Longrightarrow> g xa = a"
      unfolding g_def
      apply auto
      using f_bij
      unfolding bij_betw_def
      by auto
    show "g 0 = a"
      unfolding g_def by simp
    show "a \<in> g ` {i. i < Suc n}"
      unfolding reverse_equality [OF \<open>g 0 = a\<close>] by simp
    show "\<And>x. x \<in> A \<Longrightarrow> x \<in> g ` {i. i < Suc n}"
    proof-
      fix x
      assume "x \<in> A"
      then have "x \<in> f ` {i. i < n}"
        using f_bij
        unfolding bij_betw_def by simp
      then obtain y where y_def : "x = f y \<and> y < n" by blast
      have "x = g (Suc y) \<and> Suc y < Suc n"
        unfolding conjunct1 [OF y_def]
        unfolding g_def by (simp add: y_def)
      then show "x \<in> g ` {i. i < Suc n}"
        by simp
    qed
  qed
  show "(SOME n.
        \<exists>f. bij_betw f {i. i < n} (snd (a, insert a A)) \<and>
            f 0 = fst (a, insert a A)) =
    Suc (finite_set_length (SOME x. x \<in> A, A))"
      unfolding reverse_equality [OF n_def]
  proof
    show "\<exists>f. bij_betw f {i. i < Suc n}
         (snd (a, insert a A)) \<and>
        f 0 = fst (a, insert a A)"
      apply (rule_tac exI)
      using g_prop.
    fix m :: nat
    assume "\<exists>f. bij_betw f {i. i < m} (snd (a, insert a A)) \<and>
              f 0 = fst (a, insert a A)"
    then obtain h where h_def: "bij_betw h {i. i < m} (snd (a, insert a A)) \<and>
              h 0 = fst (a, insert a A)" by blast
    then obtain i where i_def : "bij_betw i (snd (a, insert a A)) {i. i < m}"
      using bij_betw_inv by blast
    have "bij_betw (i \<circ> g) {i. i < Suc n} {i . i < m}"
      apply (rule_tac bij_betw_trans)
      using g_prop apply blast
      using i_def.
    then have "card {i. i < Suc n} = card {i . i < m}"
      using bij_betw_same_card by blast
    then show "m = Suc n"
      by simp
  qed
qed

lemma finite_set_length_card :
  assumes "a \<in> A" and "finite A"
  shows "finite_set_length (a, A) = card A"
proof-
  define f where "f = finite_set_interval_bijection (a, A)"
  have f_bij: "bij_betw f {i. i < finite_set_length (a, A)} (snd (a, A))"
    unfolding f_def
    apply (rule_tac conjunct1 [OF finite_set_interval_bijection_char])
    unfolding Obj'_def
    using assms by simp_all
  have "\<exists>g. bij_betw g {i. i < card A} A"
    using assms(2) card_Collect_less_nat finite_same_card_bij by blast
  then have "\<exists>g. bij_betw g A {i. i < card A}"
    using bij_betw_inv by blast
  then obtain g where g_def: "bij_betw g A {i. i < card A}"
    by blast
  have "bij_betw (g \<circ> f) {i. i < finite_set_length (a, A)} {i. i < card A}"
    apply (rule_tac bij_betw_trans)
    using f_bij apply simp
    using g_def.
  then have "card {i. i < finite_set_length (a, A)} = card {i. i < card A}"
    using bij_betw_same_card by blast
  then show "finite_set_length (a, A) = card A"
    unfolding card_Collect_less_nat.
qed




end



context comm_group
begin


definition finset_sum where
  "finset_sum S f = sum (fmap f (pointed_set.finite_set_to_list ((SOME x. x \<in> S), S)))"


lemma permutation_pushforward:
  "bij_betw f {i::nat . i < length xs} {i :: nat . i < length xs} \<Longrightarrow>
   \<forall>k < length xs. get xs k \<in> carrier G \<Longrightarrow>
   push_forward (length xs, (rev_get (length xs) (\<lambda>k. (SOME m. k = f m \<and> m < length xs)))) xs = rev_get (length xs) 
         (\<lambda>k. get xs (f k))"
  unfolding push_forward_def
  apply (rule_tac getFaithful)
   apply simp
  apply simp
proof-
  fix n
  assume f_bij : "bij_betw f {i. i < length xs} {i. i < length xs}"
  assume xs_in_G : "\<forall>k < length xs. get xs k \<in> carrier G"
  assume "n < length xs"
  then have "f n < length xs"
    using f_bij
    unfolding bij_betw_def by auto

  have f_some_inv:  "\<And>k. k < length xs \<Longrightarrow>
         k = f (SOME m. k = f m \<and> m < length xs)"
  proof-
    fix k
    assume "k < length xs"
    then have "k \<in> f ` {i . i < length xs}"
      using f_bij
      unfolding bij_betw_def
      by auto
    then obtain m where m_def : "k = f m \<and> m < length xs" 
      by blast
    have "(SOME m. k = f m \<and> m < length xs) = m"
    proof
      show "k = f m \<and> m < length xs" 
        using m_def.
      show "\<And>ma. k = f ma \<and> ma < length xs \<Longrightarrow> ma = m"
        using f_bij
        unfolding bij_betw_def inj_on_def
        using m_def by auto
    qed
    then show "k = f (SOME m. k = f m \<and> m < length xs)"
      unfolding conjunct1 [OF m_def] by simp
  qed
  show "local.sum (merge_with_zeros xs
            (\<lambda>i. get (rev_get (length xs) (\<lambda>k. SOME m. k = f m \<and> m < length xs))
             i = n)) = get xs (f n)"
    apply (subst one_sum)
     apply auto
    using \<open>f n < length xs\<close> apply simp
    unfolding merge_with_zeros_def
      apply auto
    using f_some_inv apply simp
    using \<open>f n < length xs\<close> apply simp
    using xs_in_G apply simp
    using \<open>f n < length xs\<close> apply auto
  proof-
    assume not_eq: "(SOME m. f n = f m \<and> m < length xs) \<noteq> n"
    have eq: "(SOME m. f n = f m \<and> m < length xs) = n"
    proof
      show "f n = f n \<and> n < length xs"
        using \<open>n < length xs\<close> by simp
      show "\<And>m. f n = f m \<and> m < length xs \<Longrightarrow> m = n"
        using \<open>n < length xs\<close>
        using f_bij
        unfolding bij_betw_def inj_on_def
        by auto
    qed
    show "\<one> = get xs (f n)"
      using eq not_eq by simp
  qed
qed

lemma sum_permutation_invariant :
   "bij_betw f {i::nat . i < (length xs)} {i :: nat . i < (length xs)} \<Longrightarrow>
    \<forall>k<length xs. get xs k \<in> carrier G \<Longrightarrow>
        sum xs = sum (rev_get (length xs) (\<lambda>k. get xs (f k)))"
  unfolding reverse_equality [OF permutation_pushforward]
  apply (subst push_forward_sum)
     apply auto
  unfolding fin_set.Arr'_def
  apply auto
proof-
  fix n
  assume f_bij: "bij_betw f {i. i < length xs} {i. i < length xs}"
  assume "n < length xs"
  then have "n \<in> f ` {i . i < length xs}"
    using f_bij
    unfolding bij_betw_def by auto
  then obtain m where m_def: "n = f m \<and> m < length xs" by blast
  have "(SOME m. n = f m \<and> m < length xs) = m"
  proof
    show "n = f m \<and> m < length xs"
      using m_def.
    show "\<And>ma. n = f ma \<and> ma < length xs \<Longrightarrow> ma = m"
      using f_bij
      unfolding bij_betw_def inj_on_def
      using m_def by auto
  qed
  then show "(SOME m. n = f m \<and> m < length xs) < length xs"
    by (simp add: m_def)
qed

lemma finset_sum_empty :
  "finset_sum {} f = \<one>"
proof-
  have n_some: "(SOME (n :: nat). \<exists>f. bij_betw f {i. i < n} {} \<and> f 0 = (SOME x. False)) = 0"
  proof
    show "\<exists> f. bij_betw f {i. i < (0 :: nat)} {} \<and> f 0 = (SOME x. False)"
      apply (rule_tac exI)
    proof-
      show "bij_betw (\<lambda>k. (SOME x. False)) {i. i < (0 :: nat)} {} \<and> 
            (\<lambda>k. (SOME x. False)) 0 = (SOME x. False)"
        unfolding bij_betw_def by auto
    qed
    fix n :: nat
    show "\<exists>f. bij_betw f {i. i < n} {} \<and> f 0 = (SOME x. False) \<Longrightarrow> n = 0"
      unfolding bij_betw_def
      by auto
  qed
  show "finset_sum {} f = \<one>"
    unfolding finset_sum_def
    unfolding pointed_set.finite_set_to_list.simps
    unfolding pointed_set.finite_set_length_def
    apply simp
    unfolding n_some
    by simp
qed

lemma finset_sum_singleton:
  assumes "f a \<in> carrier G"
  shows "finset_sum {a} f = f a"
proof-
  have length_eq: "(pointed_set.finite_set_length (a, {a})) = 1"
    apply (subst pointed_set.finite_set_length_card)
    by simp_all
  have a_eq : "pointed_set.finite_set_interval_bijection (a, {a}) 0 = fst (a, {a})"
    apply (rule_tac conjunct2 [OF pointed_set.finite_set_interval_bijection_char])
    unfolding pointed_set.Obj'_def
    by simp_all

  show "finset_sum {a} f = f a"
    unfolding finset_sum_def
    apply simp
    unfolding pointed_set.finite_set_to_list.simps
    unfolding length_eq
    apply simp
    unfolding a_eq
    by (simp add: \<open>f a \<in> carrier G\<close>)
qed

lemma finset_sum_insert_non_empty :
  assumes "a \<notin> A" "A \<noteq> {}" "finite A"
  and "f a \<in> carrier G"
  and f_in_G: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> carrier G"
  and "finset_sum A f \<in> carrier G"
shows "finset_sum (insert a A) f = (f a) \<otimes> (finset_sum A f)"
proof-
  define n where n_def : "n = (pointed_set.finite_set_length (SOME x. x \<in> A, A))"
  have length_eq: "(pointed_set.finite_set_length (a, insert a A)) =
        Suc n"
    unfolding n_def
    apply (rule_tac pointed_set.finite_set_length_insert)
    using assms by simp_all

  have obj_aA: "pointed_set.Obj' (a, insert a A)"
    unfolding pointed_set.Obj'_def by simp
  define g where "g = pointed_set.finite_set_interval_bijection (a, insert a A)"
  have g_bij : "bij_betw g {i. i < Suc n} (insert a A) \<and> g 0 = a"
    unfolding g_def reverse_equality [OF length_eq]
    using pointed_set.finite_set_interval_bijection_char [OF obj_aA]
    using \<open>finite A\<close> by simp
  define h where "h = (\<lambda>k. g (Suc k))"
  have h_bij : "bij_betw h {i. i < n} A"
    using g_bij
    unfolding h_def bij_betw_def inj_on_def
    apply auto
  proof-
    fix x
    assume "x \<in> A"
    then have "x \<in> insert (g 0) A" by simp
    assume "g ` {i. i < Suc n} = insert (g 0) A"
    from this and \<open>x \<in> insert (g 0) A\<close> 
    have "x \<in> g ` {i. i < Suc n}" by simp
    then obtain i where i_def : "i < Suc n \<and> g i = x"
      by blast
    have "i \<noteq> 0"
    proof
      assume "i = 0"
      have "x = a"
        using i_def
        unfolding \<open>i = 0\<close>
        using g_bij by simp
      then show "False"
        using \<open>x \<in> A\<close> \<open>a \<notin> A\<close> by simp
    qed
    then have "g (Suc (i -1)) = x \<and> i - 1 < n"
      using i_def by auto
    then show "x \<in> (\<lambda>k. g (Suc k)) ` {i. i < n}"
      by auto
  qed
  have obj_A: "pointed_set.Obj' (SOME x. x \<in> A, A)"
    unfolding pointed_set.Obj'_def
    using \<open>A \<noteq> {}\<close>
    by (simp add: some_in_eq)
  define \<alpha> where "\<alpha> = pointed_set.finite_set_interval_bijection (SOME x. x \<in> A, A)"
  have bij_\<alpha> : "bij_betw \<alpha> {i . i < n} A"
    unfolding \<alpha>_def n_def
    using pointed_set.finite_set_interval_bijection_char [OF obj_A]
    using \<open>finite A\<close> by simp

  define \<beta> where "\<beta> = (restrict (inv_into {i. i < n} h) A)"
  have bij_\<beta> : "bij_betw \<beta> A {i. i < n}"
    using h_bij
    unfolding \<beta>_def
    by (simp add: bij_betw_inv_into)

  have h\<beta>id: "\<And>x. x \<in> A \<Longrightarrow> h (\<beta> x) = x"
    unfolding \<beta>_def
    using h_bij
    unfolding bij_betw_def
    using compose_id_inv_into
    by (simp add: f_inv_into_f)


  define \<gamma> where "\<gamma> = \<beta> \<circ> \<alpha>"
  have bij_\<gamma> : "bij_betw \<gamma> {i. i < n} {i. i < n}"
    unfolding \<gamma>_def
    apply (rule_tac bij_betw_trans)
    using bij_\<alpha> apply simp
    using bij_\<beta>.
  have \<gamma>_bound: "\<And>k. k < n \<Longrightarrow> \<gamma> k < n"
    using bij_\<gamma>
    unfolding bij_betw_def
    by auto

  have list_eq1: "(rev_get n (\<lambda>k. get (rev_get n (\<lambda>k. f (get (rev_get n h) k))) (\<gamma> k))) =
        (rev_get n (\<lambda>na. f (get (rev_get n \<alpha>) na)))"
    apply (rule_tac getFaithful)
     apply simp
    apply (simp add: \<gamma>_bound)
    unfolding \<gamma>_def
    apply simp
    apply (subst h\<beta>id)
    using bij_\<alpha>
    unfolding bij_betw_def
    by auto

  have EQ1: "local.sum
     (fmap f (pointed_set.finite_set_to_list (a, insert a A))) =
    f a \<otimes> finset_sum A f"
    unfolding finset_sum_def
    unfolding pointed_set.finite_set_to_list.simps
    unfolding length_eq
    apply simp
    apply (subst conjunct2 [OF pointed_set.finite_set_interval_bijection_char])
    unfolding pointed_set.Obj'_def apply simp
    using \<open>finite A\<close> apply simp
    apply simp
    unfolding reverse_equality [OF n_def]
    apply (subst sum_permutation_invariant)
      apply simp_all
    using bij_\<gamma> apply simp
     apply auto
     apply (rule_tac f_in_G)
    unfolding reverse_equality [OF g_def]
    using h_bij
    unfolding bij_betw_def
    unfolding h_def
     apply blast
    unfolding reverse_equality [OF h_def]
    unfolding reverse_equality [OF \<alpha>_def]
    unfolding list_eq1
    by simp

  have length_eq2 : "pointed_set.finite_set_length (SOME x. x \<in> insert a A, insert a A)
                     = Suc n"
    apply (subst pointed_set.finite_set_length_card)
      apply (metis insert_not_empty some_in_eq)
    using \<open>finite A\<close> apply simp
    unfolding n_def
    apply (subst pointed_set.finite_set_length_card)
    using \<open>A \<noteq> {}\<close> 
      apply (simp add: some_in_eq)
    using assms by simp_all

  have obj_aA: "pointed_set.Obj' (SOME x. x \<in> insert a A, insert a A)"
    unfolding pointed_set.Obj'_def
    apply simp
    by (metis (mono_tags, lifting) someI_ex)
  define \<delta> where "\<delta> = (pointed_set.finite_set_interval_bijection
           (SOME x. x \<in> insert a A, insert a A))"
  have bij_\<delta> : "bij_betw \<delta> {i. i < Suc n} (insert a A)"
    unfolding \<delta>_def
    using pointed_set.finite_set_interval_bijection_char [OF obj_aA]
    unfolding length_eq2
    using \<open>finite A\<close> by simp

  define \<epsilon> where "\<epsilon> = (restrict (inv_into {i. i < Suc n} \<delta>) (insert a A)) \<circ> g"
  have bij_\<epsilon> : "bij_betw \<epsilon> {i. i < Suc n} {i. i < Suc n}"
    unfolding \<epsilon>_def
    apply (rule_tac bij_betw_trans)
    using g_bij apply blast
    using bij_\<delta>
    using bij_betw_inv_into bij_betw_restrict_eq by blast

  have fa_in_G : "\<And>x. x \<in> (insert a A) \<Longrightarrow> f x \<in> carrier G"
    apply auto
    using assms by simp_all

  define m where "m = Suc n"

  have \<epsilon>_bound : "\<And>x . x < m \<Longrightarrow> \<epsilon> x < m"
    using bij_\<epsilon>
    unfolding reverse_equality [OF m_def]
    unfolding bij_betw_def
    by auto

  have eq2 : "\<And>n . n < m \<Longrightarrow>  \<delta> (\<epsilon> n) = 
     compose (insert a A) \<delta> (restrict (inv_into {i. i < m} \<delta>) (insert a A)) (g n)"
    unfolding \<epsilon>_def
    unfolding reverse_equality [OF m_def]
    apply auto
    using g_bij
    unfolding reverse_equality [OF m_def]
    unfolding bij_betw_def
    by auto

  have \<delta>\<epsilon>g : "\<And>x. x < m \<Longrightarrow> \<delta> (\<epsilon> x) = g x"
    apply (subst eq2)
     apply simp
    apply (subst compose_id_inv_into)
    using bij_\<delta>
    unfolding bij_betw_def
    using m_def apply simp
    using g_bij
    unfolding bij_betw_def
    using m_def by auto

  have list_eq2 : "(rev_get m (\<lambda>k. get (rev_get m (\<lambda>n. f (get (rev_get m \<delta>) n))) (\<epsilon> k))) =
     (rev_get m (\<lambda>n. f (get (rev_get m g) n)))"
    apply (rule_tac getFaithful)
     apply simp
    apply (simp add: \<epsilon>_bound)
    unfolding \<delta>\<epsilon>g
    by simp

  have EQ2: "finset_sum (insert a A) f = local.sum
     (fmap f (pointed_set.finite_set_to_list (a, insert a A)))"
    unfolding finset_sum_def
    unfolding pointed_set.finite_set_to_list.simps
    unfolding length_eq
    unfolding reverse_equality [OF g_def]
    unfolding reverse_equality [OF \<delta>_def]
    unfolding length_eq2
    apply (subst sum_permutation_invariant)
    using bij_\<epsilon> apply simp
    unfolding reverse_equality [OF m_def]
     apply auto
     apply (rule_tac fa_in_G)
    using bij_\<delta>
    unfolding bij_betw_def
    unfolding reverse_equality [OF m_def]
     apply auto[1]
    unfolding list_eq2
    by simp
  show "finset_sum (insert a A) f = f a \<otimes> finset_sum A f"
    using EQ1 EQ2
    by simp
qed


lemma finset_sum_insert :
  assumes "finite A"
  and "f a \<in> carrier G"
  and f_in_G: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> carrier G"
  and "finset_sum A f \<in> carrier G"
shows "finset_sum (insert a A) f =
       (if a \<in> A then (finset_sum A f) else (f a) \<otimes> (finset_sum A f))"
proof-
  have "A = {} \<or> A \<noteq> {}" by auto
  then show "finset_sum (insert a A) f =
       (if a \<in> A then (finset_sum A f) else (f a) \<otimes> (finset_sum A f))"
  proof
    show "A = {} \<Longrightarrow>
    finset_sum (insert a A) f =
    (if a \<in> A then finset_sum A f else f a \<otimes> finset_sum A f)"
      apply simp
      unfolding finset_sum_empty
      apply (subst finset_sum_singleton)
      by (simp_all add: \<open>f a \<in> carrier G\<close>)
    have "a \<in> A \<Longrightarrow> insert a A = A"
      by auto
    assume "A \<noteq> {}"
    show "
    finset_sum (insert a A) f =
    (if a \<in> A then finset_sum A f else f a \<otimes> finset_sum A f)"
      apply auto
      unfolding \<open>a \<in> A \<Longrightarrow> insert a A = A\<close>
       apply simp
      apply (rule_tac finset_sum_insert_non_empty)
      using assms \<open>A \<noteq> {}\<close> by simp_all
  qed
qed



lemma finset_sum_carrier :
  assumes "finite S"
  shows "(\<forall>x \<in> S. f x \<in> carrier G) \<Longrightarrow> finset_sum S f \<in> carrier G"
proof-
  have "(\<forall>x \<in> S. f x \<in> carrier G) \<longrightarrow> finset_sum S f \<in> carrier G"
    apply (rule_tac finite.induct [OF \<open>finite S\<close>])
     apply auto
  proof-
    show "finset_sum {} f \<in> carrier G"
      unfolding finset_sum_empty
      by simp
    fix A a
    assume A_sum_in_G: "finset_sum A f \<in> carrier G"
    assume "finite A"
    assume fa_in_G: "f a \<in> carrier G"
    assume fA_in_G: "\<forall>x\<in>A. f x \<in> carrier G"
    show "finset_sum (insert a A) f \<in> carrier G"
      apply (subst finset_sum_insert)
      by (simp_all add: \<open>finite A\<close> fa_in_G fA_in_G A_sum_in_G)
  qed
  then show "\<forall>x\<in>S. f x \<in> carrier G \<Longrightarrow> finset_sum S f \<in> carrier G"
    by simp
qed

lemma finset_sum_insert': 
  assumes "finite A"
  and "f a \<in> carrier G"
  and f_in_G: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> carrier G"
shows "finset_sum (insert a A) f =
       (if a \<in> A then (finset_sum A f) else (f a) \<otimes> (finset_sum A f))"
  apply (subst finset_sum_insert)
  using assms apply simp_all
  apply (rule_tac finset_sum_carrier)
  by simp_all



lemma finset_sum_union:
  "finite A \<Longrightarrow> f ` A \<subseteq> carrier G \<Longrightarrow> finite B \<Longrightarrow> f ` B \<subseteq> carrier G \<Longrightarrow>
   finset_sum (A \<union> B) f = finset_sum A f \<otimes> finset_sum B f
                      \<otimes> inv (finset_sum (A \<inter> B) f)"
proof-
  assume "finite A"
  have "\<And>B. finite A \<longrightarrow> f ` A \<subseteq> carrier G \<longrightarrow> finite B \<longrightarrow> f ` B \<subseteq> carrier G \<longrightarrow>
   finset_sum (A \<union> B) f = finset_sum A f \<otimes> finset_sum B f
                      \<otimes> inv (finset_sum (A \<inter> B) f)"
    apply (rule_tac finite_induct' [OF \<open>finite A\<close>])
     apply simp
    unfolding finset_sum_empty
     apply auto
  proof-
    fix B
    assume fB_in_G: "f ` B \<subseteq> carrier G"
    assume "finite B"
    have B_sum_in_G: "finset_sum B f \<in> carrier G"
      apply (rule_tac finset_sum_carrier)
       apply (simp add: \<open>finite B\<close>)
      using \<open>f ` B \<subseteq> carrier G\<close> by auto
    then show "finset_sum B f = \<one> \<otimes> finset_sum B f \<otimes> \<one>"
      by simp
    fix A a
    assume ind : "finset_sum (A \<union> B) f =
       finset_sum A f \<otimes> finset_sum B f \<otimes> inv finset_sum (A \<inter> B) f"
    assume "finite A"
    assume fa_in_G: "f a \<in> carrier G"
    assume fA_in_G: "f ` A \<subseteq> carrier G"
    have set_eq : "(insert a A \<inter> B) = (if a \<in> B then insert a (A \<inter> B) else A \<inter> B)"
      by auto

    have AiB_sum_in_G: "finset_sum (A \<inter> B) f \<in> carrier G"
      apply (rule_tac finset_sum_carrier)
       apply (simp add: \<open>finite A\<close>)
      using fA_in_G by auto[1]
    have AuB_sum_in_G: "finset_sum (A \<union> B) f \<in> carrier G"
      apply (rule_tac finset_sum_carrier)
      apply (simp add: \<open>finite A\<close> \<open>finite B\<close>)
      using fA_in_G fB_in_G by auto[1]
    have A_sum_in_G: "finset_sum A f \<in> carrier G"
      apply (rule_tac finset_sum_carrier)
       apply (simp add: \<open>finite A\<close>)
      using fA_in_G by auto[1]

    assume "a \<notin> A"
    show "
       finset_sum (insert a (A \<union> B)) f =
       finset_sum (insert a A) f \<otimes> finset_sum B f \<otimes>
       inv finset_sum (insert a A \<inter> B) f"
      apply (subst finset_sum_insert')
          apply (simp add: \<open>finite A\<close> \<open>finite B\<close>)
         apply (simp add: fa_in_G)
      using fA_in_G fB_in_G apply auto[1]
      apply (subst finset_sum_insert')
          apply (simp add: \<open>finite A\<close>)
         apply (simp add: fa_in_G)
      using fA_in_G apply auto[1]
      using finset_sum_insert
      unfolding set_eq
      using \<open>a \<notin> A\<close> apply auto
    proof-
      show "a \<notin> A \<Longrightarrow>
    finset_sum (A \<union> B) f =
    f a \<otimes> finset_sum A f \<otimes> finset_sum B f \<otimes> inv finset_sum (insert a (A \<inter> B)) f"
        apply (subst finset_sum_insert')
            apply (simp add: \<open>finite A\<close>)
           apply (simp add: fa_in_G)
        using fA_in_G apply auto[1]
        apply simp
        unfolding ind
        unfolding inv_mult [OF fa_in_G AiB_sum_in_G]
        unfolding m_comm [OF fa_in_G A_sum_in_G]
        unfolding m_assoc [OF A_sum_in_G fa_in_G B_sum_in_G]
        unfolding m_comm [OF fa_in_G B_sum_in_G]
        using AiB_sum_in_G AuB_sum_in_G A_sum_in_G B_sum_in_G fa_in_G
        apply (subst m_assoc)
           apply simp_all
        apply (subst m_assoc)
           apply simp_all
        apply (subst m_assoc)
           apply simp_all
        apply (subst reverse_equality [OF m_assoc])
        by simp_all
      show "f a \<otimes> finset_sum (A \<union> B) f =
    f a \<otimes> finset_sum A f \<otimes> finset_sum B f \<otimes> inv finset_sum (A \<inter> B) f"
        unfolding ind
        using AiB_sum_in_G AuB_sum_in_G A_sum_in_G B_sum_in_G fa_in_G
        apply (subst reverse_equality [OF m_assoc])
           apply simp_all
        apply (subst reverse_equality [OF m_assoc])
        by simp_all
    qed
  qed
  then show "finite A \<Longrightarrow>
    f ` A \<subseteq> carrier G \<Longrightarrow>
    finite B \<Longrightarrow>
    f ` B \<subseteq> carrier G \<Longrightarrow>
    finset_sum (A \<union> B) f =
    finset_sum A f \<otimes> finset_sum B f \<otimes> inv finset_sum (A \<inter> B) f"
    by simp
qed











lemma finset_sum_expand_domain:
  assumes "A \<subseteq> B"
  and "f ` A \<subseteq> carrier G"
  and "finite B"
  and trivial_outside_A: "\<And>x. x \<in> B \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = \<one>"
shows "finset_sum A f = finset_sum B f"
proof-
  define C where "C = {x. x \<in> B \<and> x \<notin> A}"
  have "B = A \<union> C"
    unfolding C_def
    using \<open>A \<subseteq> B\<close> by auto
  have fin: "finite A \<and> finite C"
    using \<open>finite B\<close>
    using \<open>B = A \<union> C\<close> by blast
  have "f ` C \<subseteq> {\<one>}"
    unfolding C_def
    using trivial_outside_A by auto

  have "C = {} \<or> C \<noteq> {}" by auto
  then have "finset_sum C f = \<one>"
  proof
    show "C = {} \<Longrightarrow> finset_sum C f = \<one>"
      apply simp
      using finset_sum_empty.
    assume "C \<noteq> {}"
    show "finset_sum C f = \<one>"
      unfolding finset_sum_def
      apply (rule_tac zero_sum)
      unfolding pointed_set.finite_set_to_list.simps
      apply auto
    proof-
      have bij : "bij_betw (pointed_set.finite_set_interval_bijection (SOME x. x \<in> C, C))
   {i. i < pointed_set.finite_set_length (SOME x. x \<in> C, C)} (snd (SOME x. x \<in> C, C))"
        apply (rule_tac conjunct1 [OF pointed_set.finite_set_interval_bijection_char])
        unfolding pointed_set.Obj'_def
        using \<open>C \<noteq> {}\<close>
         apply (simp add: some_in_eq)
        using fin by simp
      fix k
      assume "k < pointed_set.finite_set_length (SOME x. x \<in> C, C)"
      then have "pointed_set.finite_set_interval_bijection (SOME x. x \<in> C, C) k \<in> C"
        using bij
        unfolding bij_betw_def
        by auto
      then show "f (pointed_set.finite_set_interval_bijection (SOME x. x \<in> C, C) k) = \<one>"
        using \<open>f ` C \<subseteq> {\<one>}\<close> by auto
    qed
  qed
  have set_eq : "A \<inter> C = {}"
    unfolding C_def by auto
  have A_sum_in_G : "finset_sum A f \<in> carrier G"
    apply (rule_tac finset_sum_carrier)
    using fin apply simp
    using \<open>f ` A \<subseteq> carrier G\<close> by auto

  show "finset_sum A f = finset_sum B f"
    unfolding \<open>B = A \<union> C\<close>
    apply (subst finset_sum_union)
        apply (simp_all add: fin \<open>f ` A \<subseteq> carrier G\<close>)
    using  \<open>f ` C \<subseteq> {\<one>}\<close>
     apply auto[1]
    unfolding \<open>finset_sum C f = \<one>\<close>
    unfolding set_eq
    unfolding finset_sum_empty
    using A_sum_in_G by simp
qed
   

lemma finset_sum_binary_sum :
  assumes "finite A"
  and "f ` A \<subseteq> carrier G"
  and "g ` A \<subseteq> carrier G"
  shows "finset_sum A (\<lambda>x. f x \<otimes> g x) = finset_sum A f \<otimes> finset_sum A g"
proof-
  have "f ` A \<subseteq> carrier G \<longrightarrow> g ` A \<subseteq> carrier G \<longrightarrow> 
    finset_sum A (\<lambda>x. f x \<otimes> g x) = finset_sum A f \<otimes> finset_sum A g"
    apply (rule_tac finite_induct' [OF \<open>finite A\<close>])
    unfolding finset_sum_empty 
     apply simp
    apply safe
  proof-
    show "\<And>A a b. f ` insert a A \<subseteq> carrier G \<Longrightarrow> b \<in> A \<Longrightarrow> f b \<in> carrier G"
      by auto
    show "\<And>A a b. g ` insert a A \<subseteq> carrier G \<Longrightarrow> b \<in> A \<Longrightarrow> g b \<in> carrier G"
      by auto
    fix A a
    assume ind : "finset_sum A (\<lambda>x. f x \<otimes> g x) = finset_sum A f \<otimes> finset_sum A g"
    show "finite A \<Longrightarrow> a \<notin> A \<Longrightarrow>
           f ` insert a A \<subseteq> carrier G \<Longrightarrow>
           g ` insert a A \<subseteq> carrier G \<Longrightarrow>
          finset_sum (insert a A) (\<lambda>x. f x \<otimes> g x) =
           finset_sum (insert a A) f \<otimes> finset_sum (insert a A) g"
      apply (subst finset_sum_insert')
         apply auto
    proof-
      assume "finite A" "f ` A \<subseteq> carrier G"
      then have f_in_G : "finset_sum A f \<in> carrier G"
        apply (rule_tac finset_sum_carrier)
        by auto
      assume "g ` A \<subseteq> carrier G"
      then have g_in_G : "finset_sum A g \<in> carrier G"
        apply (rule_tac finset_sum_carrier)
        using \<open>finite A\<close> by auto
      show "finite A \<Longrightarrow>
    f a \<in> carrier G \<Longrightarrow>
    f ` A \<subseteq> carrier G \<Longrightarrow>
    g a \<in> carrier G \<Longrightarrow>
    g ` A \<subseteq> carrier G \<Longrightarrow>
    a \<notin> A \<Longrightarrow>
    f a \<otimes> g a \<otimes> finset_sum A (\<lambda>x. f x \<otimes> g x) =
    finset_sum (insert a A) f \<otimes> finset_sum (insert a A) g"
        apply (subst finset_sum_insert')
        using f_in_G apply auto
        apply (subst finset_sum_insert')
        using g_in_G apply auto
        unfolding ind
        apply (subst m_assoc)
           apply simp_all
        apply (subst m_assoc)
           apply simp_all
        apply (subst reverse_equality [OF m_assoc])
           apply simp_all
        apply (subst reverse_equality [OF m_assoc])
           apply simp_all
        using m_comm.
    qed
  qed
  then show ?thesis
    using assms by simp
qed


lemma finset_sum_independence: 
  assumes "finite A"
  and "f ` A \<subseteq> carrier G" 
  and "\<forall>x \<in> A. f x = g x"
 shows "finset_sum A f = finset_sum A g"
proof-
  have "f ` A \<subseteq> carrier G \<longrightarrow> (\<forall>x \<in> A. f x = g x) \<longrightarrow>
         finset_sum A f = finset_sum A g"
    apply (rule_tac finite_induct' [OF \<open>finite A\<close>])
    unfolding finset_sum_empty
     apply auto
    apply (subst finset_sum_insert')
       apply auto
  proof-
    fix A a
    show "finite A \<Longrightarrow>
           g a \<in> carrier G \<Longrightarrow>
           g ` A \<subseteq> carrier G \<Longrightarrow>
           f a = g a \<Longrightarrow>
           \<forall>x\<in>A. f x = g x \<Longrightarrow>
           finset_sum A f = finset_sum A g \<Longrightarrow>
           a \<notin> A \<Longrightarrow> g a \<otimes> finset_sum A g = finset_sum (insert a A) g"
      apply (subst finset_sum_insert')
      by auto
  qed
  then show ?thesis
    using assms by simp
qed

end



end
