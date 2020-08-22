theory ReducedHomology
  imports Main
         AbelianGroupCoproduct
         SimplicialSet
begin





lemma rev_get_app : 
  shows "rev_get (Suc n) f = app (rev_get n f) [f n]"
  apply (rule_tac getFaithful)
   apply (simp add: app_length)
  apply (subst get_rev_get)
   apply simp
  apply simp
proof-
  have l_eq: "n = length (rev_get n f)" by simp
  define n' where "n' = n"
  fix k
  assume "k < Suc n"
  then have "k < n \<or> k = n" by auto
  then show "f k = get (app (rev_get n f) [f n]) k"
    apply auto
     apply (subst getAppLemma)
      apply simp_all
    apply (subst reverse_equality [OF n'_def])
    apply (subst reverse_equality [OF n'_def])
    apply (subst reverse_equality [OF n'_def])
    apply (subst l_eq)
    unfolding n'_def
    apply (subst getAppLemma2)
    by simp
qed






context comm_group
begin


lemma zero_finset_sum :
  assumes "finite A" "(\<forall>x\<in> A. g x = \<one>)"
  shows "finset_sum A g = \<one>"
proof-
  have "(\<forall>x\<in> A. g x = \<one>) \<longrightarrow> finset_sum A g = \<one>"
    apply (rule_tac finite_induct' [OF \<open>finite A\<close>])
     apply (simp add: assms)
     apply (simp add: finset_sum_empty)
    apply auto
    apply (subst finset_sum_insert)
    by (simp_all add: assms)
  then show ?thesis
    by (simp add: assms)
qed


(*
lemma finset_sum_inv : 
  assumes "g \<in> A \<rightarrow> carrier G" "finite A"
  shows "finset_sum A (\<lambda>x. inv g x) = inv finset_sum A g"
proof-
  have carrier1 : "finset_sum A (\<lambda>x. inv g x) \<in> carrier G"
    apply (rule_tac finset_sum_carrier)
    using assms by auto
  have carrier2 : "finset_sum A g \<in> carrier G"
    apply (rule_tac finset_sum_carrier)
    using assms by auto
  have "finset_sum A (\<lambda>x. inv g x) \<otimes> finset_sum A g = \<one>"
    apply (subst reverse_equality [OF finset_sum_binary_sum])
    using assms apply auto
    apply (rule_tac zero_finset_sum)
     apply auto
  proof-
    fix x
    assume "x \<in> A"
    then have "g x \<in> carrier G"
      using assms by auto
    then show "inv g x \<otimes> g x = \<one>"
      by simp
  qed
  then show "finset_sum A (\<lambda>x. inv g x) = inv finset_sum A g"
    using carrier1 carrier2
    using local.inv_equality by auto
qed
*)



definition alternate :: "'a list \<Rightarrow> 'a list" where
  "alternate xs = rev_get (length xs) (\<lambda>k. if k mod 2 = 0 then get xs k else inv (get xs k))"


lemma alternate_length [simp]:
  "length (alternate xs) = length xs"
  unfolding alternate_def by simp

lemma alternate_carrier :
  assumes "k < length xs" "get xs k \<in> carrier G"
  shows "get (alternate xs) k \<in> carrier G"
  unfolding alternate_def
  by (simp add: assms)


definition alternating_sum :: "'a list \<Rightarrow> 'a" where
  "alternating_sum xs = sum (alternate xs)"

lemma alternating_sum_carrier :
  assumes "\<forall>k < length xs. get xs k \<in> carrier G"
  shows "alternating_sum xs \<in> carrier G"
  unfolding alternating_sum_def alternate_def
  apply (rule_tac sum_carrier)
  by (simp add: assms)


lemma sum_inv :
  assumes xs_in: "\<forall>k<length xs. get xs k \<in> carrier G"
  shows "inv (sum xs) = sum (rev_get (length xs) (\<lambda>k. inv (get xs k)))"
  apply (rule_tac local.inv_equality)
    apply (subst reverse_equality [OF binary_sum_sum])
       apply (simp add: xs_in)
      apply (simp add: xs_in)
     apply simp
    apply (rule_tac zero_sum)
    apply (simp add: xs_in)
   apply (rule_tac sum_carrier)
   apply (simp add: xs_in)
  apply (rule_tac sum_carrier)
  by (simp add: xs_in)




lemma alternating_sum_add :
  assumes xs_in: "\<forall>k<length xs. get xs k \<in> carrier G"
  shows "alternating_sum (k # xs) =
    k \<otimes> inv (alternating_sum xs)"
  unfolding alternating_sum_def
  unfolding alternate_def
  apply simp
  apply (subst sum_inv)
   apply (simp add: xs_in)
proof-
  have list_eq : "(rev_get (length xs)
       (\<lambda>ka. if Suc ka mod 2 = 0 then get (k # xs) (Suc ka) else inv get (k # xs) (Suc ka))) =
      (rev_get (length (rev_get (length xs) (\<lambda>k. if k mod 2 = 0 then get xs k else inv get xs k)))
       (\<lambda>k. inv get (rev_get (length xs) (\<lambda>k. if k mod 2 = 0 then get xs k else inv get xs k)) k))"
    apply (rule_tac getFaithful)
    using xs_in apply auto
    using mod_Suc by auto
  show "k \<otimes> local.sum
     (rev_get (length xs)
       (\<lambda>ka. if Suc ka mod 2 = 0 then get (k # xs) (Suc ka) else inv get (k # xs) (Suc ka))) =
    k \<otimes> local.sum
     (rev_get (length (rev_get (length xs) (\<lambda>k. if k mod 2 = 0 then get xs k else inv get xs k)))
       (\<lambda>k. inv get (rev_get (length xs) (\<lambda>k. if k mod 2 = 0 then get xs k else inv get xs k)) k))"
    unfolding list_eq
    using refl.
qed

definition minusone_tothe where
  "minusone_tothe n k = (if n mod 2 = 0 then k else inv k)"

lemma minusone_hom:
  "minusone_tothe n \<in> hom G G"
  unfolding minusone_tothe_def hom_def
  apply auto
  using inv_mult by simp


lemma alternating_sum_app :
  assumes k_in: "k \<in> carrier G"
  shows "\<forall>k < length xs. get xs k \<in> carrier G \<Longrightarrow> alternating_sum (app xs [k]) =
         alternating_sum xs \<otimes> (minusone_tothe (length xs) k)"
  unfolding minusone_tothe_def
  apply (induction xs)
   apply (simp add: alternating_sum_def alternate_def)
   apply (simp add: k_in)
  apply (subst alternating_sum_add)
   apply auto[1]
  unfolding app.simps
  apply (subst alternating_sum_add)
  unfolding app_length
   apply auto[1]
proof-
  fix a xs
  assume "\<forall>k<Suc (length xs). get (a # xs) k \<in> carrier G"
  then have xs_in : "\<forall>k < length xs. get xs k \<in> carrier G"
    by auto
  fix l
  assume "l < Suc (length xs)"
  then have "l < length xs \<or> l = length xs" by auto
  then show "get (app xs [k]) l \<in> carrier G"
    apply auto
     apply (subst getAppLemma)
      apply simp
     apply (simp add: xs_in)
    apply (subst getAppLemma2)
    by (simp add: k_in)
next
  fix a xs
  assume a_xs_in: "\<forall>k<length (a # xs). get (a # xs) k \<in> carrier G"
  then have xs_in : "\<forall>k < length xs. get xs k \<in> carrier G"
    by auto
  assume "(\<forall>k<length xs. get xs k \<in> carrier G \<Longrightarrow>
        alternating_sum (app xs [k]) = alternating_sum xs \<otimes> (if length xs mod 2 = 0 then k else inv k))"
  then have ind_eq :
       "alternating_sum (app xs [k]) = alternating_sum xs \<otimes> (if length xs mod 2 = 0 then k else inv k)"
    using xs_in by simp
  have if_eq : "(if length (a # xs) mod 2 = 0 then k else inv k) =
                inv (if length xs mod 2 = 0 then k else inv k)"
    using k_in mod_Suc by auto

  have sum_in : "alternating_sum xs \<in> carrier G"
    apply (rule_tac alternating_sum_carrier)
    using xs_in.
  have if_in : "(if length xs mod 2 = 0 then k else inv k) \<in> carrier G"
    using k_in by auto
  from a_xs_in have a_in : "a \<in> carrier G"
    by auto

  show "a \<otimes> inv alternating_sum (app xs [k]) =
       a \<otimes> inv alternating_sum xs \<otimes> (if length (a # xs) mod 2 = 0 then k else inv k)"
    unfolding ind_eq if_eq
    apply (subst inv_mult [OF sum_in if_in])
    apply (rule_tac reverse_equality [OF m_assoc])
    using a_in sum_in if_in by simp_all
qed

lemma alternating_sum_binary_sum :
  assumes "\<And>k. k < m \<Longrightarrow> g k \<in> carrier G" "\<And>k. k < m \<Longrightarrow> f k \<in> carrier G"
  shows  "alternating_sum (rev_get m (\<lambda>k. f k \<otimes> g k)) = 
     alternating_sum (rev_get m f) \<otimes> alternating_sum (rev_get m g)"
  unfolding alternating_sum_def
  apply (subst reverse_equality [OF binary_sum_sum])
     apply auto
    apply (rule_tac alternate_carrier)
     apply simp
    apply (simp add: assms)
   apply (rule_tac alternate_carrier)
    apply simp
   apply (simp add: assms)
proof-
  have list_eq : "(alternate (rev_get m (\<lambda>k. f k \<otimes> g k))) =
     (rev_get m (\<lambda>k. get (alternate (rev_get m f)) k \<otimes> get (alternate (rev_get m g)) k))"
    apply (rule_tac getFaithful)
     apply auto
    unfolding alternate_def
    apply auto
    apply (subst inv_mult)
    using assms by auto
  then show "local.sum (alternate (rev_get m (\<lambda>k. f k \<otimes> g k))) =
    local.sum (rev_get m (\<lambda>k. get (alternate (rev_get m f)) k \<otimes> get (alternate (rev_get m g)) k))"
    unfolding list_eq
    by simp
qed






end

context comm_group_hom
begin

interpretation F : group_hom G H f
  using is_group_hom.

lemma preserves_alternate :
  assumes "\<forall>n < length xs. get xs n \<in> carrier G" 
  shows  "fmap f (G.alternate xs) = H.alternate (fmap f xs)"
  apply (rule_tac getFaithful)
   apply simp
  apply (simp add: G.alternate_def H.alternate_def)
proof
  fix n
  assume "n < length xs"
  then have "get xs n \<in> carrier G"
    using assms by simp
  then show "f (inv\<^bsub>G\<^esub> get xs n) = inv\<^bsub>H\<^esub> f (get xs n)"
    by simp
qed
    
lemma preserves_sum :
  assumes "\<forall>n < length xs. get xs n \<in> carrier G"
  shows "f (G.sum xs) = H.sum (fmap f xs)"
  using assms
  apply (induction xs)
   apply simp
  apply auto
  apply (subst F.hom_mult)
    apply auto[1]
   apply (rule_tac G.sum_carrier)
   apply auto[1]
proof-
  fix a xs
  assume ind : "(\<forall>n<length xs. get xs n \<in> carrier G \<Longrightarrow>
        f (G.sum xs) =
        H.sum (rev_get (length xs) (\<lambda>n. f (get xs n))))"
  assume "\<forall>n<Suc (length xs). get (a # xs) n \<in> carrier G"
  then have "f (G.sum xs) =
        H.sum (rev_get (length xs) (\<lambda>n. f (get xs n)))"
    apply (rule_tac ind)
    by auto
  then show "f a \<otimes>\<^bsub>H\<^esub> f (G.sum xs) = f a \<otimes>\<^bsub>H\<^esub>
       H.sum (rev_get (length xs) (\<lambda>k. f (get xs k)))"
    by simp
qed
  
lemma preserves_alternating_sum:
  assumes "\<forall>n < length xs. get xs n \<in> carrier G"
  shows "f (G.alternating_sum xs) = H.alternating_sum (fmap f xs)"
  unfolding G.alternating_sum_def H.alternating_sum_def
  apply (subst preserves_sum)
  using G.alternate_carrier assms apply simp
  using preserves_alternate [OF assms] by simp


lemma preserves_list_carrier :
  assumes "\<forall>n < length xs. get xs n \<in> carrier G"
  shows "\<forall>n < length xs. get (fmap f xs) n \<in> carrier H"
  using assms by simp





end



context comm_group
begin


lemma minusone_suc :
   "x \<in> carrier G \<Longrightarrow> minusone_tothe m x \<otimes> minusone_tothe (Suc m) x = \<one>"
  unfolding minusone_tothe_def
  using mod_Suc by auto



lemma differential_squared_zero_lemma:
  assumes "\<And>i j. i < j \<Longrightarrow> 0 < m \<Longrightarrow> d i j = d (j - 1) i"
  and d_in: "\<And>i j. d i j \<in> carrier G"
  shows "alternating_sum (rev_get (Suc m)
   (\<lambda>i. alternating_sum  (rev_get m (\<lambda>j. d j i)))) = \<one>"
  using assms(1)
  apply (induction m)
   apply (simp add: alternating_sum_def alternate_def)
proof-
  fix m
  define k where "k = Suc m"
  assume simp_id : "(\<And>i j. i < j \<Longrightarrow> 0 < Suc m \<Longrightarrow> d i j = d (j - 1) i)"
  assume "((\<And>i j. i < j \<Longrightarrow> 0 < m \<Longrightarrow> d i j = d (j - 1) i) \<Longrightarrow>
          alternating_sum (rev_get (Suc m) (\<lambda>i. alternating_sum (rev_get m (\<lambda>j. d j i)))) = \<one>)"
  then have ind : "alternating_sum (rev_get k (\<lambda>i. alternating_sum (rev_get m (\<lambda>j. d j i)))) = \<one>"
    unfolding k_def
    using simp_id by auto

  have alt_carrier : "\<And>k m. alternating_sum (rev_get m (\<lambda>j. d j k)) \<in> carrier G"
    apply (rule_tac alternating_sum_carrier)
    using d_in by auto

  interpret minus_m : comm_group_hom G G "minusone_tothe m"
    unfolding comm_group_hom_def comm_group_hom_axioms_def
    using minusone_hom comm_group_axioms by simp
  interpret minus_k : comm_group_hom G G "minusone_tothe k"
    unfolding comm_group_hom_def comm_group_hom_axioms_def
    using minusone_hom comm_group_axioms by simp

  have list_eq1 : "(rev_get k (\<lambda>i. minusone_tothe m (d m i))) =
                   fmap (minusone_tothe m) (rev_get k (\<lambda>i. d m i))"
    apply (rule_tac getFaithful)
    by simp_all
  have list_eq2 : "(rev_get k (d m)) = (rev_get k (\<lambda>j. d j k))"
    apply (rule_tac getFaithful)
     apply auto
    apply (rule_tac reverse_equality)
    apply (subst simp_id)
    unfolding k_def
    by simp_all

  have alt_k_in : "(alternating_sum (rev_get k (\<lambda>j. d j k))) \<in> carrier G"
    apply (rule_tac alternating_sum_carrier)
    using d_in by auto

  show "alternating_sum (rev_get (Suc (Suc m)) (\<lambda>i. alternating_sum (rev_get (Suc m) (\<lambda>j. d j i)))) = \<one>"
    apply (subst reverse_equality [OF k_def])
    apply (subst rev_get_app)
    apply (subst rev_get_app)
    apply (subst alternating_sum_app)
    using alt_carrier apply blast
    unfolding reverse_equality [OF k_def]
     apply auto
     apply (subst alternating_sum_app)
    using d_in alt_carrier minus_m.preserves_carrier apply auto
    apply (subst alternating_sum_app)
      apply auto
    apply (subst alternating_sum_binary_sum)
      apply auto
    unfolding ind
    unfolding list_eq1
    apply (subst reverse_equality [OF minus_m.preserves_alternating_sum])
     apply auto
    unfolding list_eq2
    apply (subst m_assoc)
       apply auto
    using minus_k.preserves_carrier apply auto
    unfolding k_def
    apply (subst minusone_suc)
    unfolding reverse_equality [OF k_def]
    by auto
qed



end


context abelian_group_category
begin




definition pointwise_operation :: "('a list \<Rightarrow> 'a) \<Rightarrow>
              ('a, 'b) Ab_hom list \<Rightarrow> ('a, 'b) Ab_hom" where
  "pointwise_operation F xs = Some (\<lambda>x \<in> carrier (Dom' (the (get xs 0))). 
             F (fmap (\<lambda>g. fst (the g) x) xs) , Dom' (the (get xs 0)) ,
                              Cod' (the (get xs 0)) )"


lemma fst_pointwise :
  assumes "a \<in> carrier (Dom' (the (get xs 0)))"
  shows "fst (the (pointwise_operation F xs)) a = 
         F (rev_get (length xs) (\<lambda>k. (fst (the (get xs k)) a)))"
  unfolding pointwise_operation_def
  using assms by simp






definition alternating_sum_of_arrows :: "('a, 'b) Ab_hom list \<Rightarrow> ('a, 'b) Ab_hom" where
  "alternating_sum_of_arrows xs = pointwise_operation
    (comm_group.alternating_sum (Cod' (the (get xs 0)))) xs"


interpretation AbCC: classical_category Obj' Arr' Dom' Cod' Id' Comp'
  using is_classical_category.

lemma In_Hom_mapsto :
  assumes "AbCC.In_Hom f A B"
  shows "fst f \<in> carrier A \<rightarrow> carrier B"
  using assms
  unfolding AbCC.In_Hom_def
  unfolding Arr'_def hom_def
  by auto





lemma alternating_sum_arr :
  assumes xs_in_hom: "\<forall>k < length xs. AbCC.In_Hom (the (get xs k)) (Dom' (the (get xs 0))) (Cod' (the (get xs 0)))"
  and "xs \<noteq> []"
  shows "AbCC.arr (alternating_sum_of_arrows xs)"
  unfolding AbCC.arr_char
  apply (simp add: alternating_sum_of_arrows_def pointwise_operation_def)
  unfolding Arr'_def
  apply (simp add: Obj'_def Dom'_def Cod'_def)
  apply auto
proof-
  have "0 < length xs"
    using \<open>xs \<noteq> []\<close> by simp
  then have "AbCC.In_Hom (the (get xs 0)) (Dom' (the (get xs 0))) (Cod' (the (get xs 0)))"
    using assms by simp
  then have arr0: "Arr' (the (get xs 0))"
    unfolding AbCC.In_Hom_def by simp
  from arr0 show "comm_group (fst (snd (the (get xs 0))))"
    unfolding Arr'_def Obj'_def Dom'_def by simp
  then interpret Dom : comm_group "(fst (snd (the (get xs 0))))".
  from arr0 show "comm_group (snd (snd (the (get xs 0))))"
    unfolding Arr'_def Obj'_def Cod'_def by simp
  then interpret Cod : comm_group "(snd (snd (the (get xs 0))))".
  show "(\<lambda>x\<in>carrier (fst (snd (the (get xs 0)))).
        Cod.alternating_sum (rev_get (length xs) (\<lambda>n. fst (the (get xs n)) x)))
    \<in> hom (fst (snd (the (get xs 0)))) (snd (snd (the (get xs 0))))"
    unfolding hom_def
    apply auto
     apply (rule_tac Cod.alternating_sum_carrier)
     apply auto
  proof-
    fix x k
    assume x_in: "x \<in> carrier (fst (snd (the (get xs 0))))"
    assume "k < length xs"
    then have in_hom: "AbCC.In_Hom (the (get xs k)) (Dom' (the (get xs 0))) (Cod' (the (get xs 0)))"
      using assms by simp
    show "fst (the (get xs k)) x \<in> carrier (snd (snd (the (get xs 0))))"
      using In_Hom_mapsto [OF in_hom] x_in
      unfolding Dom'_def Cod'_def by auto
  next
    fix x y
    assume x_in : "x \<in> carrier (fst (snd (the (get xs 0))))"
    assume y_in : "y \<in> carrier (fst (snd (the (get xs 0))))"

    have xsx_in : "\<And>n. n < length xs \<Longrightarrow> 
             fst (the (get xs n)) x \<in> carrier (snd (snd (the (get xs 0))))"
      using In_Hom_mapsto x_in xs_in_hom
      unfolding reverse_equality [OF Dom'_def]
      unfolding reverse_equality [OF Cod'_def]
      by blast
    have xsy_in : "\<And>n. n < length xs \<Longrightarrow> 
             fst (the (get xs n)) y \<in> carrier (snd (snd (the (get xs 0))))"
      using In_Hom_mapsto y_in xs_in_hom
      unfolding reverse_equality [OF Dom'_def]
      unfolding reverse_equality [OF Cod'_def]
      by blast



    have list_eq1 : "(rev_get (length xs)
              (\<lambda>n. fst (the (get xs n)) (x \<otimes>\<^bsub>fst (snd (the (get xs 0)))\<^esub> y))) =
           (rev_get (length xs)
              (\<lambda>n. fst (the (get xs n)) x \<otimes>\<^bsub>snd (snd (the (get xs 0)))\<^esub> 
                   fst (the (get xs n)) y))"
      apply (rule_tac getFaithful)
       apply simp_all
      apply (rule_tac hom_mult)
        apply (simp_all add: x_in y_in)
    proof-
      fix n
      assume "n < length xs"
      then have "AbCC.In_Hom (the ((get xs) n)) (Dom' (the (get xs 0))) (Cod' (the (get xs 0)))"
        using assms by simp
      then have "fst (the (get xs n)) \<in> hom (Dom' (the (get xs 0))) (Cod' (the (get xs 0)))"
        unfolding AbCC.In_Hom_def Arr'_def
        by auto
      then show "fst (the (get xs n))
         \<in> hom (fst (snd (the (get xs 0)))) (snd (snd (the (get xs 0))))"
        unfolding Dom'_def Cod'_def.
    qed

    have list_eq2 : "
     (Cod.alternate (rev_get (length xs)
         (\<lambda>n. fst (the (get xs n)) x \<otimes>\<^bsub>snd (snd (the (get xs 0)))\<^esub>
               fst (the (get xs n)) y))) =  (rev_get (length xs)
       (\<lambda>k. get (Cod.alternate (rev_get (length xs) (\<lambda>n. fst (the (get xs n)) x)))
              k \<otimes>\<^bsub>snd (snd (the (get xs 0)))\<^esub>
      get (Cod.alternate  (rev_get (length xs) (\<lambda>n. fst (the (get xs n)) y))) k))"
      apply (rule_tac getFaithful)
       apply simp
      apply auto
      unfolding Cod.alternate_def
      apply auto
      apply (rule_tac Cod.inv_mult)
      using xsx_in apply simp
      using xsy_in.

    show "Cod.alternating_sum
            (rev_get (length xs)
              (\<lambda>n. fst (the (get xs n)) (x \<otimes>\<^bsub>fst (snd (the (get xs 0)))\<^esub> y))) =
           Cod.alternating_sum
            (rev_get (length xs)
              (\<lambda>n. fst (the (get xs n)) x)) \<otimes>\<^bsub>snd (snd (the (get xs 0)))\<^esub>
           Cod.alternating_sum (rev_get (length xs) (\<lambda>n. fst (the (get xs n)) y))"
      unfolding list_eq1
      unfolding Cod.alternating_sum_def
      apply (subst reverse_equality [OF Cod.binary_sum_sum])
         apply auto
        apply (rule_tac Cod.alternate_carrier)
         apply simp
        apply (simp add: xsy_in)
        apply (rule_tac Cod.alternate_carrier)
         apply simp
       apply (simp add: xsx_in)
      unfolding list_eq2
      by simp
  qed
qed

interpretation AbC : category comp
  using is_category.


lemma arr_comm_group_hom :
  assumes "AbC.arr f"
  shows "comm_group_hom (Dom' (the f)) (Cod' (the f)) (fst (the f))"
  unfolding comm_group_hom_def comm_group_hom_axioms_def
  using assms 
  unfolding comp_def AbCC.arr_char Arr'_def Obj'_def
  by simp_all


lemma in_hom_fst_hom :
  assumes "AbC.in_hom f A B"
  shows "fst (the f) \<in> hom (Dom' (the A)) (Dom' (the B))"
proof-
  have "AbCC.In_Hom (the f) (Dom' (the A)) (Dom' (the B))"
    using assms
    unfolding comp_def AbCC.in_hom_char by simp
  then show ?thesis
    unfolding AbCC.In_Hom_def
    unfolding Arr'_def
    by auto
qed

lemma alternating_sum_in_hom : 
  assumes xs_in_hom: "\<forall>k < length xs. AbCC.in_hom (get xs k) (AbCC.dom (get xs 0)) (AbCC.cod (get xs 0))"
  and "xs \<noteq> []"
  and "A = AbC.dom (get xs 0)"
  and "B = AbC.cod (get xs 0)"
shows "AbC.in_hom (alternating_sum_of_arrows xs) A B"
  unfolding \<open>A = AbC.dom (get xs 0)\<close>
  unfolding \<open>B = AbC.cod (get xs 0)\<close>
  unfolding comp_def
proof-
  have arr_0: "AbCC.arr (get xs 0)"
    using assms
    by blast
  have arr_sum: "AbCC.arr (alternating_sum_of_arrows xs)"
    apply (rule_tac alternating_sum_arr)
    using xs_in_hom \<open>xs \<noteq> []\<close>
    unfolding AbCC.in_hom_char
     apply auto
  proof-
    have dom_eq : "Dom' (the (AbCC.dom (get xs 0))) = Dom' (the (get xs 0))"
      unfolding AbCC.dom_char
      by (simp add: arr_0 Dom'_def Id'_def)
    have cod_eq : "Dom' (the (AbCC.cod (get xs 0))) = Cod' (the (get xs 0))"
      unfolding AbCC.cod_char
      by (simp add: arr_0 Dom'_def Id'_def)
    fix k
    assume "k < length xs"
    assume "\<forall>k<length xs.
            AbCC.ide (AbCC.dom (get xs 0)) \<and>
            AbCC.ide (AbCC.cod (get xs 0)) \<and>
            (\<exists>a aa b. get xs k = Some (a, aa, b)) \<and>
            AbCC.In_Hom (the (get xs k)) (Dom' (the (AbCC.dom (get xs 0))))
             (Dom' (the (AbCC.cod (get xs 0))))"
    then show "AbCC.In_Hom (the (get xs k)) (Dom' (the (get xs 0)))
          (Cod' (the (get xs 0)))"
      unfolding dom_eq cod_eq
      using \<open>k < length xs\<close> by simp
  qed

  show "AbCC.in_hom (alternating_sum_of_arrows xs) (AbCC.dom (get xs 0))
     (AbCC.cod (get xs 0))"
    apply (rule_tac AbCC.in_homI)
    using arr_sum apply simp
    unfolding AbCC.dom_char AbCC.cod_char
     apply (simp_all add: arr_sum arr_0)
    unfolding alternating_sum_of_arrows_def
    unfolding pointwise_operation_def
    by (simp_all add: Cod'_def Dom'_def)
qed


lemma comp_alternating_sum :
  assumes xs_in_hom: "\<forall>k < length xs. AbCC.in_hom (get xs k) (AbCC.dom (get xs 0)) (AbCC.cod (get xs 0))"
  and "AbC.arr f" "AbC.dom f = AbC.cod (get xs 0)" "xs \<noteq> []"
shows "comp f (alternating_sum_of_arrows xs) = alternating_sum_of_arrows (fmap (\<lambda>g. comp f g) xs)"
proof-
  have arr0 : "AbCC.arr (get xs 0)"
    using assms by blast
  have xs_In_Hom : "\<forall>k < length xs. AbCC.In_Hom (the (get xs k)) (Dom' (the (get xs 0))) (Cod' (the (get xs 0)))"
    using assms apply auto
    unfolding AbCC.in_hom_char AbCC.dom_char AbCC.cod_char
    using arr0 apply auto
    unfolding Dom'_def Id'_def Cod'_def
    by simp
  have seq : "\<And>k. k < length xs \<Longrightarrow> AbCC.seq f (get xs k)"
    apply (rule_tac AbCC.seqI)
    using assms apply blast
    using assms apply (simp add: comp_def)
    apply (subst AbCC.in_hom_cod)
    using assms apply blast
    using assms by (simp add: comp_def)
  then have seq0 : "AbCC.seq f (get xs 0)"
    using \<open>xs \<noteq> []\<close> by simp
  have comp_in_hom : "\<forall>k < length xs.
       AbCC.in_hom (AbCC.comp f (get xs k)) (AbCC.dom (AbCC.comp f (get xs 0))) (AbCC.cod ((AbCC.comp f (get xs 0))))"
    apply auto
    apply (rule_tac AbCC.in_homI)
    using seq apply simp_all
     apply (subst AbCC.dom_comp)
      apply (simp add: \<open>xs \<noteq> []\<close>)
    using assms AbCC.in_hom_dom apply blast
    apply (subst AbCC.cod_comp)
     apply (simp add: \<open>xs \<noteq> []\<close>)
    by simp
    
  have comp_In_Hom : "\<forall>k<length xs.
       AbCC.In_Hom (the (AbCC.comp f (get xs k))) (Dom' (the (AbCC.comp f (get xs 0)))) (Cod' (the (AbCC.comp f (get xs 0))))"
    using comp_in_hom apply auto
    unfolding AbCC.in_hom_char AbCC.dom_char AbCC.cod_char
    using seq0 apply auto
    unfolding Dom'_def Id'_def Cod'_def
    by simp
  have alt_arr : "AbCC.arr (alternating_sum_of_arrows xs)"
    apply (rule_tac alternating_sum_arr)
     apply (simp add: xs_In_Hom)
    using assms by simp


  have alt_seq : "AbCC.seq f (alternating_sum_of_arrows xs)"apply (rule_tac AbCC.seqI)
      apply (simp add: alt_arr)
    using assms
    unfolding reverse_equality [OF comp_def]
     apply simp_all
    apply (subst AbC.in_hom_cod [OF alternating_sum_in_hom])
    unfolding comp_def
    by simp_all
  have alt_in_hom : "AbC.in_hom (alternating_sum_of_arrows xs) (AbC.dom (get xs 0)) (AbC.cod (get xs 0))"
    apply (rule_tac alternating_sum_in_hom)
    using assms by simp_all


  show ?thesis
    apply (rule_tac fun_eqI)
    using assms
    unfolding comp_def
    apply (simp add: alt_seq)
       apply (rule_tac alternating_sum_arr)
        apply (simp add: \<open>xs \<noteq> []\<close>)
        apply (simp add: comp_In_Hom)
    apply simp_all
  proof-
    have "length (rev_get (length xs) (\<lambda>n. AbCC.comp f (get xs n))) \<noteq> length []"
      apply simp
      using \<open>xs \<noteq> []\<close>.
    then show neq: "rev_get (length xs) (\<lambda>n. AbCC.comp f (get xs n)) \<noteq> []"
      by fastforce

    have in_hom : "AbC.in_hom (alternating_sum_of_arrows (rev_get (length xs) (\<lambda>n. local.comp f (get xs n))))
            (AbC.dom (get xs 0)) (AbC.cod f)"
      apply (rule_tac alternating_sum_in_hom)
         apply simp
      using comp_in_hom apply (simp add: comp_def \<open>xs \<noteq> []\<close>)
        apply (simp add: neq comp_def)
       apply (simp_all add: \<open>xs \<noteq> []\<close>)
       apply (subst AbC.dom_comp)
        apply (simp add: seq0 comp_def)
       apply simp
      apply (subst AbC.cod_comp)
       apply  (simp add: seq0 comp_def)
      by simp

    show "AbCC.dom (AbCC.comp f (alternating_sum_of_arrows xs)) =
    AbCC.dom (alternating_sum_of_arrows (rev_get (length xs) (\<lambda>n. AbCC.comp f (get xs n))))"
      apply (subst AbCC.dom_comp)
      using alt_seq apply simp
      unfolding reverse_equality [OF comp_def]
      apply (subst AbC.in_hom_dom [OF alternating_sum_in_hom])
      using assms apply simp_all
      using AbC.in_hom_dom [OF in_hom].
    show "AbCC.cod (AbCC.comp f (alternating_sum_of_arrows xs)) =
    AbCC.cod (alternating_sum_of_arrows (rev_get (length xs) (\<lambda>n. AbCC.comp f (get xs n))))"
      apply (subst AbCC.cod_comp)
       apply (simp add: alt_seq)
      unfolding reverse_equality [OF comp_def]
      using AbC.in_hom_cod [OF in_hom] by simp
    have "AbCC.dom (AbCC.comp f (alternating_sum_of_arrows xs)) =
                    AbCC.dom (alternating_sum_of_arrows xs)"
      apply (rule_tac AbCC.dom_comp)
      using alt_seq.
    then have dom_eq1 : "(Dom' (the (AbCC.comp f (alternating_sum_of_arrows xs)))) =
                         (Dom' (the (alternating_sum_of_arrows xs)))"
      unfolding AbCC.dom_char
      using alt_seq alt_arr
      by (simp add: Id'_def)

    fix x
    assume x_in_comp: "x \<in> carrier (Dom' (the (AbCC.comp f (alternating_sum_of_arrows xs))))"
    then have x_in : "x \<in> carrier (Dom' (the (alternating_sum_of_arrows xs)))"
      unfolding dom_eq1.
    then have x_in0 : "x \<in> carrier (Dom' (the (get xs 0)))"
      using AbC.in_hom_dom [OF alt_in_hom]
      unfolding comp_def AbCC.dom_char
      by (simp add: alt_arr arr0 Id'_def)

    have seq0_eq : "(Cod' (the (get xs 0))) = Dom' (the f)"
      using AbCC.seqE [OF seq0] by simp
    have nx_in : "\<forall>n<length xs. fst (the (get xs n)) x \<in> carrier (Dom' (the f))"
      apply auto
    proof-
      fix n
      assume "n < length xs"
      then have n_in_hom: "AbCC.in_hom (get xs n) (AbCC.dom (get xs 0)) (AbCC.cod (get xs 0))"
        using assms by simp
      have "fst (the (get xs n)) \<in> carrier (Dom' (the (get xs 0))) \<rightarrow> carrier (Cod' (the (get xs 0)))"
        apply (rule_tac in_hom_mapsto [OF n_in_hom])
        unfolding AbCC.dom_char AbCC.cod_char
        by (simp_all add: arr0 Dom'_def Id'_def)
      then show "fst (the (get xs n)) x \<in> carrier (Dom' (the f))"
        using x_in0
        unfolding seq0_eq by auto
    qed

    interpret F : comm_group_hom "Dom' (the f)" "(Cod' (the f))" "fst (the f)"
      apply (rule_tac arr_comm_group_hom)
      using assms by simp

    have "AbC.cod (comp f (get xs 0)) = AbC.cod f"
      apply (rule_tac AbC.cod_comp)
      using seq0 by (simp add: comp_def)
    then have cod_eq : "(Cod' (the (local.comp f (get xs 0)))) = Cod' (the f)"
      using assms(2)
      unfolding comp_def AbCC.cod_char
      by (simp add: seq0 Id'_def)

    have "AbC.dom (comp f (get xs 0)) = AbC.dom (get xs 0)"
      apply (rule_tac AbC.dom_comp)
      using seq0
      unfolding comp_def.
    then have dom_eq : "(Dom' (the (local.comp f (get xs 0)))) = Dom' (the (get xs 0))"
      using arr0
      unfolding comp_def AbCC.dom_char
      by (simp add: seq0 Id'_def)

    have x_in_n : "\<And>n. n < length xs \<Longrightarrow> x \<in> carrier (Dom' (the (get xs n)))"
    proof-
      fix n
      assume "n < length xs"
      then have n_in_hom: "AbCC.in_hom (get xs n) (AbCC.dom (get xs 0)) (AbCC.cod (get xs 0))"
        using assms by simp
      then have arr_n: "AbCC.arr (get xs n)"
        by blast
      have "AbC.dom (get xs n) = AbC.dom (get xs 0)"
        using AbCC.in_hom_dom [OF n_in_hom]
        unfolding comp_def.
      then have "Dom' (the (get xs n)) = Dom' (the (get xs 0))"
        unfolding comp_def AbCC.dom_char
        by (simp add: arr0 arr_n Id'_def)
      then show "x \<in> carrier (Dom' (the (get xs n)))"
        using x_in0 by simp
    qed

    have list_eq : "(fmap (fst (the f)) (rev_get (length xs) (\<lambda>k. fst (the (get xs k)) x))) =
    (rev_get (length (rev_get (length xs) (\<lambda>n. local.comp f (get xs n))))
       (\<lambda>k. fst (the (get (rev_get (length xs) (\<lambda>n. local.comp f (get xs n))) k)) x))"
      apply (rule_tac getFaithful)
       apply simp
      apply simp
      unfolding comp_def
      apply (subst AbCC.comp_simp)
      using seq
       apply force
      unfolding Comp'_def
      by (simp add: x_in_n)

    show "fst (the (AbCC.comp f (alternating_sum_of_arrows xs))) x =
         fst (the (alternating_sum_of_arrows (rev_get (length xs) (\<lambda>n. AbCC.comp f (get xs n))))) x"
      apply (subst AbCC.comp_simp)
      using alt_seq apply auto[1]
      unfolding reverse_equality [OF comp_def]
      unfolding Comp'_def
      apply (simp add: x_in)
      unfolding alternating_sum_of_arrows_def
      apply (subst fst_pointwise)
      using x_in0 apply simp
      unfolding seq0_eq
      apply (subst F.preserves_alternating_sum)
       apply (simp add: nx_in)
      apply (subst get_rev_get)
       apply (simp add: \<open>xs \<noteq> []\<close>)
      unfolding cod_eq
      apply (subst fst_pointwise)
       apply (simp add: \<open>xs \<noteq> []\<close>)
      unfolding dom_eq
      using x_in0 apply simp
      unfolding list_eq by simp
  qed
qed
      

definition zero_map :: "('a, 'b) monoid_scheme \<Rightarrow> ('a, 'b) monoid_scheme \<Rightarrow> 
                        ('a, 'b) Ab_hom" where
  "zero_map A B = Some ((\<lambda>x \<in> carrier A . \<one>\<^bsub>B\<^esub> ) ,(A, B))"

lemma zero_map_arr : 
  assumes "comm_group A" "comm_group B"
  shows "AbCC.arr (zero_map A B)"
proof-
  interpret A : comm_group A
    using assms by simp
  interpret B : comm_group B
    using assms by simp
  show ?thesis
    unfolding AbCC.arr_char zero_map_def apply simp
    unfolding Arr'_def Obj'_def Dom'_def Cod'_def hom_def
    by (simp add: assms)
qed


lemma two_alt_sum_zero : 
  assumes "AbC.arr a" "a = b"
  shows "alternating_sum_of_arrows [a, b] = zero_map (Dom' (the a)) (Cod' (the a))"
proof-
  have in_hom : "AbCC.in_hom a (AbC.dom a) (AbC.cod a)"
    apply (rule_tac AbCC.in_homI)
    using \<open>AbC.arr a\<close> by (simp_all add: comp_def)

  have In_Hom : "AbCC.In_Hom (the a) (Dom' (the a)) (Cod' (the a))"
    unfolding AbCC.In_Hom_def
    using \<open>AbC.arr a\<close>
    unfolding comp_def AbCC.arr_char by simp
  interpret Dom : comm_group "Dom' (the a)"
    using \<open>AbC.arr a\<close>
    unfolding comp_def AbCC.arr_char Arr'_def Obj'_def by simp
  interpret Cod : comm_group "Cod' (the a)"
    using \<open>AbC.arr a\<close>
    unfolding comp_def AbCC.arr_char Arr'_def Obj'_def by simp

  have k_hom: "\<forall>k<Suc (Suc 0). AbCC.In_Hom (the (get [a, a] k)) (Dom' (the a)) (Cod' (the a))"
    apply auto
  proof-
    fix k
    assume "k < Suc (Suc 0)"
    then have "k = 0 \<or> k = 1" by auto
    then show "AbCC.In_Hom (the (get [a, a] k)) (Dom' (the a)) (Cod' (the a))"
      apply auto
      by (simp_all add: In_Hom)
  qed
  have sum_arr : "AbCC.arr (alternating_sum_of_arrows [a, a])"
    apply (rule_tac alternating_sum_arr)
     apply (simp add: k_hom)
    by simp
  have zero_arr : "AbCC.arr (zero_map (Dom' (the a)) (Cod' (the a)))"
    using zero_map_arr [OF Dom.comm_group_axioms Cod.comm_group_axioms].

  show ?thesis
    unfolding reverse_equality [OF \<open>a = b\<close>]
    apply (rule_tac fun_eqI)
    unfolding AbCC.dom_char AbCC.cod_char
        apply (simp_all add: sum_arr zero_arr)
    unfolding alternating_sum_of_arrows_def zero_map_def
    apply (simp add: Dom'_def pointwise_operation_def)
     apply (simp add: Cod'_def pointwise_operation_def)
    unfolding Dom'_def apply simp
    apply (subst fst_pointwise)
     apply (simp add: Dom'_def)
    unfolding Cod.alternating_sum_def Cod.alternate_def
    apply simp
  proof-
    fix x
    assume "x \<in> carrier (fst (snd (the a)))"
    then have "x \<in> carrier (Dom' (the a))"
      by (simp add: Dom'_def)
    then have "fst (the a) x \<in> carrier (Cod' (the a))"
      using in_hom_mapsto [OF in_hom refl refl] assms(1)
      unfolding comp_def AbCC.dom_char AbCC.cod_char
      unfolding Dom'_def Id'_def by auto
    then show "fst (the a) x \<otimes>\<^bsub>Cod' (the a)\<^esub> (inv\<^bsub>Cod' (the a)\<^esub> fst (the a) x 
               \<otimes>\<^bsub>Cod' (the a)\<^esub> \<one>\<^bsub>Cod' (the a)\<^esub>) = \<one>\<^bsub>Cod' (the a)\<^esub>"
      by simp
  qed
qed

lemma dom_Dom_eq : assumes "AbC.dom f = AbC.dom g" "AbC.arr f" "AbC.arr g"
  shows "Dom' (the f) = Dom' (the g)"
  using assms
  unfolding comp_def AbCC.dom_char
  by (simp add: Id'_def)

lemma seq_Seq_eq : assumes "AbC.dom f = AbC.cod g" "AbC.arr f" "AbC.arr g"
  shows "Dom' (the f) = Cod' (the g)"
  using assms
  unfolding comp_def AbCC.dom_char AbCC.cod_char
  by (simp add: Id'_def)

lemma cod_Cod_eq : assumes "AbC.cod f = AbC.cod g" "AbC.arr f" "AbC.arr g"
  shows "Cod' (the f) = Cod' (the g)"
  using assms
  unfolding comp_def AbCC.cod_char
  by (simp add: Id'_def)



end







locale Reduced_Homology =
  Y : pointed_simplicial_set Y +
  A : comm_group A
  for Y :: "(nat \<times> nat list) option \<Rightarrow> 'a pointed_set.parr option"
  and A :: "('b, 'c) monoid_scheme"
begin

interpretation P : pointed_set.
interpretation D : simplex.
interpretation Ab : abelian_group_category.
interpretation AbC : category Ab.comp
  using Ab.is_category.
interpretation AbCC : classical_category Ab.Obj' Ab.Arr' Ab.Dom' Ab.Cod' Ab.Id' Ab.Comp'
  using Ab.is_classical_category.

interpretation S : set_category SetCat.comp
  using SetCat.is_set_category.


interpretation CA : coproduct_of_A_functor A
  unfolding coproduct_of_A_functor_def
  using A.comm_group_axioms.
interpretation ColimFun : colimit_functoriality SetCat.comp Ab.comp "\<lambda>S. discrete_category.comp (S.set S)"
   coproduct_cocone.discrete_functor "coproduct_cocone.cocone Ab.comp CA.obj"
   "\<lambda>c. Some (Ab.Id' (CA.coproduct_of_A (S.set c)))" CA.coproduct_inc_nattrafo CA.coproduct_UP_map
  using CA.colimit_functoriality.


definition YA where
  "YA = CA.map \<circ> P.forget_functor \<circ> Y"

interpretation YA : "functor" D.comp Ab.comp YA
  unfolding YA_def
  apply (rule_tac functor_comp)
  using Y.X.functor_axioms apply simp
  apply (rule_tac functor_comp)
  using P.forget_functor apply simp
  using CA.is_functor.
  



definition degeneracy :: "nat \<Rightarrow> nat \<Rightarrow> ('a SetCat.arr \<Rightarrow> 'b, 'c) Ab_hom" where
  "degeneracy n k = YA (D.d n k)"


definition differential :: "nat \<Rightarrow> ('a SetCat.arr \<Rightarrow> 'b, 'c) Ab_hom" where
  "differential n = Ab.alternating_sum_of_arrows (rev_get (Suc n) (degeneracy n))"


definition degree_n_chains where
  "degree_n_chains k = YA (Some (fin_set.Id' (Suc k)))"


lemma n_chains_group : "comm_group (Ab.Dom' (the (degree_n_chains n)))"
  unfolding degree_n_chains_def
  using YA.preserves_ide [OF D.ide_Dn]
  unfolding Ab.comp_def
  unfolding AbCC.ide_char
  unfolding Ab.Arr'_def
  unfolding Ab.Obj'_def
  by blast


lemma degeneracy_in_hom : "AbCC.in_hom (degeneracy (Suc n) k) (AbCC.dom (degeneracy (Suc n) 0)) 
           (AbCC.cod (degeneracy (Suc n) 0))"
proof-
  have arr_d : "Y.X.A.arr (D.d (Suc n) 0)"
    using D.d_in_hom by blast
  show ?thesis
    unfolding degeneracy_def
    unfolding reverse_equality [OF Ab.comp_def]
    apply (subst YA.preserves_dom [OF arr_d])
    apply (subst YA.preserves_cod [OF arr_d])
    apply (rule_tac YA.preserves_hom)
    apply (subst Y.X.A.in_hom_dom [OF D.d_in_hom])
     apply simp
    apply (subst Y.X.A.in_hom_cod [OF D.d_in_hom])
     apply simp
    using D.d_in_hom by simp
qed

lemma arr_d0 : "Y.X.A.arr (D.d (Suc n) 0)"
    using D.d_in_hom by blast

lemma degeneracy_dom : "YA (Some (fin_set.Id' (Suc (Suc n)))) = AbC.dom (degeneracy (Suc n) 0)"
  unfolding degeneracy_def
    apply (subst YA.preserves_dom [OF arr_d0])
    apply (subst D.dom_char)
    using arr_d0 apply simp
    by (simp add: D.d_def)

lemma degeneracy_cod : "YA (Some (fin_set.Id' (Suc n))) = AbC.cod (degeneracy (Suc n) 0)"
  unfolding degeneracy_def
    apply (subst YA.preserves_cod [OF arr_d0])
    apply (subst D.cod_char)
    using arr_d0 apply simp
    by (simp add: D.d_def)

lemma differential_in_hom : "AbC.in_hom (differential (Suc n))
        (degree_n_chains (Suc n)) (degree_n_chains n)"
  unfolding degree_n_chains_def differential_def
  apply (rule_tac Ab.alternating_sum_in_hom)
     apply auto
    apply (subst reverse_equality [OF rev_get.simps(2)])
    apply (subst reverse_equality [OF rev_get.simps(2)])
    apply (subst get_rev_get)
     apply simp
  using degeneracy_in_hom apply blast
  using degeneracy_dom degeneracy_cod.

lemma fst_differential :
  "0 < n \<Longrightarrow> x \<in> carrier (Ab.Dom' (the (degeneracy n 0)))
     \<Longrightarrow> fst (the (differential n)) x = 
     comm_group.alternating_sum (Ab.Cod' (the (degeneracy n 0)))
     (rev_get (Suc n) (\<lambda>k. fst (the (degeneracy n k)) x))"
  unfolding differential_def Ab.alternating_sum_of_arrows_def
  unfolding Ab.pointwise_operation_def
  apply simp
proof-
  have list_eq : "rev_get n (\<lambda>k. fst (the (get (rev_get n (\<lambda>k. degeneracy n (Suc k))) k)) x) =
       rev_get n (\<lambda>k. fst (the (degeneracy n (Suc k))) x)"
    apply (rule_tac getFaithful)
    by simp_all
  then show "comm_group.alternating_sum (Ab.Cod' (the (degeneracy n 0)))
     (fst (the (degeneracy n 0)) x # rev_get n (\<lambda>k. fst (the (get (rev_get n (\<lambda>k. degeneracy n (Suc k))) k)) x)) =
    comm_group.alternating_sum (Ab.Cod' (the (degeneracy n 0)))
     (fst (the (degeneracy n 0)) x # rev_get n (\<lambda>k. fst (the (degeneracy n (Suc k))) x))"
    by simp
qed




interpretation PF : "functor" P.pointed_set_comp SetCat.comp P.forget_functor
  using P.forget_functor.


definition terminal_Y0_map where
  "terminal_Y0_map = S.mkArr (S.Dom (P.forget_functor (Y (Some (fin_set.Id' (Suc 0))))))
                     {S.unity} (\<lambda>x. S.unity)"

lemma terminal_Y0_arr: "S.arr terminal_Y0_map"
  unfolding terminal_Y0_map_def
  unfolding S.arr_mkArr
  apply auto
  using functor.preserves_ide [OF P.forget_functor Y.X.preserves_ide [OF D.ide_Dn]]
  using S.set_subset_Univ in_mono apply auto[1]
  using S.terminal_unity.

lemma terminal_Y0_in_hom : "S.in_hom terminal_Y0_map 
          (P.forget_functor (Y (Some (fin_set.Id' (Suc 0))))) (S.mkIde {S.unity})"
  apply (rule_tac S.in_homI)
    apply (simp add: terminal_Y0_arr)
proof-
  have arr1 : "Y.X.A.arr (Some (fin_set.Id' (Suc 0)))"
    using D.ide_Dn by simp
  show "S.dom terminal_Y0_map = P.forget_functor (Y (Some (fin_set.Id' (Suc 0))))"
    unfolding terminal_Y0_map_def
    apply (subst S.dom_mkArr)
    using terminal_Y0_arr terminal_Y0_map_def apply simp
    apply (subst S.mkIde_set)
     apply (rule_tac S.ide_dom)
    using PF.preserves_arr [OF Y.X.preserves_arr [OF arr1]] apply simp
    apply (subst PF.preserves_dom [OF Y.X.preserves_arr [OF arr1]])
    apply (subst Y.X.preserves_dom [OF arr1])
    unfolding D.dom_char [OF arr1]
    by (simp add: fin_set.Id'_def)
  show "S.cod terminal_Y0_map = S.mkIde {S.unity}"
    unfolding terminal_Y0_map_def
    apply (subst S.cod_mkArr)
    using terminal_Y0_arr terminal_Y0_map_def apply simp
    by simp
qed


definition augmentation_map :: "('a SetCat.arr \<Rightarrow> 'b, 'c) Ab_hom" where
  "augmentation_map = CA.map (terminal_Y0_map)"

lemma augmentation_arr : "AbC.arr augmentation_map"
  unfolding augmentation_map_def
  apply (rule_tac functor.preserves_arr [OF CA.is_functor])
  using terminal_Y0_arr.


lemma augmentation_in_hom : "AbC.in_hom augmentation_map 
     (degree_n_chains 0) (Some (Ab.Id' (CA.coproduct_of_A {S.unity})))"
  apply (rule_tac AbC.in_homI)
  using augmentation_arr apply simp_all
  unfolding Ab.comp_def
  unfolding AbCC.dom_char AbCC.cod_char
   apply simp_all
  unfolding augmentation_map_def degree_n_chains_def
  unfolding YA_def
proof-
  interpret CAF : "functor" SetCat.comp Ab.comp CA.map
    using CA.is_functor.

  have arr_1 : "Y.X.A.arr (Some (fin_set.Id' (Suc 0)))"
    using D.ide_Dn by simp
  have "AbC.dom (CA.map (terminal_Y0_map)) =
        (CA.map \<circ> P.forget_functor \<circ> Y) (Some (fin_set.Id' (Suc 0)))"
    unfolding CAF.preserves_dom [OF terminal_Y0_arr]
    apply simp
    unfolding terminal_Y0_map_def
    apply (subst S.dom_mkArr)
    using terminal_Y0_arr terminal_Y0_map_def apply simp
    apply (subst S.mkIde_set)
     apply (rule_tac S.ide_dom)
    using PF.preserves_arr [OF Y.X.preserves_arr [OF arr_1]] apply simp
    unfolding PF.preserves_dom [OF Y.X.preserves_arr [OF arr_1]]
    unfolding Y.X.preserves_dom [OF arr_1]
    unfolding D.dom_char [OF arr_1]
    by (simp add: fin_set.Id'_def)

  then show "AbCC.arr (CA.map terminal_Y0_map) \<Longrightarrow>
    Some (Ab.Id' (Ab.Dom' (the (CA.map terminal_Y0_map)))) =
    (CA.map \<circ> P.forget_functor \<circ> Y) (Some (fin_set.Id' (Suc 0)))"
    unfolding Ab.comp_def
    unfolding AbCC.dom_char
    by simp
  have "AbC.cod (CA.map (terminal_Y0_map)) =
        Some (Ab.Id' (CA.coproduct_of_A {S.unity}))"
    unfolding CAF.preserves_cod [OF terminal_Y0_arr]
    unfolding CA.map_def
    apply (subst ColimFun.colim_functor_obj_simp)
    using terminal_Y0_arr Y.X.B.ide_cod apply simp
  proof-
    have ide_PY1: "S.ide (P.forget_functor (Y (Some (fin_set.Id' (Suc 0)))))"
      apply (rule_tac PF.preserves_ide)
      apply (rule_tac Y.X.preserves_ide)
      using D.ide_Dn by simp
    have "(S.Cod terminal_Y0_map) = {S.unity}"
      unfolding terminal_Y0_map_def
      apply (subst S.cod_mkArr)
      unfolding S.arr_mkArr
       apply (simp add: ide_PY1 S.terminal_unity)
      apply (rule_tac S.set_mkIde)
      by (simp add: S.terminal_unity)
    then show "Some (Ab.Id' (CA.coproduct_of_A (S.Cod terminal_Y0_map))) = 
               Some (Ab.Id' (CA.coproduct_of_A {S.unity}))"
      by simp
  qed
  then show "AbCC.arr (CA.map terminal_Y0_map) \<Longrightarrow>
    Ab.Id' (Ab.Cod' (the (CA.map terminal_Y0_map))) = Ab.Id' (CA.coproduct_of_A {S.unity})"
    unfolding Ab.comp_def
    unfolding AbCC.cod_char
    by simp
qed

    


definition kernel' :: "('x, 'y) Ab_hom \<Rightarrow> 'x set" where
  "kernel' f = kernel (Ab.Dom' (the f)) (Ab.Cod' (the f)) (fst (the f))"

definition image' :: "('x, 'y) Ab_hom \<Rightarrow> 'x set" where
  "image' f = (fst (the f)) ` (carrier (Ab.Dom' (the f)))"

definition cycle :: "nat \<Rightarrow> ('a SetCat.arr \<Rightarrow> 'b) \<Rightarrow> bool" where
  "cycle n x = (if n = 0 
              then x \<in> kernel' (augmentation_map) 
              else x \<in> kernel' (differential n))"

definition cycle_group where
  "cycle_group n = subgroup_generated (Ab.Dom' (the (degree_n_chains n))) {x. cycle n x}"

lemma cycle_group_group : "comm_group (cycle_group n)"
  unfolding cycle_group_def
  apply (rule_tac group.abelian_subgroup_generated)
  using n_chains_group comm_group_def
  by auto

definition boundary :: "nat \<Rightarrow> ('a SetCat.arr \<Rightarrow> 'b) \<Rightarrow> bool" where
  "boundary n x = (x \<in> image' (differential (Suc n)))"

definition homology_group where
  "homology_group n = (cycle_group n) Mod (Collect (boundary n))"


lemma terminal_comp : 
  assumes "S.in_hom f X (P.forget_functor (Y (Some (fin_set.Id' (Suc 0)))))"
  and "S.in_hom g X (P.forget_functor (Y (Some (fin_set.Id' (Suc 0)))))"
shows "SetCat.comp terminal_Y0_map f = SetCat.comp terminal_Y0_map g"
proof-
  have seq_f : "S.seq terminal_Y0_map f"
    apply (rule_tac S.seqI')
    using assms apply blast
    using terminal_Y0_in_hom by blast
  have seq_g : "S.seq terminal_Y0_map g"
    apply (rule_tac S.seqI')
    using assms apply blast
    using terminal_Y0_in_hom by blast
  show ?thesis
    apply (rule_tac S.arr_eqI)
     apply (subst S.dom_comp [OF seq_f])
     apply (subst S.dom_comp [OF seq_g])
     apply (subst S.cod_comp [OF seq_f])
     apply (subst S.cod_comp [OF seq_g])
    unfolding S.in_hom_dom [OF assms(1)]
    unfolding S.in_hom_dom [OF assms(2)]
     apply (simp add: seq_f seq_g)
    unfolding S.Fun_comp [OF seq_f]
    unfolding S.Fun_comp [OF seq_g]
    unfolding S.in_hom_dom [OF assms(1)]
    unfolding S.in_hom_dom [OF assms(2)]
    apply (rule_tac ext)
    apply auto
    using terminal_Y0_arr
    unfolding terminal_Y0_map_def
    apply (subst S.Fun_mkArr)
     apply simp
    apply (subst S.Fun_mkArr)
     apply simp
  proof-
    fix x
    assume x_in: "x \<in> S.set X"
    have fx_in: "\<And>f. S.in_hom f X (P.forget_functor (Y (Some (fin_set.Id' (Suc 0))))) \<Longrightarrow> 
           S.Fun f x \<in> S.Dom (P.forget_functor (Y (Some (fin_set.Id' (Suc 0)))))"
    proof-
      fix f
      assume f_hom: "S.in_hom f X (P.forget_functor (Y (Some (fin_set.Id' (Suc 0)))))"
      have arr_f : "S.arr f"
        using f_hom by blast
      have seq_f : "S.seq terminal_Y0_map f"
        apply (rule_tac S.seqI')
        using f_hom apply blast
        using terminal_Y0_in_hom by blast
      have seq_eq: "S.dom terminal_Y0_map = S.cod f"
        apply (rule_tac S.seqE [OF seq_f]).
      have "x \<in> S.Dom f"
        using x_in
        unfolding S.in_hom_dom [OF f_hom].
      then have "S.Fun f x \<in> S.Cod f"
        using S.Fun_mapsto [OF arr_f] by auto
      then show "S.Fun f x \<in> S.Dom (P.forget_functor (Y (Some (fin_set.Id' (Suc 0)))))"
        unfolding reverse_equality [OF seq_eq]
        unfolding terminal_Y0_map_def
        by (metis S.comp_cod_arr S.in_homE S.seqE f_hom seq_eq terminal_Y0_map_def)
    qed
    show "(\<lambda>x\<in>S.Dom (P.forget_functor (Y (Some (fin_set.Id' (Suc 0))))). S.unity) (S.Fun f x) =
         (\<lambda>x\<in>S.Dom (P.forget_functor (Y (Some (fin_set.Id' (Suc 0))))). S.unity) (S.Fun g x)"
      using fx_in [OF assms(1)] fx_in [OF assms(2)]
      by simp
  qed
qed




lemma augmentation_differential_zero : 
     "Ab.comp augmentation_map (differential (Suc 0)) = Ab.zero_map 
     (Ab.Dom' (the (Ab.comp augmentation_map (degeneracy (Suc 0) 0))))
     (Ab.Cod' (the (Ab.comp augmentation_map (degeneracy (Suc 0) 0))))"
  unfolding differential_def
  apply (subst Ab.comp_alternating_sum)
      apply simp_all
proof-
  have seq0 : "S.seq terminal_Y0_map (P.forget_functor (Y (D.d (Suc 0) 0)))"
    apply (rule_tac S.seqI')
     apply (rule_tac functor.preserves_hom [OF P.forget_functor])
     apply (rule_tac Y.X.preserves_hom)
    using D.d_in_hom apply blast
    using terminal_Y0_in_hom.
  have seq1 : "S.seq terminal_Y0_map (P.forget_functor (Y (D.d (Suc 0) (Suc 0))))"
    apply (rule_tac S.seqI')
     apply (rule_tac functor.preserves_hom [OF P.forget_functor])
     apply (rule_tac Y.X.preserves_hom)
    using D.d_in_hom apply blast
    using terminal_Y0_in_hom.
  have aug_deg_eq: "Ab.comp augmentation_map (degeneracy (Suc 0) 0) = Ab.comp augmentation_map (degeneracy (Suc 0) (Suc 0))"
    unfolding augmentation_map_def degeneracy_def YA_def
    apply simp
    apply (subst reverse_equality [OF functor.preserves_comp [OF CA.is_functor]])
     apply (simp add: seq0)
    apply (subst reverse_equality [OF functor.preserves_comp [OF CA.is_functor]])
     apply (simp add: seq1)
    apply (subst terminal_comp)
      apply auto
     apply (rule_tac functor.preserves_hom [OF P.forget_functor])
     apply (rule_tac Y.X.preserves_hom)
    using D.d_in_hom apply blast
    apply (rule_tac functor.preserves_hom [OF P.forget_functor])
    apply (rule_tac Y.X.preserves_hom)
    using D.d_in_hom by blast
  show "Ab.alternating_sum_of_arrows
     [Ab.comp augmentation_map (degeneracy (Suc 0) 0), Ab.comp augmentation_map (degeneracy (Suc 0) (Suc 0))] =
    ReducedHomology.abelian_group_category.zero_map (Ab.Dom' (the (Ab.comp augmentation_map (degeneracy (Suc 0) 0))))
     (Ab.Cod' (the (Ab.comp augmentation_map (degeneracy (Suc 0) 0))))"
    apply (rule_tac Ab.two_alt_sum_zero)
     apply (simp add: augmentation_map_def degeneracy_def YA_def)
     apply (rule_tac functor.preserves_seq [OF CA.is_functor])
    using seq0 apply simp
    using aug_deg_eq.
  show "\<forall>k<Suc (Suc 0).
       AbCC.in_hom (get [degeneracy (Suc 0) 0, degeneracy (Suc 0) (Suc 0)] k) (AbCC.dom (degeneracy (Suc 0) 0))
        (AbCC.cod (degeneracy (Suc 0) 0))"
    apply auto
  proof-
    fix k
    assume "k < Suc (Suc 0)"
    then have "k = 0 \<or> k = 1" by auto
    then show "AbCC.in_hom (get [degeneracy (Suc 0) 0, degeneracy (Suc 0) (Suc 0)] k) (AbCC.dom (degeneracy (Suc 0) 0))
          (AbCC.cod (degeneracy (Suc 0) 0))"
      apply auto
      using degeneracy_in_hom by auto
  qed
  show "AbC.arr augmentation_map"
    using augmentation_in_hom by blast
  have arr_d : "Y.X.A.arr (D.d (Suc 0) 0)"
    using D.d_in_hom by blast
  show "AbC.dom augmentation_map = AbC.cod (degeneracy (Suc 0) 0)"
    unfolding AbC.in_hom_dom [OF augmentation_in_hom]
    unfolding degree_n_chains_def
    unfolding degeneracy_def
    apply (subst YA.preserves_cod [OF arr_d])
    apply (subst D.cod_char)
    using arr_d apply simp
    by (simp add: D.d_def)
qed

declare rev_get.simps(2)[simp del]


lemma boundary_cycle : "\<And>x. boundary n x \<Longrightarrow> cycle n x"
  unfolding boundary_def cycle_def image'_def kernel'_def kernel_def
  apply auto
proof-
  have arr_d0 : "AbCC.arr (differential (Suc 0))"
    using differential_in_hom
    unfolding Ab.comp_def by blast
  have "fst (the (differential (Suc 0))) \<in> 
          carrier (Ab.Dom' (the (differential (Suc 0)))) 
          \<rightarrow> carrier (Ab.Dom' (the augmentation_map))"
    apply (rule_tac Ab.in_hom_mapsto)
    unfolding reverse_equality [OF Ab.comp_def]
    using differential_in_hom apply blast
    unfolding reverse_equality 
            [OF AbC.in_hom_dom [OF differential_in_hom]]
    unfolding Ab.comp_def AbCC.dom_char
     apply (simp add: arr_d0 Ab.Id'_def Ab.Dom'_def)
    unfolding augmentation_map_def degree_n_chains_def YA_def
  proof-
    interpret F : "functor" P.pointed_set_comp Ab.comp "(CA.map \<circ> P.forget_functor)"
      apply (rule_tac functor_comp)
      using P.forget_functor apply simp
      using CA.is_functor.

    have arr_Y0 : "Y.X.B.arr (Y (Some (fin_set.Id' (Suc 0))))"
      apply (rule_tac Y.X.preserves_arr)
      apply (rule_tac Y.X.A.ideD(1))
      using D.ide_Dn by simp
    have "AbC.dom ((CA.map \<circ> P.forget_functor)(Y (Some (fin_set.Id' (Suc 0))))) 
          = AbC.dom (CA.map (terminal_Y0_map))"
      apply (subst F.preserves_dom [OF arr_Y0])
      apply (subst functor.preserves_dom [OF CA.is_functor])
      using terminal_Y0_arr apply simp
      unfolding S.in_hom_dom [OF terminal_Y0_in_hom]
      by (simp add: Y.X.preserves_ide [OF D.ide_Dn])
    then show "carrier (Ab.Dom' (the ((CA.map \<circ> P.forget_functor \<circ> Y) (Some (fin_set.Id' (Suc 0)))))) =
    carrier (Ab.Dom' (the (CA.map terminal_Y0_map)))"
      using F.preserves_arr [OF arr_Y0]
      using functor.preserves_arr [OF CA.is_functor terminal_Y0_arr]
      unfolding Ab.comp_def AbCC.dom_char
      by (simp add: Ab.Id'_def)
  qed
  then show d0x_carrier: "\<And>x. x \<in> carrier (Ab.Dom' (the (differential (Suc 0)))) \<Longrightarrow>
          n = 0 \<Longrightarrow> fst (the (differential (Suc 0))) x
          \<in> carrier (Ab.Dom' (the augmentation_map))"
    by auto
  fix x
  assume x_in: "x \<in> carrier (Ab.Dom' (the (differential (Suc 0))))"

  have seq : "AbCC.seq augmentation_map (differential (Suc 0))"
    apply (rule_tac AbCC.seqI')
    unfolding reverse_equality [OF Ab.comp_def]
     apply (rule_tac differential_in_hom)
    using augmentation_in_hom.

  have seq_deg : "AbC.seq augmentation_map (degeneracy (Suc 0) 0)" 
    apply (rule_tac AbC.seqI')
    unfolding Ab.comp_def
     apply (rule_tac degeneracy_in_hom)
    unfolding reverse_equality [OF Ab.comp_def]
    unfolding reverse_equality [OF degeneracy_cod]
    unfolding reverse_equality [OF degree_n_chains_def]
    using augmentation_in_hom by blast
  have "AbC.dom (Ab.comp augmentation_map (degeneracy (Suc 0) 0)) =
        AbC.dom (differential (Suc 0))"
    apply (subst AbC.dom_comp)
     apply (simp add: seq_deg)
    unfolding AbC.in_hom_dom [OF differential_in_hom]
    unfolding degree_n_chains_def
    unfolding degeneracy_dom
    using refl.
  then have dom_eq : "(Ab.Dom' (the (Ab.comp augmentation_map (degeneracy (Suc 0) 0)))) =
                 (Ab.Dom' (the (differential (Suc 0))))"
    unfolding Ab.comp_def
    unfolding AbCC.dom_char
    using seq_deg arr_d0
    unfolding Ab.comp_def
    by (simp add: Ab.Id'_def)
  have "AbC.cod (Ab.comp augmentation_map (degeneracy (Suc 0) 0)) = AbC.cod (augmentation_map)"
    apply (subst AbC.cod_comp)
    using seq_deg by simp_all
  then have cod_eq : "Ab.Cod' (the (Ab.comp augmentation_map (degeneracy (Suc 0) 0))) =
                 Ab.Cod' (the (augmentation_map))"
    unfolding Ab.comp_def
    unfolding AbCC.cod_char
    using seq_deg augmentation_arr
    unfolding Ab.comp_def
    by (simp add: Ab.Id'_def)

  have comp_char : "fst (the augmentation_map) (fst (the (differential (Suc 0))) x) =
                    fst (the (Ab.comp augmentation_map (differential (Suc 0)))) x"
    unfolding Ab.comp_def
    apply (subst AbCC.comp_simp)
    using seq apply auto[1]
    unfolding Ab.Comp'_def
    by (simp add: x_in)
  show "fst (the augmentation_map) (fst (the (differential (Suc 0))) x) = \<one>\<^bsub>Ab.Cod' (the augmentation_map)\<^esub>"
    unfolding comp_char
    unfolding augmentation_differential_zero
    unfolding Ab.zero_map_def
    unfolding dom_eq cod_eq
    by (simp add: x_in)
next
  have "n > 0 \<Longrightarrow> fst (the (differential (Suc n))) \<in> 
        carrier (Ab.Dom' (the (differential (Suc n))))
     \<rightarrow> carrier (Ab.Dom' (the (differential n)))"
    apply (rule_tac Ab.in_hom_mapsto)
    unfolding reverse_equality [OF Ab.comp_def]
    using differential_in_hom apply blast
  proof-
    have arr_dn : "\<And>n. AbCC.arr (differential (Suc n))"
      unfolding reverse_equality [OF Ab.comp_def]
      using differential_in_hom by blast
    have dom_eq: "\<And>n. carrier (Ab.Dom' (the (degree_n_chains (Suc n)))) =
    carrier (Ab.Dom' (the (differential (Suc n))))"
      apply (subst reverse_equality [OF
          AbC.in_hom_dom [OF differential_in_hom]])
      unfolding Ab.comp_def AbCC.dom_char
      by (simp add: arr_dn Ab.Id'_def Ab.Dom'_def)
    then show "carrier (Ab.Dom' (the (degree_n_chains (Suc n)))) =
    carrier (Ab.Dom' (the (differential (Suc n))))"
      by simp
    assume "0 < n"
    then obtain m where m_def : "n = Suc m"
      using gr0_conv_Suc by blast
    show "carrier (Ab.Dom' (the (degree_n_chains n))) =
    carrier (Ab.Dom' (the (differential n)))"
      unfolding m_def
      using dom_eq.
  qed
  then show dx_in: "\<And>x. x \<in> carrier (Ab.Dom' (the (differential (Suc n)))) \<Longrightarrow>
          0 < n \<Longrightarrow> fst (the (differential (Suc n))) x
          \<in> carrier (Ab.Dom' (the (differential n)))"
    by auto

  assume "0 < n"
  then obtain m where m_def: "n = Suc m"
    using Suc_pred' by blast

  define differential' where "differential' = differential"
  interpret D1 : comm_group_hom "Ab.Dom' (the (differential n))" 
                                "Ab.Cod' (the (differential n))" 
                                "fst (the (differential n))"
    apply (rule_tac Ab.arr_comm_group_hom)
    unfolding m_def
    using differential_in_hom by blast

  fix x
  assume x_in: "x \<in> carrier (Ab.Dom' (the (differential (Suc n))))"

  have dom_eq: "\<And>n j. (Ab.Dom' (the (degeneracy (Suc n) j))) = (Ab.Dom' (the (differential (Suc n))))"
    apply (rule_tac Ab.dom_Dom_eq)
    unfolding Ab.comp_def
      apply (subst AbCC.in_hom_dom [OF degeneracy_in_hom])
    unfolding reverse_equality [OF Ab.comp_def]
    unfolding AbC.in_hom_dom [OF differential_in_hom] 
    unfolding degree_n_chains_def 
    unfolding degeneracy_dom
      apply simp
    using degeneracy_in_hom
    unfolding reverse_equality [OF Ab.comp_def] apply blast
    using differential_in_hom by blast

  have seq_eq : "(Ab.Cod' (the (degeneracy (Suc n) 0))) = Ab.Dom' (the (differential n))"
    apply (rule_tac reverse_equality)
    apply (rule_tac Ab.seq_Seq_eq)
    unfolding m_def
    unfolding AbC.in_hom_dom [OF differential_in_hom]
    unfolding degree_n_chains_def
    unfolding degeneracy_cod apply simp
    using differential_in_hom apply blast
    using degeneracy_in_hom
    unfolding Ab.comp_def by blast

  have cod_eq : "(Ab.Cod' (the (degeneracy n 0))) = Ab.Cod' (the (differential n))"
    apply (rule_tac Ab.cod_Cod_eq)
    unfolding m_def
    unfolding AbC.in_hom_cod [OF differential_in_hom]
    unfolding degree_n_chains_def
    unfolding degeneracy_cod apply simp
    using degeneracy_in_hom 
    unfolding Ab.comp_def apply blast
    using differential_in_hom
    unfolding Ab.comp_def by blast



  have arr_deg : "\<And>k n. AbCC.arr (degeneracy (Suc n) k)"
    using degeneracy_in_hom by blast

  have deg_mapsto: "\<And>k. fst (the (degeneracy (Suc n) k)) \<in> 
        carrier (Ab.Dom' (the (differential (Suc n)))) 
     \<rightarrow> carrier (Ab.Dom' (the (differential n)))"
    apply (rule_tac Ab.in_hom_mapsto)
    using degeneracy_in_hom apply blast
    unfolding AbCC.dom_char AbCC.cod_char
    apply (simp_all add: arr_deg)
    unfolding dom_eq seq_eq
    by (simp_all add: Ab.Id'_def Ab.Dom'_def)
  have deg_x_in : "\<And>k. fst (the (degeneracy (Suc n) k)) x \<in> carrier (Ab.Dom' (the (differential n)))"
    using x_in deg_mapsto by auto

  have list_eq : "(rev_get (Suc (Suc n)) (\<lambda>na. fst (the (differential n))
               (get (rev_get (Suc (Suc n)) (\<lambda>k. fst (the (degeneracy (Suc n) k)) x)) na))) =
                 (rev_get (Suc (Suc n))
       (\<lambda>na. fst (the (differential n)) (fst (the (degeneracy (Suc n) na)) x)))"
    apply (rule_tac getFaithful)
    by auto


  show "fst (the (differential n)) (fst (the (differential (Suc n))) x) =
          \<one>\<^bsub>Ab.Cod' (the (differential n))\<^esub>"
    apply (subst reverse_equality [OF differential'_def])
    apply (subst fst_differential)
      apply (simp add: \<open>0 < n\<close>)
    unfolding dom_eq
     apply (simp add: x_in)
    unfolding differential'_def
    unfolding seq_eq
    apply (subst D1.preserves_alternating_sum)
     apply safe
     apply (subst get_rev_get)
      apply simp
     apply (simp add: deg_x_in)
    apply simp
    unfolding list_eq
    apply (subst fst_differential)
      apply (simp add: \<open>0 < n\<close>)
    using deg_x_in
    unfolding m_def dom_eq apply simp
    unfolding reverse_equality [OF m_def]
    unfolding cod_eq
    apply (rule_tac D1.H.differential_squared_zero_lemma)
  proof-
    fix i j :: nat
    assume "i < j"
    assume "0 < Suc n"
    have d_eq: "D.comp (D.d n i) (D.d (Suc n) j) = D.comp (D.d n (j - 1)) (D.d (Suc n) i)"
      using D.simplicial_identity_d_d [OF \<open>i < j\<close> \<open>0 < n\<close>].
    have deg_eq: "Ab.comp (degeneracy n i) (degeneracy (Suc n) j) =
          Ab.comp (degeneracy n (j - 1)) (degeneracy (Suc n) i)"
      unfolding degeneracy_def
      apply (subst reverse_equality [OF YA.preserves_comp])
       apply (rule_tac Y.X.A.seqI')
      using D.d_in_hom apply blast
       apply (rule_tac D.d_in_hom)
       apply (simp add: \<open>0 < n\<close>)
      apply (subst reverse_equality [OF YA.preserves_comp])
       apply (rule_tac Y.X.A.seqI')
      using D.d_in_hom apply blast
       apply (rule_tac D.d_in_hom)
       apply (simp add: \<open>0 < n\<close>)
      using d_eq by simp

    have seq1 : "AbCC.seq (degeneracy n i) (degeneracy (Suc n) j)"
      apply (rule_tac AbCC.seqI')
      unfolding degeneracy_def reverse_equality [OF Ab.comp_def]
       apply (rule_tac YA.preserves_hom)
      using D.d_in_hom apply blast
      apply (rule_tac YA.preserves_hom)
      using D.d_in_hom [OF \<open>0 < n\<close>].

    have seq2 : "AbCC.seq (degeneracy n (j - 1)) (degeneracy (Suc n) i)"
      apply (rule_tac AbCC.seqI')
      unfolding degeneracy_def reverse_equality [OF Ab.comp_def]
       apply (rule_tac YA.preserves_hom)
      using D.d_in_hom apply blast
      apply (rule_tac YA.preserves_hom)
      using D.d_in_hom [OF \<open>0 < n\<close>].

    have comp_char1 : "fst (the (degeneracy n i)) (fst (the (degeneracy (Suc n) j)) x) =
                       fst (the (Ab.comp (degeneracy n i) (degeneracy (Suc n) j) )) x"
      unfolding Ab.comp_def
      apply (subst AbCC.comp_simp)
      using seq1 apply auto[1]
      unfolding Ab.Comp'_def
      unfolding dom_eq
      using x_in by simp
    have comp_char2 : "fst (the (degeneracy n (j - 1))) (fst (the (degeneracy (Suc n) i)) x) =
                       fst (the (Ab.comp (degeneracy n (j - 1)) (degeneracy (Suc n) i) )) x"
      unfolding Ab.comp_def
      apply (subst AbCC.comp_simp)
      using seq2 apply auto[1]
      unfolding Ab.Comp'_def
      unfolding dom_eq
      using x_in by simp

    show "fst (the (degeneracy n i)) (fst (the (degeneracy (Suc n) j)) x) =
    fst (the (degeneracy n (j - 1))) (fst (the (degeneracy (Suc n) i)) x)"
      unfolding comp_char1 comp_char2
      using deg_eq by simp
  next
    fix i j
    have deg_mapsto : "fst (the (degeneracy n i)) \<in> carrier (Ab.Dom' (the (differential n))) \<rightarrow>
                   carrier (Ab.Cod' (the (differential n)))"
      apply (rule_tac Ab.in_hom_mapsto)
      unfolding m_def
      using degeneracy_in_hom apply blast
      unfolding reverse_equality [OF Ab.comp_def]
      unfolding reverse_equality [OF degeneracy_dom]
      unfolding reverse_equality [OF degeneracy_cod]
      unfolding reverse_equality [OF degree_n_chains_def]
    proof-
      have ide_chains: "\<And>m. AbC.ide (degree_n_chains m)"
        unfolding degree_n_chains_def
        apply (rule_tac YA.preserves_ide)
        using D.ide_Dn by simp
      have "(Ab.Dom' (the (degree_n_chains (Suc m)))) = (Ab.Dom' (the (differential (Suc m))))"
        apply (rule_tac Ab.dom_Dom_eq)
        unfolding AbC.in_hom_dom [OF differential_in_hom]
          apply (rule_tac AbC.ideD(2))
        using ide_chains apply simp_all
        using differential_in_hom by blast
      then show "carrier (Ab.Dom' (the (degree_n_chains (Suc m)))) = carrier (Ab.Dom' (the (differential (Suc m))))"
        by simp
      have "(Ab.Dom' (the (degree_n_chains m))) = (Ab.Cod' (the (differential (Suc m))))"
        apply (rule_tac Ab.seq_Seq_eq)
        unfolding AbC.in_hom_cod [OF differential_in_hom]
          apply (rule_tac AbC.ideD(2))
        using ide_chains apply simp_all
        using differential_in_hom by blast
      then show "carrier (Ab.Dom' (the (degree_n_chains m))) = carrier (Ab.Cod' (the (differential (Suc m))))"
        by simp
    qed

    show "fst (the (degeneracy n i)) (fst (the (degeneracy (Suc n) j)) x)
       \<in> carrier (Ab.Cod' (the (differential n)))"
      using deg_x_in deg_mapsto by auto
  qed
qed


lemma boundary_subgroup : "subgroup (Collect (boundary n)) (Ab.Dom' (the (degree_n_chains n)))"
  unfolding boundary_def image'_def
proof-
  have ide_chains : "AbC.ide (degree_n_chains (Suc n))"
    unfolding degree_n_chains_def
    apply (rule_tac YA.preserves_ide)
    using D.ide_Dn by blast
  have dom_eq : "(Ab.Dom' (the (differential (Suc n)))) = Ab.Dom' (the (degree_n_chains (Suc n)))"
    apply (rule_tac Ab.dom_Dom_eq)
    unfolding AbC.in_hom_dom [OF differential_in_hom]
      apply (rule_tac reverse_equality [OF AbC.ideD(2)])
    using ide_chains apply simp_all
    using differential_in_hom by blast
  interpret Diff : group_hom "(Ab.Dom' (the (differential (Suc n))))" 
                   "(Ab.Dom' (the (degree_n_chains n)))"
                   "fst (the (differential (Suc n)))"
    unfolding dom_eq
    unfolding group_hom_def
    apply auto
    using n_chains_group
    using comm_group.axioms(2) apply blast
    using n_chains_group
    using comm_group.axioms(2) apply blast
    unfolding group_hom_axioms_def
    using Ab.in_hom_fst_hom [OF differential_in_hom].
  have set_eq : "{x. x \<in> fst (the (differential (Suc n))) ` carrier (Ab.Dom' (the (differential (Suc n))))}
                 = fst (the (differential (Suc n))) ` carrier (Ab.Dom' (the (differential (Suc n))))"
    by auto
  show "subgroup {x. x \<in> fst (the (differential (Suc n))) ` carrier (Ab.Dom' (the (differential (Suc n))))}
     (Ab.Dom' (the (degree_n_chains n)))"
    unfolding set_eq
    using Diff.img_is_subgroup.
qed

lemma is_comm_group: "comm_group (homology_group n)"
  unfolding homology_group_def
  apply (rule_tac comm_group.abelian_FactGroup)
   apply (simp add: cycle_group_group)
  unfolding cycle_group_def
  apply (rule_tac group.subgroup_of_subgroup_generated)
  using n_chains_group comm_group_def apply blast
  using boundary_cycle apply auto[1]
  using boundary_subgroup.

end




end
