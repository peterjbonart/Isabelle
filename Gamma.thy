theory Gamma
  imports Main
         "Category3.Category"
         "Category3.Subcategory"
     
begin


type_synonym gamma = "(nat \<times> nat list) option"

fun get :: "('a list) \<Rightarrow> nat \<Rightarrow> 'a" where
 "get [] n = undefined" |
 "get (x # xs) 0 = x" |
 "get (x # xs) (Suc n) = get xs n"


fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app [] xs = xs" |
  "app (y # ys) xs = y # (app ys xs)"

fun rev_get :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where
  "rev_get 0 f = []" |
  "rev_get (Suc n) f = (f 0) # (rev_get n (\<lambda>k. f (Suc k)))"


fun fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "fmap f xs = (rev_get (length xs) (\<lambda>n. f (get xs n)))"




lemma app_length : "length (app xs ys) = length xs + length ys"
  apply (induction xs)
  by simp_all

lemma rev_get_length [simp] : "length (rev_get n f) = n"
  apply (induction n arbitrary: f)
   apply simp
  by simp

lemma getAppLemma : "n < length xs \<Longrightarrow> get (app xs ys) n = get xs n"
  apply (induction xs arbitrary: n)
   apply simp
proof-
  fix a xs n
  assume ind: "(\<And> m. m < length xs \<Longrightarrow> get (app xs ys) m = get xs m)"
  show "n < length (a # xs) \<Longrightarrow> get (app (a # xs) ys) n = get (a # xs) n"
    apply (induction n)
     apply simp
    by (simp add: ind)
qed

lemma getAppLemma2 : "get (app xs ys) (length xs) = get ys 0"
  apply (induction xs)
  by simp_all


lemma get_rev_get [simp]: "n < m \<Longrightarrow> get (rev_get m f) n = f n"
  apply (induction m arbitrary: n f)
   apply simp
  apply simp
proof-
  fix m n
  fix f :: "nat \<Rightarrow> 'a"
  assume ind : "(\<And>n (f :: nat \<Rightarrow> 'a). n < m \<Longrightarrow> get (rev_get m f) n = f n)"
  show "n < Suc m \<Longrightarrow> get (f 0 # rev_get m (\<lambda>k. f (Suc k))) n = f n"
    apply (induction n)
     apply simp
    by (simp add: ind)
qed


lemma getFaithful : "length xs = length ys \<Longrightarrow> (\<And> n. n < length xs \<Longrightarrow> get xs n = get ys n) \<Longrightarrow> xs = ys"
  apply(induction xs arbitrary : ys)
   apply simp
  apply simp
proof-
  fix a 
  fix xs ys :: "'a list"
  assume ind: "(\<And>ys. length xs = length ys \<Longrightarrow>
              (\<And>n. n < length ys \<Longrightarrow> get xs n = get ys n) \<Longrightarrow> xs = ys)"
  assume length: "Suc (length xs) = length ys"
  assume ind2: "(\<And>n. n < length ys \<Longrightarrow> get (a # xs) n = get ys n)"
  from length  obtain b zs where " ys = b # zs"
    by (meson Suc_length_conv \<open>Suc (length xs) = length ys\<close>)
  from length have "length xs = length zs"
    using \<open>ys = b # zs\<close> by auto
  from this and ind have h1: "(\<And>n. n < length zs \<Longrightarrow> get xs n = get zs n) \<Longrightarrow> xs = zs" by simp
  have "(\<And>n. n < length zs \<Longrightarrow> get xs n = get zs n)"
  proof-
    fix n
    assume "n < length zs"
    then have "Suc n < length ys" using \<open>ys = b # zs\<close>  by simp
    from this and ind2 have "get (a # xs) (Suc n) = get ys (Suc n)" by blast
    thus "get xs n = get zs n" using \<open>ys = b # zs\<close>  by simp
  qed
  from this and h1 have h2: "xs = zs" by simp
  have "0 < length ys" using \<open>ys = b # zs\<close>  by simp
  from this and ind2 have "get (a # xs) 0 = get ys 0" by blast
  then have "a = b" using \<open>ys = b # zs\<close>  by simp
  from this and h2 have "a # xs = b # zs" by simp
  thus "a # xs = ys" using \<open>ys = b # zs\<close>  by simp
qed

lemma rev_get_get : "rev_get (length xs) (get xs) = xs"
  apply (rule_tac getFaithful)
   apply simp
  by simp


lemma rev_get_independence : "(\<And> n. n < m \<Longrightarrow> f n = g n) \<Longrightarrow> rev_get m f = rev_get m g"
  apply (rule_tac getFaithful)
  by simp_all



locale fin_set
begin

abbreviation Dom' :: "nat \<times> nat list \<Rightarrow> nat" where
  "Dom' t \<equiv> length (snd t)"

abbreviation Cod' :: "nat \<times> nat list \<Rightarrow> nat" where
  "Cod' t \<equiv> fst t"

abbreviation Obj' :: "nat \<Rightarrow> bool" where
  "Obj' t \<equiv> True"

definition Arr' :: "nat \<times> nat list \<Rightarrow> bool" where
  "Arr' t \<equiv> (\<forall>n. (n < (Dom' t) \<longrightarrow> get (snd t) n < Cod' t))"

definition Id' :: "nat \<Rightarrow> nat \<times> nat list" where
  "Id' n \<equiv> (n, rev_get n (\<lambda>k. k))"

definition Comp' :: "(nat \<times> nat list) \<Rightarrow> (nat \<times> nat list) \<Rightarrow> nat \<times> nat list" where
  "Comp' f g \<equiv> (fst f ,rev_get (length (snd g)) (\<lambda>n. get (snd f) (get (snd g) n)))"

interpretation CC: classical_category Obj' Arr' Dom' Cod' Id' Comp'
  apply (unfold_locales)
  unfolding Arr'_def
           apply simp_all
proof
  show "\<And>a n. n < length (snd (Id' a)) \<longrightarrow> get (snd (Id' a)) n < fst (Id' a)"
    by (simp add: Id'_def get_rev_get)
  show "\<And>a. length (snd (Id' a)) = a"
    by (simp add: Id'_def)
  show "\<And>a. fst (Id' a) = a"
    by (simp add: Id'_def)
  show "\<And>f g. \<forall>n<length (snd f). get (snd f) n < length (snd g) \<Longrightarrow>
           \<forall>n<length (snd g). get (snd g) n < fst g \<Longrightarrow>
           fst f = length (snd g) \<Longrightarrow>
           \<forall>n<length (snd (Comp' g f)). get (snd (Comp' g f)) n < fst (Comp' g f)"
    by (simp add: Comp'_def get_rev_get)
  show "\<And>f g. \<forall>n<length (snd f). get (snd f) n < length (snd g) \<Longrightarrow>
           \<forall>n<length (snd g). get (snd g) n < fst g \<Longrightarrow>
           fst f = length (snd g) \<Longrightarrow> length (snd (Comp' g f)) = length (snd f)"
    by (simp add: Comp'_def)
  show "\<And>f g. \<forall>n<length (snd f). get (snd f) n < length (snd g) \<Longrightarrow>
           \<forall>n<length (snd g). get (snd g) n < fst g \<Longrightarrow>
           fst f = length (snd g) \<Longrightarrow> fst (Comp' g f) = fst g"
    by (simp add: Comp'_def)
  show "\<And>f. \<forall>n<length (snd f). get (snd f) n < fst f \<Longrightarrow> Comp' f (Id' (length (snd f))) = f"
  proof
    show "\<And>f. \<forall>n<length (snd f). get (snd f) n < fst f \<Longrightarrow>
         fst (Comp' f (Id' (length (snd f)))) = fst f"
      unfolding Comp'_def Id'_def by simp
    have subst: "\<And>f. (snd (Comp' f (Id' (length (snd f)))) = snd f) = 
(snd (Comp' f (Id' (length (snd f)))) = rev_get (length (snd f)) (get (snd f)))" by (simp add: rev_get_get)
    show "\<And>f. \<forall>n<length (snd f). get (snd f) n < fst f \<Longrightarrow>
         snd (Comp' f (Id' (length (snd f)))) = snd f"
      apply (subst subst)
      apply (simp add: Comp'_def Id'_def)
      apply (rule_tac getFaithful)
      by simp_all
  qed
  show "\<And>f. \<forall>n<length (snd f). get (snd f) n < fst f \<Longrightarrow> Comp' (Id' (fst f)) f = f"
  proof
    show "\<And>f. \<forall>n<length (snd f). get (snd f) n < fst f \<Longrightarrow> fst (Comp' (Id' (fst f)) f) = fst f"
      unfolding Comp'_def Id'_def by simp
    have subst: "\<And>f. 
   (snd (Comp' (Id' (fst f)) f) = snd f) =
   (snd (Comp' (Id' (fst f)) f) =  rev_get (length (snd f)) (get (snd f)))" by (simp add: rev_get_get)
    show "\<And>f. \<forall>n<length (snd f). get (snd f) n < fst f \<Longrightarrow> snd (Comp' (Id' (fst f)) f) = snd f"
      apply (subst subst)
      apply (simp add: Comp'_def Id'_def)
      apply (rule_tac getFaithful)
      by simp_all
  qed
  show "\<And>f g h.
       \<forall>n<length (snd f). get (snd f) n < length (snd g) \<Longrightarrow>
       \<forall>n<length (snd g). get (snd g) n < length (snd h) \<Longrightarrow>
       \<forall>n<length (snd h). get (snd h) n < fst h \<Longrightarrow>
       fst f = length (snd g) \<Longrightarrow>
       fst g = length (snd h) \<Longrightarrow> Comp' (Comp' h g) f = Comp' h (Comp' g f)"
  proof
    show "\<And>f g h.
       \<forall>n<length (snd f). get (snd f) n < length (snd g) \<Longrightarrow>
       \<forall>n<length (snd g). get (snd g) n < length (snd h) \<Longrightarrow>
       \<forall>n<length (snd h). get (snd h) n < fst h \<Longrightarrow>
       fst f = length (snd g) \<Longrightarrow>
       fst g = length (snd h) \<Longrightarrow> fst (Comp' (Comp' h g) f) = fst (Comp' h (Comp' g f))"
      unfolding Comp'_def by simp
    show "\<And>f g h.
       \<forall>n<length (snd f). get (snd f) n < length (snd g) \<Longrightarrow>
       \<forall>n<length (snd g). get (snd g) n < length (snd h) \<Longrightarrow>
       \<forall>n<length (snd h). get (snd h) n < fst h \<Longrightarrow>
       fst f = length (snd g) \<Longrightarrow>
       fst g = length (snd h) \<Longrightarrow> snd (Comp' (Comp' h g) f) = snd (Comp' h (Comp' g f))"
      unfolding Comp'_def apply simp
      apply (rule_tac getFaithful)
      by simp_all
  qed
qed

definition comp where "comp = CC.comp"

lemma is_classical_category : "classical_category Obj' Arr' Dom' Cod' Id' Comp'"
  using local.CC.classical_category_axioms.

lemma is_category : "category comp"
  using CC.is_functor functor.axioms(1) local.comp_def by auto

lemma arr_char: "partial_magma.arr comp f = (f \<noteq> None \<and> Arr' (the f))"
  unfolding comp_def
  using CC.arr_char.

lemma ide_char : "partial_magma.ide comp a = (Arr' (the a) \<and> a = Some (Id' (length (snd (the a)))))"
  unfolding comp_def
  using CC.ide_char.

lemma dom_char: "partial_magma.dom comp f = (if CC.arr f then Some (Id' (length (snd (the f)))) else None)"
  unfolding comp_def
  using CC.dom_char.

lemma cod_char: "partial_magma.cod comp f = (if CC.arr f then Some (Id' (fst (the f))) else None)"
  unfolding comp_def
  using CC.cod_char.


lemma comp_char : "partial_magma.arr comp f \<Longrightarrow>
                   partial_magma.arr comp g \<Longrightarrow>
                   partial_magma.dom comp g = partial_magma.cod comp f
               \<Longrightarrow> comp g f = Some (Comp' (the g) (the f))"
proof-
  have "partial_magma.arr comp f \<longrightarrow>
                   partial_magma.arr comp g \<longrightarrow>
                   partial_magma.dom comp g = partial_magma.cod comp f
               \<longrightarrow> comp g f = Some (Comp' (the g) (the f))"
    unfolding comp_def
    apply (subst CC.dom_char)
    apply (subst CC.cod_char)
    apply simp
    apply (subst CC.comp_char)
    apply (simp add: CC.arr_char)
    unfolding Id'_def by simp
  then show "partial_magma.arr comp f \<Longrightarrow>
                   partial_magma.arr comp g \<Longrightarrow>
                   partial_magma.dom comp g = partial_magma.cod comp f
               \<Longrightarrow> comp g f = Some (Comp' (the g) (the f))"
    by auto
qed


lemma comp_length : "length (snd (Comp' g f)) = length (snd f)"
  unfolding Comp'_def by simp


end






fun pairIndex:: "nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> nat" where
  "pairIndex n (a, b) = a * n + b"

fun revPairIndex :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "revPairIndex n c = (c div n, c mod n)"

fun productMap :: "(nat \<times> nat list) \<Rightarrow> (nat \<times> nat list) \<Rightarrow> nat \<times> nat list" where
  "productMap (x,xs) (y,ys) = (x*y, rev_get (length xs * length ys) 
        (\<lambda>k. pairIndex x (get xs (fst (revPairIndex (length xs) k)) , 
                          get ys (snd (revPairIndex (length xs) k)))))"

fun prod_proj1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat list" where
 "prod_proj1 n m = (n, rev_get (n*m) (\<lambda>k. fst (revPairIndex n k)))"

fun prod_proj2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat list" where
 "prod_proj2 n m = (m, rev_get (n*m) (\<lambda>k. snd (revPairIndex n k)))"


fun point :: "(nat \<times> nat list) \<Rightarrow> nat \<times> nat list" where
  "point (x, xs) = (x, 0 # xs)"

fun tail :: "(nat \<times> nat list) \<Rightarrow> nat \<times> nat list" where
  "tail (n,[]) = undefined" |
  "tail (n, x # xs) = (n, xs)"

fun smash_product :: "(nat \<times> nat list) \<Rightarrow> (nat \<times> nat list) \<Rightarrow> (nat \<times> nat list)" where
  "smash_product f g = point (productMap (tail f) (tail g))"



locale pointed_fin_set
begin

definition PointedArr' where
  "PointedArr' t \<equiv> (partial_magma.arr fin_set.comp t) \<and> (get (snd (the t)) 0 = 0) \<and> fin_set.Dom' (the t) \<noteq> 0"



lemma PointedArr_Id: "\<And>n. n \<noteq> 0 \<Longrightarrow> PointedArr' (Some (fin_set.Id' n))"
  unfolding PointedArr'_def
  apply auto
proof-
  fix n
  show "partial_magma.arr fin_set.comp (Some (fin_set.Id' n))"
    unfolding fin_set.comp_def
    apply (subst classical_category.arr_char)
    using fin_set.is_classical_category apply blast
    apply auto
    using fin_set.is_classical_category by (simp add: classical_category.Arr_Id)
  assume "0 < n"
  show "get (snd (fin_set.Id' n)) 0 = 0"
    unfolding fin_set.Id'_def apply simp
    apply (subst get_rev_get)
     apply simp_all
    using \<open>0<n\<close>.
  show "snd (fin_set.Id' n) = [] \<Longrightarrow> False"
    unfolding fin_set.Id'_def apply simp
    by (metis \<open>0 < n\<close> less_numeral_extra(3) list.size(3) rev_get_length)
qed




interpretation SC : subcategory fin_set.comp PointedArr'
  unfolding subcategory_def
  apply (simp add: fin_set.is_category)
  apply (unfold_locales)
proof-
  fix f
  assume p_arr: "PointedArr' f"
  show "partial_magma.arr fin_set.comp f"
    using p_arr by (simp add: PointedArr'_def)
  from p_arr have arr: "partial_magma.arr
               (classical_category.comp fin_set.Arr' (\<lambda>t. length (snd t)) fst fin_set.Comp')
               f" unfolding PointedArr'_def fin_set.comp_def by simp

  show "PointedArr' (partial_magma.dom fin_set.comp f)"
    apply (simp add: fin_set.comp_def)
    apply (subst classical_category.dom_char)
    using fin_set.is_classical_category apply blast
    apply (simp add: arr)
    apply (subst PointedArr_Id)
    using p_arr unfolding PointedArr'_def apply simp
    by simp
  have "fst (the f) \<noteq> 0"
  proof-
    have "partial_magma.arr fin_set.comp f"
      using p_arr unfolding PointedArr'_def by simp
    then have "fin_set.Arr' (the f)"
      unfolding fin_set.comp_def 
      using classical_category.arr_char fin_set.is_classical_category by blast
    then show "fst (the f) \<noteq> 0"
      unfolding fin_set.Arr'_def
      using p_arr pointed_fin_set.PointedArr'_def by auto
  qed
  show "PointedArr' (partial_magma.cod fin_set.comp f)"
    apply (simp add: fin_set.comp_def)
    apply (subst classical_category.cod_char)
    using fin_set.is_classical_category apply blast
    apply (simp add: arr)
    apply (subst PointedArr_Id)
    using p_arr unfolding PointedArr'_def
     apply (simp add: \<open>fst (the f) \<noteq> 0\<close>)
    by simp
  fix g
  assume p_arr_g: "PointedArr' g"
  assume seq : "partial_magma.cod fin_set.comp f = partial_magma.dom fin_set.comp g"
  have seq2: "fin_set.Cod' (the f) = fin_set.Dom' (the g)"
  proof-
    have eq1: "Some (fin_set.Id' (fin_set.Cod' (the f))) = partial_magma.cod fin_set.comp f"
      using fin_set.is_classical_category classical_category.cod_char
      using arr fin_set.comp_def by fastforce
    have eq2: "Some (fin_set.Id' (fin_set.Dom' (the g))) = partial_magma.dom fin_set.comp g"
      using fin_set.is_classical_category classical_category.dom_char
      using fin_set.comp_def p_arr_g pointed_fin_set.PointedArr'_def by fastforce
    from eq1 and eq2 and seq have
      "Some (fin_set.Id' (fin_set.Cod' (the f))) = Some (fin_set.Id' (fin_set.Dom' (the g)))" by simp
    then show "fin_set.Cod' (the f) = fin_set.Dom' (the g)"
      by (simp add: fin_set.Id'_def)
  qed

  have subst: "(f \<noteq> None \<and>
         g \<noteq> None \<and>
         fin_set.Arr' (the f) \<and>
         fin_set.Arr' (the g) \<and> fst (the f) = length (snd (the g))) = True"
    apply auto
    using arr classical_category.arr_char fin_set.is_classical_category apply fastforce
    using classical_category.arr_char fin_set.comp_def fin_set.is_classical_category p_arr_g pointed_fin_set.PointedArr'_def apply fastforce
    using p_arr unfolding PointedArr'_def
    using arr classical_category.arr_char fin_set.is_classical_category apply blast
    using p_arr_g unfolding PointedArr'_def
    using classical_category.arr_char fin_set.comp_def fin_set.is_classical_category pointed_fin_set.PointedArr'_def apply fastforce
    by (simp add: seq2)
  show "PointedArr' (fin_set.comp g f)"
    unfolding PointedArr'_def
    apply (subst category.seqI')
    apply (simp add: fin_set.is_category)
    apply (subst category.in_homI)
          apply (simp add: fin_set.is_category)
    using p_arr apply (simp add: PointedArr'_def)
        apply blast
       apply blast
      apply simp
     apply (subst category.in_homI)
         apply (simp add: fin_set.is_category)
    using p_arr_g apply (simp add: PointedArr'_def)
       apply (simp add: seq)
      apply blast
     apply simp
    apply simp
    apply (rule_tac conjI)
    unfolding fin_set.comp_def
     apply (subst classical_category.comp_char)
    using fin_set.is_classical_category apply blast
     apply (subst subst)
    unfolding fin_set.Comp'_def apply simp
     apply (subst get_rev_get)
    using p_arr unfolding PointedArr'_def apply simp
    using p_arr p_arr_g unfolding PointedArr'_def apply simp
    apply (subst classical_category.comp_char)
    using fin_set.is_classical_category unfolding fin_set.Comp'_def apply blast
    apply (subst subst)
    apply simp
  proof
    assume "rev_get (length (snd (the f))) (\<lambda>n. get (snd (the g)) (get (snd (the f)) n)) = []"
    then have "length (rev_get (length (snd (the f))) (\<lambda>n. get (snd (the g)) (get (snd (the f)) n))) = 0" by simp
    then have "length (snd (the f)) = 0" by simp
    then show "False" using p_arr unfolding PointedArr'_def by simp
  qed
qed

 

definition comp where "comp = SC.comp"

lemma is_category : "category comp"
  by (simp add: SC.subcategory_axioms local.comp_def subcategory.is_category)

lemma is_subcategory : "subcategory fin_set.comp PointedArr'"
  using local.SC.subcategory_axioms.





lemma dom_char : "partial_magma.arr local.comp f \<Longrightarrow>
               partial_magma.dom local.comp f =
               Some (fin_set.Id' (length (snd (the f))))"
  unfolding local.comp_def
  apply (subst subcategory.dom_char)
   apply (simp add: is_subcategory)
  apply simp
  unfolding fin_set.comp_def
  apply (subst classical_category.dom_char)
  using fin_set.is_classical_category apply blast
  apply simp
  using subcategory.arr_char
  using SC.arrE SC.inclusion fin_set.comp_def by auto

lemma cod_char: "partial_magma.arr local.comp f \<Longrightarrow>
               partial_magma.cod local.comp f =
               Some (fin_set.Id' (fst (the f)))"
  unfolding local.comp_def
  apply (subst subcategory.cod_char)
   apply (simp add: is_subcategory)
  apply simp
  unfolding fin_set.comp_def
  apply (subst classical_category.cod_char)
  using fin_set.is_classical_category apply blast
  apply simp
  using subcategory.arr_char
  using SC.arrE SC.inclusion fin_set.comp_def by auto



lemma ide_char : "partial_magma.ide comp f =
                  (f = Some (fin_set.Id' (length (snd (the f)))) \<and> (length (snd (the f)) \<noteq> 0))"
  unfolding local.comp_def
  apply (subst SC.ide_char)
  apply (subst SC.arr_char)
  unfolding fin_set.comp_def
  apply (subst classical_category.ide_char)
  using fin_set.is_classical_category apply simp
proof
  show "PointedArr' f \<and>
    fin_set.Arr' (the f) \<and> f = Some (fin_set.Id' (length (snd (the f)))) \<Longrightarrow>
    f = Some (fin_set.Id' (length (snd (the f)))) \<and> length (snd (the f)) \<noteq> 0"
    unfolding PointedArr'_def by simp
  have arr_f: "f = Some (fin_set.Id' (length (snd (the f)))) \<Longrightarrow>
    snd (the f) \<noteq> [] \<Longrightarrow> fin_set.Arr' (the f)"
  proof-
    assume eq: "f = Some (fin_set.Id' (length (snd (the f))))"
    show "fin_set.Arr' (the f)"
      apply (subst eq)
      apply simp
      using classical_category.Arr_Id [OF fin_set.is_classical_category] by simp
  qed
  show "f = Some (fin_set.Id' (length (snd (the f)))) \<and> length (snd (the f)) \<noteq> 0 \<Longrightarrow>
    PointedArr' f \<and> fin_set.Arr' (the f) \<and> f = Some (fin_set.Id' (length (snd (the f))))"
    apply auto
    unfolding PointedArr'_def
    apply simp
    unfolding fin_set.comp_def
     apply (subst classical_category.arr_char [OF fin_set.is_classical_category])
    using arr_f apply auto
    unfolding fin_set.Id'_def apply auto
  proof-
    assume eq: "f = Some (length (snd (the f)), rev_get (length (snd (the f))) (\<lambda>k. k))"
    assume "snd (the f) \<noteq> []"
    show "get (snd (the f)) 0 = 0"
      apply (subst eq)
      apply simp
      apply (subst get_rev_get)
      by (simp_all add: \<open>snd (the f) \<noteq> []\<close>)
  qed
qed



lemma comp_char : "partial_magma.arr comp f \<Longrightarrow>
                   partial_magma.arr comp g \<Longrightarrow>
                   partial_magma.dom comp g = partial_magma.cod comp f \<Longrightarrow>
                   comp g f = Some (fin_set.Comp' (the g) (the f))"
  unfolding comp_def
  apply (subst SC.comp_char)
  apply simp
  apply (simp add: SC.arr_char)
  unfolding PointedArr'_def
  apply simp
  by (simp add: fin_set.comp_char)


end




end
