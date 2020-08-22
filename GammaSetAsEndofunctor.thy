theory GammaSetAsEndofunctor
  imports Main
          PointedSet
          FinsetEquivalence
          ColimitFunctoriality
begin




locale finiteSubsetCat = 
  fixes X :: "'a pointed_set"
begin


interpretation pointed_set.



definition XObj where
  "XObj t = pointed_finset X t"

definition XArr where
  "XArr t = pointed_finset_triangle X (fst t) (snd t)"

definition XId where
  "XId t = (t,t)"

definition XComp where
  "XComp s t = (if (fst s) = (snd t) then (fst t, snd s) else undefined)"


lemma is_classical_category : "classical_category XObj XArr fst snd XId XComp"
  unfolding classical_category_def
  apply safe
  unfolding XArr_def XObj_def XId_def XComp_def pointed_finset_triangle_def
  by auto

interpretation CC: classical_category XObj XArr fst snd XId XComp
  using is_classical_category.

definition comp where
  "comp = CC.comp" 

lemma is_category : "category comp"
  unfolding comp_def
  by (simp add: CC.induces_category)

lemma arr_char : "partial_magma.arr comp f = (f \<noteq> None \<and> XArr (the f))"
  unfolding comp_def
  using CC.arr_char.

lemma dom_char : "partial_magma.dom comp f = (if partial_magma.arr comp f then Some (XId (fst (the f))) else None)"
  unfolding comp_def
  using CC.dom_char.

lemma cod_char : "partial_magma.cod comp f = (if partial_magma.arr comp f then Some (XId (snd (the f))) else None)"
  unfolding comp_def
  using CC.cod_char.

lemma comp_char : "comp g f =
  (if f \<noteq> None \<and> g \<noteq> None \<and> CC.Seq (the g) (the f) then Some (XComp (the g) (the f)) else None)"
  unfolding comp_def
  using CC.comp_char.





end

context begin


interpretation pointed_set.

lemma XId_arr : assumes "pointed_finset X A"  
  shows "partial_magma.arr (finiteSubsetCat.comp X) (Some (finiteSubsetCat.XId A))"
  unfolding finiteSubsetCat.arr_char
            finiteSubsetCat.XId_def
  apply simp
  unfolding finiteSubsetCat.XArr_def
            pointed_finset_triangle_def
  using \<open>pointed_finset X A\<close>
  by simp





section "Finite Subset Inclusion Functor"


definition inclusion_map :: "'a pointed_set \<Rightarrow> 'a pointed_set \<Rightarrow> 'a parr" where
  "inclusion_map S T = MkArr S T (\<lambda>x. x)"

lemma inclusion_map_arr: "pointed_finset_triangle X S T \<Longrightarrow>
       Arr' (inclusion_map S T)"
  unfolding pointed_finset_triangle_def
            Arr'_def
            setcat.Arr_def
            inclusion_map_def
            MkArr_def
            pointed_finset_def
            Obj'_def
  by auto



definition finite_subset_inclusion_functor where
  "finite_subset_inclusion_functor X = MkFunctor (finiteSubsetCat.comp X) pointed_set_comp
                       (\<lambda>t. Some (inclusion_map (fst (the t)) (snd (the t))))"


lemma arr_pointed_finset_triangle : assumes arr_f: "partial_magma.arr (finiteSubsetCat.comp X) f"
  shows "pointed_finset_triangle X (fst (the f)) (snd (the f))"
proof-
  from arr_f have "f \<noteq> None \<and> finiteSubsetCat.XArr X (the f)"
    using finiteSubsetCat.arr_char by blast
  then show pft: "pointed_finset_triangle X (fst (the f)) (snd (the f))"
    unfolding finiteSubsetCat.XArr_def by simp 
qed

lemma finite_subset_inclusion_functor_arr :
  assumes arr_f: "partial_magma.arr (finiteSubsetCat.comp X) f"
  shows "partial_magma.arr pointed_set_comp (finite_subset_inclusion_functor X f)"
  apply (subst arr_char)
  unfolding finite_subset_inclusion_functor_def apply (simp add: arr_f)
  using inclusion_map_arr [OF arr_pointed_finset_triangle [OF arr_f]].

lemma finite_subset_inclusion_functor_id: 
  assumes "pointed_finset X A"
  shows   "Some (Id' A) =
      finite_subset_inclusion_functor X (Some (finiteSubsetCat.XId A))"
  unfolding finite_subset_inclusion_functor_def
  apply (simp add: XId_arr [OF \<open>pointed_finset X A\<close>])
  unfolding inclusion_map_def MkArr_def Id'_def finiteSubsetCat.XId_def
  by simp


lemma finite_subset_inclusion_functor_dom :
  assumes arr_f: "partial_magma.arr (finiteSubsetCat.comp X) f"
  shows "partial_magma.dom pointed_set_comp (finite_subset_inclusion_functor X f) =
         finite_subset_inclusion_functor X (partial_magma.dom (finiteSubsetCat.comp X) f)"
proof-
  have arr_dom : "partial_magma.arr (finiteSubsetCat.comp X) (Some (fst (the f), fst (the f)))"
    apply (subst finiteSubsetCat.arr_char)
    unfolding finiteSubsetCat.XArr_def apply simp
    using arr_pointed_finset_triangle [OF arr_f]
    unfolding pointed_finset_triangle_def by simp
  show "partial_magma.dom pointed_set_comp (finite_subset_inclusion_functor X f) =
         finite_subset_inclusion_functor X (partial_magma.dom (finiteSubsetCat.comp X) f)"
    apply (subst finiteSubsetCat.dom_char)
    using arr_f unfolding finiteSubsetCat.comp_def apply simp
    apply (subst dom_char [OF finite_subset_inclusion_functor_arr [OF arr_f]])
    unfolding finite_subset_inclusion_functor_def finiteSubsetCat.XId_def 
              reverse_equality [OF finiteSubsetCat.comp_def]
    apply (simp add: arr_dom)
    unfolding Id'_def inclusion_map_def MkArr_def by simp
qed

lemma finite_subset_inclusion_functor_cod :
  assumes arr_f: "partial_magma.arr (finiteSubsetCat.comp X) f"
  shows "partial_magma.cod pointed_set_comp (finite_subset_inclusion_functor X f) =
         finite_subset_inclusion_functor X (partial_magma.cod (finiteSubsetCat.comp X) f)"
proof-
  have arr_cod : "partial_magma.arr (finiteSubsetCat.comp X) (Some (snd (the f), snd (the f)))"
    apply (subst finiteSubsetCat.arr_char)
    unfolding finiteSubsetCat.XArr_def apply simp
    using arr_pointed_finset_triangle [OF arr_f]
    unfolding pointed_finset_triangle_def by simp
  show "partial_magma.cod pointed_set_comp (finite_subset_inclusion_functor X f) =
         finite_subset_inclusion_functor X (partial_magma.cod (finiteSubsetCat.comp X) f)"
    apply (subst finiteSubsetCat.cod_char)
    using arr_f apply simp
    apply (subst cod_char [OF finite_subset_inclusion_functor_arr [OF arr_f]])
    unfolding finite_subset_inclusion_functor_def finiteSubsetCat.XId_def 
              reverse_equality [OF finiteSubsetCat.comp_def]
    apply (simp add: arr_cod)
    unfolding Id'_def inclusion_map_def MkArr_def by simp
qed



lemma finite_subset_inclusion_functor_all_pointedsets: "functor (finiteSubsetCat.comp X) pointed_set_comp (finite_subset_inclusion_functor X)"
  unfolding functor_def
  apply (simp add: finiteSubsetCat.is_category
                   is_category)
  unfolding functor_axioms_def
  apply safe
proof-
  fix f
  show "\<not> partial_magma.arr (finiteSubsetCat.comp X) f \<Longrightarrow>
         finite_subset_inclusion_functor X f = partial_magma.null pointed_set_comp"
    unfolding finite_subset_inclusion_functor_def by simp
  assume arr_f : "partial_magma.arr (finiteSubsetCat.comp X) f"
  show arr_if: "partial_magma.arr pointed_set_comp (finite_subset_inclusion_functor X f)"
    using finite_subset_inclusion_functor_arr [OF arr_f].
  show "partial_magma.dom pointed_set_comp (finite_subset_inclusion_functor X f) =
         finite_subset_inclusion_functor X (partial_magma.dom (finiteSubsetCat.comp X) f)"
    using finite_subset_inclusion_functor_dom [OF arr_f].
  show "partial_magma.cod pointed_set_comp (finite_subset_inclusion_functor X f) =
         finite_subset_inclusion_functor X (partial_magma.cod (finiteSubsetCat.comp X) f)"
    using finite_subset_inclusion_functor_cod [OF arr_f].
next
  fix g f
  assume arr_gf: "partial_magma.arr (finiteSubsetCat.comp X) (finiteSubsetCat.comp X g f)"
  then have gf_prop : "(partial_magma.arr (finiteSubsetCat.comp X) f \<and>
     partial_magma.arr (finiteSubsetCat.comp X) g \<and>
     partial_magma.dom (finiteSubsetCat.comp X) g = partial_magma.cod (finiteSubsetCat.comp X) f)"
    using category.seqE [OF finiteSubsetCat.is_category arr_gf] by auto
  from gf_prop have arr_f : "partial_magma.arr (finiteSubsetCat.comp X) f" by simp
  from gf_prop have arr_g : "partial_magma.arr (finiteSubsetCat.comp X) g" by simp
  from gf_prop have seq : "partial_magma.dom (finiteSubsetCat.comp X) g = 
                           partial_magma.cod (finiteSubsetCat.comp X) f" by simp
  have arr_if : "partial_magma.arr pointed_set_comp (finite_subset_inclusion_functor X f)" 
    using finite_subset_inclusion_functor_arr [OF arr_f].
  have arr_ig : "partial_magma.arr pointed_set_comp (finite_subset_inclusion_functor X g)" 
    using finite_subset_inclusion_functor_arr [OF arr_g].
  have i_seq : "partial_magma.dom pointed_set_comp (finite_subset_inclusion_functor X g) =
    partial_magma.cod pointed_set_comp (finite_subset_inclusion_functor X f)"
    apply (subst finite_subset_inclusion_functor_dom [OF arr_g])
    apply (subst finite_subset_inclusion_functor_cod [OF arr_f])
    using seq by simp

  have comp_helper: "f \<noteq> None \<and>
         g \<noteq> None \<and> finiteSubsetCat.XArr X (the f) \<and> finiteSubsetCat.XArr X (the g) \<and> snd (the f) = fst (the g)"
    using gf_prop
    unfolding finiteSubsetCat.comp_def
    unfolding classical_category.arr_char [OF finiteSubsetCat.is_classical_category]
              classical_category.dom_char [OF finiteSubsetCat.is_classical_category]
              classical_category.cod_char [OF finiteSubsetCat.is_classical_category]
              finiteSubsetCat.XId_def
    by auto
  from comp_helper have "snd (the f) = fst (the g)" by simp

  have arr_comp : "partial_magma.arr (finiteSubsetCat.comp X) (Some (fst (the f), snd (the g)))"
    unfolding finiteSubsetCat.arr_char
    apply simp
    using arr_pointed_finset_triangle [OF arr_f]
          arr_pointed_finset_triangle [OF arr_g]
    unfolding finiteSubsetCat.XArr_def
              pointed_finset_triangle_def
    using \<open>snd (the f) = fst (the g)\<close> by auto

  have fun_eq : "the (finite_subset_inclusion_functor X g) \<cdot> the (finite_subset_inclusion_functor X f) = 
      the (finite_subset_inclusion_functor X (Some (fst (the f), snd (the g))))"
    apply (rule_tac comp_eq_char)
    using arr_ig unfolding arr_char apply simp
    using arr_if unfolding arr_char apply simp
    using finite_subset_inclusion_functor_arr [OF arr_comp]
    unfolding arr_char apply simp
  proof-
    show "fst (snd (the (finite_subset_inclusion_functor X f))) =
    fst (snd (the (finite_subset_inclusion_functor X (Some (fst (the f), snd (the g))))))"
      unfolding finite_subset_inclusion_functor_def
                inclusion_map_def MkArr_def 
      by (simp add: arr_f arr_comp)
    show "snd (snd (the (finite_subset_inclusion_functor X g))) =
    snd (snd (the (finite_subset_inclusion_functor X (Some (fst (the f), snd (the g))))))"
      unfolding finite_subset_inclusion_functor_def
                inclusion_map_def MkArr_def 
      by (simp add: arr_g arr_comp)
    show "fst (snd (the (finite_subset_inclusion_functor X g))) = 
         snd (snd (the (finite_subset_inclusion_functor X f)))"
      using i_seq
      unfolding dom_char [OF arr_ig]
                cod_char [OF arr_if]
                Id'_def
      by simp
    fix x
    assume "x \<in> snd (fst (snd (the (finite_subset_inclusion_functor X f))))"
    then have x_in_dom : "x \<in> snd (fst (the f))"
      unfolding finite_subset_inclusion_functor_def apply (simp add: arr_f)
      unfolding inclusion_map_def MkArr_def by simp
    have x_in_dom_helper: "x \<in> snd (fst (the f)) \<Longrightarrow> x \<in> snd (fst (the g))"
      apply (subst reverse_equality [OF \<open>snd (the f) = fst (the g)\<close>])
      using arr_pointed_finset_triangle [OF arr_f]
      unfolding pointed_finset_triangle_def by auto
    show "fst (the (finite_subset_inclusion_functor X g)) (fst (the (finite_subset_inclusion_functor X f)) x) =
         fst (the (finite_subset_inclusion_functor X (Some (fst (the f), snd (the g))))) x"
      unfolding finite_subset_inclusion_functor_def apply (simp add: arr_f arr_g arr_comp)
      unfolding inclusion_map_def MkArr_def by (simp add: x_in_dom_helper)
  qed
  show "finite_subset_inclusion_functor X (finiteSubsetCat.comp X g f) =
           pointed_set_comp (finite_subset_inclusion_functor X g) (finite_subset_inclusion_functor X f)"
    apply (subst comp_char [OF arr_if arr_ig i_seq])
    apply (subst finiteSubsetCat.comp_char)
    apply (simp add: comp_helper)
    unfolding finiteSubsetCat.XComp_def
    apply (simp add: comp_helper)
    apply (subst fun_eq)
    unfolding finite_subset_inclusion_functor_def
    using arr_comp by simp
qed


lemma finite_subset_inclusion_functor_factors_finite_sets :
       "factorization (finiteSubsetCat.comp X) pointed_set_comp
        (finite_subset_inclusion_functor X) FiniteArr'"
  unfolding factorization_def
  apply (simp add: is_category 
                   finite_subcat_is_category 
                   finiteSubsetCat.is_category
                   finite_subcat
                   finite_subset_inclusion_functor_all_pointedsets)
  unfolding factorization_axioms_def
  apply safe
proof-
  fix f
  assume arr_f: "partial_magma.arr (finiteSubsetCat.comp X) f"
  then have "finiteSubsetCat.XArr X (the f)"
    unfolding finiteSubsetCat.arr_char
    by simp
  then have finite: "finite (snd (fst (the f))) \<and> finite (snd (snd (the f)))"
    unfolding finiteSubsetCat.XArr_def
              pointed_finset_triangle_def
              pointed_finset_def
    by simp
  show "FiniteArr' (finite_subset_inclusion_functor X f)"
    unfolding FiniteArr'_def
    apply safe
    using finite_subset_inclusion_functor_arr [OF arr_f] apply simp
    unfolding finite_subset_inclusion_functor_def apply (simp_all add: arr_f)
    unfolding inclusion_map_def MkArr_def by (simp_all add: finite)
qed


lemma finite_subset_inclusion_functor: "functor (finiteSubsetCat.comp X) pointed_finite_subcat (finite_subset_inclusion_functor X)"
  unfolding pointed_finite_subcat_def
  using factorization.is_functor [OF finite_subset_inclusion_functor_factors_finite_sets].



section "Finite Subset Image Functor"


lemma pointed_finset_triangle_id : "pointed_finset_triangle X S S = pointed_finset X S"
  unfolding pointed_finset_triangle_def by simp


fun pointed_image :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pointed_set \<Rightarrow> 'b pointed_set" where
  "pointed_image f (a, A) = (f a, f ` A)"

lemma pointed_image_simps : "pointed_image f X = (f (fst X), f ` (snd X))"
proof-
  have eq: "X = (fst X, snd X)"by simp
  show "pointed_image f X = (f (fst X), f ` (snd X))"
    apply (subst eq)
    apply (subst pointed_image.simps)
    by simp
qed


definition finite_subset_image_functor :: "'a parr \<Rightarrow> 
                 (('a pointed_set) \<times> ('a pointed_set)) option \<Rightarrow> 
                 (('a pointed_set) \<times> ('a pointed_set)) option "  where
  "finite_subset_image_functor f = MkFunctor 
                     (finiteSubsetCat.comp (Dom' f))
                     (finiteSubsetCat.comp (Cod' f))
                     (\<lambda>t. Some ( pointed_image (fst f) (fst (the t))  , 
                                 pointed_image (fst f) (snd (the t))))"

lemma pointed_finset_image : assumes "Arr' F" 
  shows "pointed_finset (fst (snd F)) A
   \<Longrightarrow> pointed_finset (snd (snd F)) (pointed_image (fst F) A)"
proof-
  fix A :: "'a \<times> 'a set"
  have "A = (fst A, snd A)" by simp
  assume "pointed_finset (fst (snd F)) A" 
  then show "pointed_finset (snd (snd F)) (pointed_image (fst F) A)"
    apply (subst \<open>A = (fst A, snd A)\<close>)
    unfolding pointed_finset_def Obj'_def apply auto
    using \<open>Arr' F\<close>
    unfolding Arr'_def setcat.Arr_def by auto
qed

lemma pointed_image_obj: 
  assumes "Obj' A"
  shows "Obj' (pointed_image f A)"
proof-
  have "A = (fst A, snd A)" by simp
  show "Obj' (pointed_image f A)"
    apply (subst \<open>A = (fst A, snd A)\<close>)
    unfolding pointed_image.simps
    using \<open>Obj' A\<close>
    unfolding Obj'_def by simp
qed


lemma finite_subset_image_functor_arr:
  assumes "Arr' F"
  and arr_f : "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f"
  shows "partial_magma.arr (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f)"

proof-
  have "fst (the f) = (fst (fst (the f)), snd (fst (the f)))"
    by simp
  then obtain a A where f_conv1: "fst (the f) = (a, A)" by blast
  have "snd (the f) = (fst (snd (the f)), snd (snd (the f)))"
    by simp
  then obtain b B where f_conv2: "snd (the f) = (b, B)" by blast

  have pftAB: "pointed_finset_triangle (Dom' F) (a, A) (b, B)"
    using arr_f
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def
              f_conv1 f_conv2
    by simp
  from pftAB have pftA : "pointed_finset (Dom' F) (a, A)"
    unfolding pointed_finset_triangle_def by simp
  from pftAB have pftB : "pointed_finset (Dom' F) (b, B)"
    unfolding pointed_finset_triangle_def by simp


  show arr_Ff: "partial_magma.arr (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f)"
    unfolding finiteSubsetCat.arr_char
              finite_subset_image_functor_def 
    using arr_f
    unfolding finiteSubsetCat.comp_def
    apply simp
    unfolding finiteSubsetCat.XArr_def
    apply simp
    unfolding f_conv1 f_conv2
  proof-
    show "pointed_finset_triangle (snd (snd F)) (pointed_image (fst F) (a, A)) (pointed_image (fst F) (b, B))"
      using pftAB
      unfolding pointed_finset_triangle_def
      using pointed_finset_image [OF \<open>Arr' F\<close> pftA]
      using pointed_finset_image [OF \<open>Arr' F\<close> pftB] by auto
  qed
qed


lemma finite_subset_image_functor_id : 
  assumes "Arr' F"
   and arr_f : "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f"
   and  "pointed_finset (fst (snd F)) A"
 shows      "Some (finiteSubsetCat.XId (pointed_image (fst F) A)) =
          finite_subset_image_functor F (Some (finiteSubsetCat.XId (A)))"
  using XId_arr [OF \<open>pointed_finset (fst (snd F)) A\<close>]
  unfolding finiteSubsetCat.XId_def finite_subset_image_functor_def 
  by (simp add: arr_f finite_subset_image_functor_arr [OF \<open>Arr' F\<close> arr_f])

lemma finite_subset_image_functor_dom:
  assumes "Arr' F"
  and arr_f : "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f"
  shows "partial_magma.dom (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f) =
         finite_subset_image_functor F (partial_magma.dom (finiteSubsetCat.comp (fst (snd F))) f)"
proof-
  have arr_dom : "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) (Some (fst (the f), fst (the f)))" 
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def
    apply simp
    apply (subst pointed_finset_triangle_id)
    using arr_f
    unfolding finiteSubsetCat.comp_def
              classical_category.arr_char [OF finiteSubsetCat.is_classical_category]
              finiteSubsetCat.XArr_def 
              pointed_finset_triangle_def
    by simp

  show "partial_magma.dom (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f) =
         finite_subset_image_functor F (partial_magma.dom (finiteSubsetCat.comp (fst (snd F))) f)" 
    using arr_f finite_subset_image_functor_arr [OF \<open>Arr' F\<close> arr_f]
    unfolding finiteSubsetCat.dom_char apply simp
  proof-
    show "Some (finiteSubsetCat.XId (fst (the (finite_subset_image_functor F f)))) =
          finite_subset_image_functor F (Some (finiteSubsetCat.XId (fst (the f))))"
      unfolding finiteSubsetCat.XId_def finite_subset_image_functor_def 
      by (simp add: arr_f finite_subset_image_functor_arr [OF \<open>Arr' F\<close> arr_f] arr_dom)
  qed
qed
lemma finite_subset_image_functor_cod:
  assumes "Arr' F"
  and arr_f : "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f"
  shows "partial_magma.cod (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f) =
         finite_subset_image_functor F (partial_magma.cod (finiteSubsetCat.comp (fst (snd F))) f)"
proof-
  have arr_cod : "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) (Some (snd (the f), snd (the f)))" 
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def
    apply simp
    apply (subst pointed_finset_triangle_id)
    using arr_f
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def 
              pointed_finset_triangle_def
    by simp

  show "partial_magma.cod (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f) =
         finite_subset_image_functor F (partial_magma.cod (finiteSubsetCat.comp (fst (snd F))) f)" 
    using arr_f finite_subset_image_functor_arr [OF \<open>Arr' F\<close> arr_f]
    unfolding finiteSubsetCat.cod_char apply simp
  proof-
    show "Some (finiteSubsetCat.XId (snd (the (finite_subset_image_functor F f)))) =
          finite_subset_image_functor F (Some (finiteSubsetCat.XId (snd (the f))))"
      unfolding finiteSubsetCat.XId_def finite_subset_image_functor_def 
      by (simp add: arr_f finite_subset_image_functor_arr [OF \<open>Arr' F\<close> arr_f] arr_cod)
  qed
qed

lemma finite_subset_image_functor : 
  assumes "Arr' F" 
  shows  "functor (finiteSubsetCat.comp (Dom' F))
                     (finiteSubsetCat.comp (Cod' F))
                  (finite_subset_image_functor F)"
  unfolding functor_def
  apply (simp add: finiteSubsetCat.is_category)
  unfolding functor_axioms_def
  apply safe
proof-
  fix f
  show "\<not> partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f \<Longrightarrow>
          finite_subset_image_functor F f = partial_magma.null (finiteSubsetCat.comp (snd (snd F)))"
    unfolding finite_subset_image_functor_def by simp
  assume arr_f : "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f"
  show "partial_magma.arr (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f)"
    using finite_subset_image_functor_arr [OF \<open>Arr' F\<close> arr_f].
  show "partial_magma.dom (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f) =
         finite_subset_image_functor F (partial_magma.dom (finiteSubsetCat.comp (fst (snd F))) f)"
    using finite_subset_image_functor_dom [OF \<open>Arr' F\<close> arr_f].
  show "partial_magma.cod (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f) =
         finite_subset_image_functor F (partial_magma.cod (finiteSubsetCat.comp (fst (snd F))) f)"
    using finite_subset_image_functor_cod [OF \<open>Arr' F\<close> arr_f].
next
  fix g f
  assume arr_gf: "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) (finiteSubsetCat.comp (fst (snd F)) g f)"

  have gf_prop : "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f \<and>
   partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) g \<and>
   partial_magma.dom (finiteSubsetCat.comp (fst (snd F))) g =
   partial_magma.cod (finiteSubsetCat.comp (fst (snd F))) f"
    using category.seqE [OF finiteSubsetCat.is_category arr_gf] by auto

  from gf_prop have comp_helper1 : "f \<noteq> None \<and>
         g \<noteq> None \<and>
         finiteSubsetCat.XArr (fst (snd F)) (the f) \<and>
         finiteSubsetCat.XArr (fst (snd F)) (the g) \<and> snd (the f) = fst (the g)"
    unfolding finiteSubsetCat.comp_def
              classical_category.arr_char [OF finiteSubsetCat.is_classical_category]
              classical_category.dom_char [OF finiteSubsetCat.is_classical_category]
              classical_category.cod_char [OF finiteSubsetCat.is_classical_category]
              finiteSubsetCat.XId_def
    by auto
  then have "snd (the f) = fst (the g)" by simp

  have Fgf_prop: "partial_magma.arr (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f) \<and>
   partial_magma.arr (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F g) \<and>
   partial_magma.dom (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F g) =
   partial_magma.cod (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f)" 
    using finite_subset_image_functor_arr [OF \<open>Arr' F\<close>] gf_prop apply simp
    apply (subst finite_subset_image_functor_dom [OF \<open>Arr' F\<close>])
     apply simp
    apply (subst finite_subset_image_functor_cod [OF \<open>Arr' F\<close>])
     apply simp
    by simp

  from Fgf_prop have comp_helper2: "finite_subset_image_functor F f \<noteq> None \<and>
        finite_subset_image_functor F g \<noteq> None \<and>
        finiteSubsetCat.XArr (snd (snd F)) (the (finite_subset_image_functor F f)) \<and>
        finiteSubsetCat.XArr (snd (snd F)) (the (finite_subset_image_functor F g)) \<and>
        snd (the (finite_subset_image_functor F f)) = fst (the (finite_subset_image_functor F g))"
    unfolding finiteSubsetCat.comp_def
              classical_category.arr_char [OF finiteSubsetCat.is_classical_category]
              classical_category.dom_char [OF finiteSubsetCat.is_classical_category]
              classical_category.cod_char [OF finiteSubsetCat.is_classical_category]
              finiteSubsetCat.XId_def
    by auto
  have arr_comp : "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) (Some (fst (the f), snd (the g)))"
    unfolding finiteSubsetCat.arr_char
    apply simp
    using comp_helper1
    unfolding finiteSubsetCat.XArr_def
              pointed_finset_triangle_def
              \<open>snd (the f) = fst (the g)\<close>
    by auto

  show "finite_subset_image_functor F (finiteSubsetCat.comp (fst (snd F)) g f) =
           finiteSubsetCat.comp (snd (snd F)) (finite_subset_image_functor F g) (finite_subset_image_functor F f)"
    unfolding finiteSubsetCat.comp_char
              finiteSubsetCat.XComp_def
    apply (simp add: comp_helper1 comp_helper2)
  proof-
    show "finite_subset_image_functor F (Some (fst (the f), snd (the g))) =
    Some (fst (the (finite_subset_image_functor F f)), snd (the (finite_subset_image_functor F g)))"
      unfolding finite_subset_image_functor_def by (simp add: gf_prop arr_comp)
  qed
qed


section "Natural transformation between image functors"

definition finite_subset_image_nattrafo :: "'a parr
    \<Rightarrow> (('a pointed_set) \<times> ('a pointed_set)) option \<Rightarrow> 'a parr option" where
  "finite_subset_image_nattrafo f = MkFunctor (finiteSubsetCat.comp (Dom' f)) pointed_set_comp
                    (\<lambda>t. Some ( MkArr (fst (the t)) (pointed_image (fst f) (snd (the t))) (\<lambda>x. fst f x)))"


lemma finite_subset_image_nattrafo_arr:
  assumes "Arr' F" 
  and arr_f : "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f"
  shows "partial_magma.arr pointed_set_comp (finite_subset_image_nattrafo F f)"
  unfolding arr_char
  apply (subst finite_subset_image_nattrafo_def)
  apply (simp add: arr_f)
  unfolding Arr'_def
  apply safe
proof-
  have f_conv: "snd (the f) = (fst (snd (the f)), snd (snd (the f)))" by simp

  show "setcat.Arr (forget (the (finite_subset_image_nattrafo F f)))"
    unfolding setcat.Arr_def finite_subset_image_nattrafo_def MkArr_def
    using arr_f apply auto
  proof-
    fix x
    assume "x \<in> snd (fst (the f))"
    then have "x \<in> snd (snd (the f))"
      using arr_f
      unfolding finiteSubsetCat.arr_char
                finiteSubsetCat.XArr_def
                pointed_finset_triangle_def 
      by auto
    show "fst F x \<in> snd (pointed_image (fst F) (snd (the f)))"
      apply (subst f_conv)
      unfolding pointed_image.simps
      apply simp
      using \<open>x \<in> snd (snd (the f))\<close>
      by simp
  qed
  have "Obj' (fst (the f))"
    using arr_f
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def
              pointed_finset_triangle_def
              pointed_finset_def
    by simp
  show "Obj' (fst (snd (the (finite_subset_image_nattrafo F f))))"
    unfolding finite_subset_image_nattrafo_def MkArr_def apply (simp add: arr_f)
    using \<open>Obj' (fst (the f))\<close>.
  show "Obj' (snd (snd (the (finite_subset_image_nattrafo F f))))"
    unfolding finite_subset_image_nattrafo_def MkArr_def apply (simp add: arr_f)
    apply (rule_tac pointed_image_obj)
    using arr_f
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def
              pointed_finset_triangle_def
              pointed_finset_def
    by simp
  have "(snd (the f)) = (fst (snd (the f)), snd (snd (the f)))" by simp
  show "fst (the (finite_subset_image_nattrafo F f))
     (fst (fst (snd (the (finite_subset_image_nattrafo F f))))) =
    fst (snd (snd (the (finite_subset_image_nattrafo F f))))"
    using \<open>Obj' (fst (the f))\<close>
    unfolding finite_subset_image_nattrafo_def 
              MkArr_def Obj'_def apply (simp add: arr_f)
    apply (subst \<open>(snd (the f)) = (fst (snd (the f)), snd (snd (the f)))\<close>)
    unfolding pointed_image.simps apply simp
    using arr_f
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def
              pointed_finset_triangle_def
              pointed_finset_def
    by simp
qed

lemma finite_subset_image_nattrafo_dom :
  assumes "Arr' F"
   and arr_f: "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f"
  shows "partial_magma.dom pointed_set_comp (finite_subset_image_nattrafo F f) =
         finite_subset_inclusion_functor (fst (snd F))
          (partial_magma.dom (finiteSubsetCat.comp (fst (snd F))) f)"
proof-
  from arr_f have pft: "pointed_finset_triangle (fst (snd F)) (fst (the f)) (snd (the f))"
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def
    by simp
  have dom_eq: "Dom' (the (finite_subset_image_nattrafo F f)) = fst (the f)"
    unfolding finite_subset_image_nattrafo_def MkArr_def by (simp add: arr_f)

show "partial_magma.dom pointed_set_comp (finite_subset_image_nattrafo F f) =
         finite_subset_inclusion_functor (fst (snd F))
          (partial_magma.dom (finiteSubsetCat.comp (fst (snd F))) f)"
    using dom_char
    apply (subst dom_char [OF finite_subset_image_nattrafo_arr [OF \<open>Arr' F\<close> arr_f]])
    unfolding finiteSubsetCat.dom_char
    apply (simp add: arr_f)
    apply (subst reverse_equality [OF finite_subset_inclusion_functor_id])
    using pft
    unfolding pointed_finset_triangle_def apply simp
    using dom_eq by simp
qed

lemma finite_subset_image_nattrafo_cod :
  assumes "Arr' F"
   and arr_f: "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f"
 shows "partial_magma.cod pointed_set_comp (finite_subset_image_nattrafo F f) =
         (finite_subset_inclusion_functor (snd (snd F)) \<circ> finite_subset_image_functor F)
          (partial_magma.cod (finiteSubsetCat.comp (fst (snd F))) f)"
proof-
  from arr_f have pft: "pointed_finset_triangle (fst (snd F)) (fst (the f)) (snd (the f))"
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def
    by simp
  have cod_eq: "Cod' (the (finite_subset_image_nattrafo F f)) = pointed_image (fst F) (snd (the f))"
    unfolding finite_subset_image_nattrafo_def MkArr_def by (simp add: arr_f)

  show "partial_magma.cod pointed_set_comp (finite_subset_image_nattrafo F f) =
         (finite_subset_inclusion_functor (snd (snd F)) \<circ> finite_subset_image_functor F)
          (partial_magma.cod (finiteSubsetCat.comp (fst (snd F))) f)"
    apply (subst cod_char [OF finite_subset_image_nattrafo_arr [OF \<open>Arr' F\<close> arr_f]])
    unfolding finiteSubsetCat.cod_char
    apply (simp add: arr_f)
    apply (subst reverse_equality [OF finite_subset_image_functor_id 
                                  [OF \<open>Arr' F\<close> arr_f]])
    using pft
    unfolding pointed_finset_triangle_def apply simp
    apply (subst reverse_equality [OF finite_subset_inclusion_functor_id])
    apply (rule_tac pointed_finset_image [OF \<open>Arr' F\<close>])
    using pft
    unfolding pointed_finset_triangle_def apply simp
    apply (subst cod_eq)
    by simp
qed


lemma finite_subset_image_nattrafo_all_pointedsets:
  assumes "Arr' F"
  shows "natural_transformation (finiteSubsetCat.comp (Dom' F)) pointed_set_comp
       (finite_subset_inclusion_functor (Dom' F))
       ((finite_subset_inclusion_functor (Cod' F)) \<circ>
       (finite_subset_image_functor F))
       (finite_subset_image_nattrafo F)"
  unfolding natural_transformation_def
  apply (simp add: finiteSubsetCat.is_category 
                   is_category
                   finite_subset_inclusion_functor_all_pointedsets)
  apply safe
   apply (rule_tac functor_comp)
  using finite_subset_image_functor [OF \<open>Arr' F\<close>] apply simp
  using finite_subset_inclusion_functor_all_pointedsets apply blast
  unfolding natural_transformation_axioms_def
  apply safe
proof-
  fix f
  show "\<not> partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f \<Longrightarrow>
         finite_subset_image_nattrafo F f = partial_magma.null pointed_set_comp"
    unfolding finite_subset_image_nattrafo_def by simp
  assume arr_f: "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) f"
  then have pft: "pointed_finset_triangle (fst (snd F)) (fst (the f)) (snd (the f))"
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def
    by simp

  show "partial_magma.dom pointed_set_comp (finite_subset_image_nattrafo F f) =
         finite_subset_inclusion_functor (fst (snd F))
          (partial_magma.dom (finiteSubsetCat.comp (fst (snd F))) f)"
    using finite_subset_image_nattrafo_dom [OF \<open>Arr' F\<close> arr_f].

  show "partial_magma.cod pointed_set_comp (finite_subset_image_nattrafo F f) =
         (finite_subset_inclusion_functor (snd (snd F)) \<circ> finite_subset_image_functor F)
          (partial_magma.cod (finiteSubsetCat.comp (fst (snd F))) f)"
    using finite_subset_image_nattrafo_cod [OF \<open>Arr' F\<close> arr_f].

  have arr_id1: "partial_magma.arr (finiteSubsetCat.comp (fst (snd F)))
          (Some (finiteSubsetCat.XId (fst (the f))))"
      apply (rule_tac XId_arr)
    using pft 
    unfolding pointed_finset_triangle_def by simp
  have pf_id: "pointed_finset (fst (snd F)) (snd (finiteSubsetCat.XId (fst (the f))))"
    unfolding finiteSubsetCat.XId_def
    apply simp
    using pft
    unfolding pointed_finset_triangle_def
    by simp

  have arr_Ff: "partial_magma.arr (finiteSubsetCat.comp (snd (snd F))) (finite_subset_image_functor F f)"
    using finite_subset_image_functor_arr [OF \<open>Arr' F\<close> arr_f].


  have eq1: "fst (the (finite_subset_image_functor F f)) = 
            pointed_image (fst F) (snd (finiteSubsetCat.XId (fst (the f))))"
    unfolding finiteSubsetCat.XId_def apply simp
    unfolding finite_subset_image_functor_def by (simp add: arr_f)


  show "pointed_set_comp
          ((finite_subset_inclusion_functor (snd (snd F)) \<circ> finite_subset_image_functor F) f)
          (finite_subset_image_nattrafo F
            (partial_magma.dom (finiteSubsetCat.comp (fst (snd F))) f)) =
         finite_subset_image_nattrafo F f"
    unfolding finiteSubsetCat.dom_char
    apply (simp add: arr_f)
    apply (subst comp_char)
       apply (rule_tac finite_subset_image_nattrafo_arr [OF \<open>Arr' F\<close>])
       apply (subst finiteSubsetCat.arr_char)
    apply simp
       apply (rule_tac classical_category.Arr_Id [OF finiteSubsetCat.is_classical_category])
    unfolding finiteSubsetCat.XObj_def
    using pft unfolding pointed_finset_triangle_def apply simp
      apply (rule_tac finite_subset_inclusion_functor_arr)
      apply (rule_tac finite_subset_image_functor_arr [OF \<open>Arr' F\<close> arr_f])
    unfolding finite_subset_inclusion_functor_dom [OF arr_Ff]
              finite_subset_image_functor_dom [OF \<open>Arr' F\<close> arr_f]
              finiteSubsetCat.dom_char
              finite_subset_image_nattrafo_cod [OF \<open>Arr' F\<close> arr_id1]
              finiteSubsetCat.cod_char
     apply (simp add: arr_Ff arr_id1)
     apply (subst reverse_equality [OF finite_subset_image_functor_id [OF \<open>Arr' F\<close> arr_f pf_id]])
    using eq1 apply simp
  proof-
    have EQ: "the (finite_subset_inclusion_functor (snd (snd F)) (finite_subset_image_functor F f)) \<cdot>
      the (finite_subset_image_nattrafo F (Some (finiteSubsetCat.XId (fst (the f))))) =
      the (finite_subset_image_nattrafo F f)"
      apply (rule_tac comp_eq_char)
      using finite_subset_inclusion_functor_arr [OF arr_Ff]
      unfolding arr_char apply simp
      using finite_subset_image_nattrafo_arr [OF \<open>Arr' F\<close> arr_id1]
      unfolding arr_char apply simp
      using finite_subset_image_nattrafo_arr [OF \<open>Arr' F\<close> arr_f]
      unfolding arr_char apply simp
    proof-
      show "fst (snd (the (finite_subset_image_nattrafo F (Some (finiteSubsetCat.XId (fst (the f))))))) =
    fst (snd (the (finite_subset_image_nattrafo F f)))"
        unfolding finite_subset_image_nattrafo_def MkArr_def apply (simp add: arr_f arr_id1)
        unfolding finiteSubsetCat.XId_def by simp
      show "snd (snd (the (finite_subset_inclusion_functor (snd (snd F))
                    (finite_subset_image_functor F f)))) =
    snd (snd (the (finite_subset_image_nattrafo F f)))"
        unfolding finite_subset_inclusion_functor_def apply (simp add: arr_Ff)
        unfolding finite_subset_image_nattrafo_def MkArr_def apply (simp add: arr_f)
        unfolding inclusion_map_def MkArr_def apply simp
        unfolding finite_subset_image_functor_def by (simp add: arr_f)
      show "fst (snd (the (finite_subset_inclusion_functor (snd (snd F))
                    (finite_subset_image_functor F f)))) =
    snd (snd (the (finite_subset_image_nattrafo F (Some (finiteSubsetCat.XId (fst (the f)))))))"
        unfolding finite_subset_inclusion_functor_def apply (simp add: arr_Ff)
        unfolding finite_subset_image_nattrafo_def MkArr_def apply (simp add: arr_id1)
        unfolding inclusion_map_def MkArr_def apply simp
        unfolding finite_subset_image_functor_def apply (simp add: arr_f)
        unfolding finiteSubsetCat.XId_def by simp
      fix x
      assume "x \<in> snd (fst (snd (the (finite_subset_image_nattrafo F
                                  (Some (finiteSubsetCat.XId (fst (the f))))))))"
      then have x_in_id_dom : "x \<in> snd (fst (finiteSubsetCat.XId (fst (the f))))"
        unfolding finite_subset_image_nattrafo_def MkArr_def by (simp add: arr_id1)
      then have x_in_f_dom : "x \<in> snd (fst (the f))"
        unfolding finiteSubsetCat.XId_def by simp
      have "fst (the f) = (fst (fst (the f)), snd (fst (the f)))" by simp
      have Fx_in_dom : "fst F x \<in> snd (fst (the (finite_subset_image_functor F f)))"
        unfolding finite_subset_image_functor_def apply (simp add: arr_f)
        apply (subst \<open>fst (the f) = (fst (fst (the f)), snd (fst (the f)))\<close>)
        apply (subst pointed_image.simps)
        by (simp add: x_in_f_dom)

      show "fst (the (finite_subset_inclusion_functor (snd (snd F)) (finite_subset_image_functor F f)))
          (fst (the (finite_subset_image_nattrafo F (Some (finiteSubsetCat.XId (fst (the f)))))) x) =
         fst (the (finite_subset_image_nattrafo F f)) x"
        unfolding finite_subset_image_nattrafo_def apply (simp add: arr_id1 arr_f)
        unfolding MkArr_def apply (simp add: x_in_id_dom x_in_f_dom)
        unfolding finite_subset_inclusion_functor_def apply (simp add: arr_Ff)
        unfolding inclusion_map_def MkArr_def by (simp add: Fx_in_dom)
    qed
    then show "Some
     (the (finite_subset_inclusion_functor (snd (snd F)) (finite_subset_image_functor F f)) \<cdot>
      the (finite_subset_image_nattrafo F (Some (finiteSubsetCat.XId (fst (the f)))))) =
    finite_subset_image_nattrafo F f"
      apply (subst EQ)
      unfolding finite_subset_image_nattrafo_def by (simp add: arr_f)
  qed

  have arr_id2: "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) (Some (finiteSubsetCat.XId (snd (the f))))"
      apply (rule_tac XId_arr)
    using pft 
    unfolding pointed_finset_triangle_def by simp
  have pf_id2: "pointed_finset (fst (snd F)) (snd (finiteSubsetCat.XId (snd (the f))))"
    unfolding finiteSubsetCat.XId_def
    apply simp
    using pft
    unfolding pointed_finset_triangle_def
    by simp
    

  show "pointed_set_comp
          (finite_subset_image_nattrafo F (partial_magma.cod (finiteSubsetCat.comp (fst (snd F))) f))
          (finite_subset_inclusion_functor (fst (snd F)) f) =
         finite_subset_image_nattrafo F f"
    unfolding finiteSubsetCat.cod_char
    apply (simp add: arr_f)
    apply (subst comp_char)
       apply (rule_tac finite_subset_inclusion_functor_arr [OF arr_f])
      apply (rule_tac finite_subset_image_nattrafo_arr [OF \<open>Arr' F\<close> arr_id2])
    unfolding finite_subset_image_nattrafo_dom [OF \<open>Arr' F\<close> arr_id2]
              finiteSubsetCat.dom_char
              finite_subset_inclusion_functor_cod [OF arr_f]
              finiteSubsetCat.cod_char
     apply (simp add: arr_id2 arr_f)
    unfolding finiteSubsetCat.XId_def apply simp
  proof-
    have arr_id2: "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) (Some (snd (the f), snd (the f)))"
      using arr_id2
      unfolding finiteSubsetCat.XId_def.

    have EQ: "the (finite_subset_image_nattrafo F (Some (snd (the f), snd (the f)))) \<cdot>
      the (finite_subset_inclusion_functor (fst (snd F)) f) =
         the (finite_subset_image_nattrafo F f)"
      apply (rule_tac comp_eq_char)
      using finite_subset_image_nattrafo_arr [OF \<open>Arr' F\<close> arr_id2]
      unfolding finiteSubsetCat.XId_def
                arr_char apply simp
      using finite_subset_inclusion_functor_arr [OF arr_f]
      unfolding arr_char apply simp
      using finite_subset_image_nattrafo_arr [OF \<open>Arr' F\<close> arr_f]
      unfolding arr_char apply simp
    proof-
      show "fst (snd (the (finite_subset_inclusion_functor (fst (snd F)) f))) =
    fst (snd (the (finite_subset_image_nattrafo F f)))"
        unfolding finite_subset_inclusion_functor_def apply (simp add: arr_f)
        unfolding finite_subset_image_nattrafo_def MkArr_def apply (simp add: arr_f)
        unfolding inclusion_map_def MkArr_def by simp
      show "snd (snd (the (finite_subset_image_nattrafo F (Some (snd (the f), snd (the f)))))) =
    snd (snd (the (finite_subset_image_nattrafo F f)))"
        unfolding finite_subset_image_nattrafo_def
                  MkArr_def by (simp add: arr_f arr_id2)
      show "fst (snd (the (finite_subset_image_nattrafo F (Some (snd (the f), snd (the f)))))) =
    snd (snd (the (finite_subset_inclusion_functor (fst (snd F)) f)))"
        unfolding finite_subset_image_nattrafo_def
                  MkArr_def apply (simp add: arr_id2)
        unfolding finite_subset_inclusion_functor_def apply (simp add: arr_f)
        unfolding inclusion_map_def MkArr_def by simp
      fix x
      assume "x \<in> snd (fst (snd (the (finite_subset_inclusion_functor (fst (snd F)) f))))"
      then have x_in_f_dom : "x \<in> snd (fst (the f))"
        unfolding finite_subset_inclusion_functor_def apply (simp add: arr_f)
        unfolding inclusion_map_def MkArr_def by simp 
      then have x_in_f_dom2 : "x \<in> snd (snd (the f))"
        using pft
        unfolding pointed_finset_triangle_def
        by auto
      show "fst (the (finite_subset_image_nattrafo F (Some (snd (the f), snd (the f)))))
          (fst (the (finite_subset_inclusion_functor (fst (snd F)) f)) x) =
         fst (the (finite_subset_image_nattrafo F f)) x"
        unfolding finite_subset_inclusion_functor_def apply (simp add: arr_f)
        unfolding inclusion_map_def MkArr_def apply (simp add: x_in_f_dom)
        unfolding finite_subset_image_nattrafo_def apply (simp add: arr_id2 arr_f)
        unfolding MkArr_def by (simp add: x_in_f_dom x_in_f_dom2)
    qed
    show "Some
     (the (finite_subset_image_nattrafo F (Some (snd (the f), snd (the f)))) \<cdot>
      the (finite_subset_inclusion_functor (fst (snd F)) f)) =
    finite_subset_image_nattrafo F f"
      apply (subst EQ)
      unfolding finite_subset_image_nattrafo_def by (simp add: arr_f)
  qed
qed

lemma finite_subset_image_nattrafo_id: 
  assumes ide_c : "partial_magma.ide pointed_set_comp c"
  shows "(finite_subset_image_nattrafo (the c)) = 
         finite_subset_inclusion_functor (Dom' (the c))"
proof
  from ide_c have "Arr' (the c)"
    unfolding ide_char by simp
  from ide_c have "c = Some (Id' (fst (snd (the c))))"
    unfolding ide_char by simp
  fix x
  have "partial_magma.arr (finiteSubsetCat.comp (fst (snd (the c)))) x \<Longrightarrow>
         the (finite_subset_image_nattrafo (the c) x) =
         the (finite_subset_inclusion_functor (fst (snd (the c))) x)"
    apply (rule_tac fun_eq_char)
    using finite_subset_image_nattrafo_arr [OF \<open>Arr' (the c)\<close>]
    unfolding arr_char apply simp
    using finite_subset_inclusion_functor_arr
    unfolding arr_char apply blast
  proof-
    assume arr_x : "partial_magma.arr (finiteSubsetCat.comp (fst (snd (the c)))) x"
    then have pft: "pointed_finset_triangle (fst (snd (the c))) (fst (the x)) (snd (the x))"
      unfolding finiteSubsetCat.arr_char
                finiteSubsetCat.XArr_def 
      by simp
    then have "fst (snd (the x)) \<in> snd (fst (snd (the c)))"
      unfolding pointed_finset_triangle_def
                pointed_finset_def
                Obj'_def
      by blast
                  

    show "fst (snd (the (finite_subset_image_nattrafo (the c) x))) =
    fst (snd (the (finite_subset_inclusion_functor (fst (snd (the c))) x)))"
      unfolding finite_subset_image_nattrafo_def
                finite_subset_inclusion_functor_def
      apply (simp add: arr_x)
      unfolding inclusion_map_def
                MkArr_def
      by simp
    show "snd (snd (the (finite_subset_image_nattrafo (the c) x))) =
    snd (snd (the (finite_subset_inclusion_functor (fst (snd (the c))) x)))" 
      unfolding finite_subset_image_nattrafo_def
                finite_subset_inclusion_functor_def
      apply (simp add: arr_x)
      unfolding inclusion_map_def
                MkArr_def
      apply simp
      apply (subst \<open>c = (Some (Id' (fst (snd (the c)))))\<close>)
      apply (subst pointed_image_simps)
      unfolding Id'_def
      apply (simp add: \<open>fst (snd (the x)) \<in> snd (fst (snd (the c)))\<close>)
    proof
      show "fst (fst (snd (the x)),
         snd (snd (the x)) \<inter> snd (fst (snd (the c))) \<union>
         (\<lambda>x. undefined) `
         (snd (snd (the x)) \<inter> {x. x \<notin> snd (fst (snd (the c)))})) =
    fst (snd (the x))"
        by simp
      show "snd (fst (snd (the x)),
         snd (snd (the x)) \<inter> snd (fst (snd (the c))) \<union>
         (\<lambda>x. undefined) `
         (snd (snd (the x)) \<inter> {x. x \<notin> snd (fst (snd (the c)))})) =
    snd (snd (the x))"
        apply simp
        using pft
        unfolding pointed_finset_triangle_def
                  pointed_finset_def
        by auto
    qed
    fix z
    assume "z \<in> snd (fst (snd (the (finite_subset_image_nattrafo (the c) x))))"
    then have z_in_dom_x: "z \<in> snd (fst (the x))"
      unfolding finite_subset_image_nattrafo_def
      apply (simp add: arr_x)
      unfolding MkArr_def
      by simp
    then have z_in_dom_c: "z \<in> snd (fst (snd (the c)))"
      using pft
      unfolding pointed_finset_triangle_def
                pointed_finset_def
      by auto
    show "fst (the (finite_subset_image_nattrafo (the c) x)) z =
          fst (the (finite_subset_inclusion_functor (fst (snd (the c))) x)) z"
      unfolding finite_subset_image_nattrafo_def 
                  finite_subset_inclusion_functor_def 
      apply (simp add: arr_x)
      unfolding inclusion_map_def MkArr_def
      apply (simp add: z_in_dom_x)
      apply (subst \<open>c = Some (Id' (fst (snd (the c))))\<close>)
      unfolding Id'_def
      by (simp add: z_in_dom_c)
  qed

  then show "finite_subset_image_nattrafo (the c) x =
         finite_subset_inclusion_functor (fst (snd (the c))) x "
    unfolding finite_subset_image_nattrafo_def
              finite_subset_inclusion_functor_def
    by auto
      
qed



lemma finite_subset_image_nattrafo_factors:
 assumes "Arr' F" 

shows "nat_trafo_factorization (finiteSubsetCat.comp (fst (snd F)))
     pointed_set_comp (finite_subset_inclusion_functor (fst (snd F)))
     (finite_subset_inclusion_functor (snd (snd F)) \<circ>
      finite_subset_image_functor F)
     (finite_subset_image_nattrafo F) FiniteArr'"
  unfolding nat_trafo_factorization_def
  apply safe
          apply (rule_tac finiteSubsetCat.is_category)
         apply (rule_tac is_category)
        apply (rule_tac finite_subcat)
       apply (rule_tac finite_subset_inclusion_functor_all_pointedsets)
      apply (rule_tac finite_subset_inclusion_functor_factors_finite_sets)
     apply (rule_tac factorization.comp_factorization)
      apply (rule_tac finite_subset_inclusion_functor_factors_finite_sets)
     apply (rule_tac finite_subset_image_functor [OF \<open>Arr' F\<close>])
    apply (rule_tac functor_comp)
     apply (rule_tac finite_subset_image_functor [OF \<open>Arr' F\<close>])
    apply (rule_tac finite_subset_inclusion_functor_all_pointedsets)
   apply (rule_tac finite_subset_image_nattrafo_all_pointedsets [OF \<open>Arr' F\<close>])
  unfolding nat_trafo_factorization_axioms_def
  apply safe
proof-
  fix a
  assume arr_a: "partial_magma.arr (finiteSubsetCat.comp (fst (snd F))) a"
  then have pft : "pointed_finset_triangle (fst (snd F)) (fst (the a)) (snd (the a))"
    unfolding finiteSubsetCat.arr_char
              finiteSubsetCat.XArr_def
    by simp
  have pf_image: "pointed_finset (snd (snd F)) (pointed_image (fst F) (snd (the a)))"
    apply (rule_tac pointed_finset_image [OF \<open>Arr' F\<close>])
    using pft
    unfolding pointed_finset_triangle_def by simp


  show "FiniteArr' (finite_subset_image_nattrafo F a)"
    unfolding FiniteArr'_def
    apply safe
  proof-
    show arr_Fa: "partial_magma.arr pointed_set_comp (finite_subset_image_nattrafo F a)"
      using finite_subset_image_nattrafo_arr [OF \<open>Arr' F\<close> arr_a] by simp
    show "finite (snd (fst (snd (the (finite_subset_image_nattrafo F a)))))"
      unfolding finite_subset_image_nattrafo_def
      apply (simp add: arr_a)
      unfolding MkArr_def
      apply simp
      using pft
      unfolding pointed_finset_triangle_def
                pointed_finset_def
      by simp
    show "finite (snd (snd (snd (the (finite_subset_image_nattrafo F a)))))"
      unfolding finite_subset_image_nattrafo_def
      apply (simp add: arr_a)
      unfolding MkArr_def
      apply simp
      using pf_image
      unfolding pointed_finset_def
      by simp
  qed
qed

lemma finite_subset_image_nattrafo:
 assumes "Arr' F" 
 shows "natural_transformation (finiteSubsetCat.comp (fst (snd F))) pointed_finite_subcat
  (finite_subset_inclusion_functor (fst (snd F)))
  (finite_subset_inclusion_functor (snd (snd F)) \<circ>
   finite_subset_image_functor F)
  (finite_subset_image_nattrafo F)"
  unfolding pointed_finite_subcat_def
  apply (rule_tac nat_trafo_factorization.is_natural_transformation)
  apply (rule_tac finite_subset_image_nattrafo_factors)
  using \<open>Arr' F\<close>.




interpretation S : category pointed_set_comp
  using is_category.

lemma functor_to_cat: "functor_to_cat pointed_set_comp
     (\<lambda>t. finiteSubsetCat.comp (Dom' (the t)))
     (\<lambda>t. finite_subset_image_functor (the t))"
  unfolding functor_to_cat_def
  apply (simp add: is_category)
  unfolding functor_to_cat_axioms_def
  apply safe
proof-
  fix c
  assume "S.arr c"
  then have "Arr' (the c)"
    unfolding pointed_set_comp_def
              classical_category.arr_char [OF ccpf]
    by simp
  show "functor (finiteSubsetCat.comp (fst (snd (the (S.dom c)))))
          (finiteSubsetCat.comp (fst (snd (the (S.cod c)))))
          (finite_subset_image_functor (the c))"
    using finite_subset_image_functor [OF \<open>Arr' (the c)\<close>]
    unfolding pointed_set_comp_def
    unfolding classical_category.dom_char [OF ccpf]
              classical_category.cod_char [OF ccpf]
    unfolding reverse_equality [OF pointed_set_comp_def]
    apply (simp add: \<open>S.arr c\<close>)
    unfolding Id'_def by simp
next
  fix c
  assume "S.ide c"
  then have "c = Some (Id' (fst (snd (the c))))"
    using ide_char by blast

  show "category (finiteSubsetCat.comp (fst (snd (the c))))"
    using finiteSubsetCat.is_category.
  then have "identity_functor (finiteSubsetCat.comp (fst (snd (the c))))"
    unfolding identity_functor_def.
  show "finite_subset_image_functor (the c) =
         identity_functor.map (finiteSubsetCat.comp (fst (snd (the c))))"
  proof
    fix x :: "(('b \<times> 'b set) \<times> 'b \<times> 'b set) option"
    have x_conv1: "fst (the x) = (fst (fst (the x)), snd (fst (the x)))" by simp
    have x_conv2: "snd (the x) = (fst (snd (the x)), snd (snd (the x)))" by simp
    show "finite_subset_image_functor (the c) x =
         identity_functor.map (finiteSubsetCat.comp (fst (snd (the c)))) x"
      unfolding finite_subset_image_functor_def
                identity_functor.map_def 
                [OF \<open>identity_functor (finiteSubsetCat.comp (fst (snd (the c))))\<close>]
      apply auto
    proof-
      assume "partial_magma.arr (finiteSubsetCat.comp (fst (snd (the c)))) x"
      then obtain t where t_def: "x = Some t \<and> finiteSubsetCat.XArr (fst (snd (the c))) (the x)"
        unfolding finiteSubsetCat.arr_char by auto
      then have subseteq: "snd (fst (the x)) \<subseteq> snd (fst (snd (the c))) \<and>
                           snd (snd (the x)) \<subseteq> snd (fst (snd (the c)))"
        unfolding finiteSubsetCat.XArr_def
                  pointed_finset_triangle_def
                  pointed_finset_def
        by blast

      from t_def have "x = Some t" by simp
      then have "t = the x" by simp

      have "fst (fst t) \<in> snd (fst (snd (the c)))"
        apply (subst \<open>t = the x\<close>)
        using t_def
        unfolding finiteSubsetCat.XArr_def
                  pointed_finset_triangle_def
                  pointed_finset_def
                  Obj'_def
        by blast
      have "fst (snd t) \<in> snd (fst (snd (the c)))"
        apply (subst \<open>t = the x\<close>)
        using t_def
        unfolding finiteSubsetCat.XArr_def
                  pointed_finset_triangle_def
                  pointed_finset_def
                  Obj'_def
        by blast

      have eq1: "fst (the c) ` snd (fst t) = snd (fst t)"
        apply (subst \<open>c = Some (Id' (fst (snd (the c))))\<close>)
        unfolding Id'_def 
        using subseteq t_def by auto
      have eq2: "fst (the c) ` snd (snd t) = snd (snd t)"
        apply (subst \<open>c = Some (Id' (fst (snd (the c))))\<close>)
        unfolding Id'_def
        using subseteq t_def by auto
      show "Some
     (pointed_image (fst (the c)) (fst (the x)),
      pointed_image (fst (the c)) (snd (the x))) =
      x"
        apply (rule_tac reverse_equality)
        apply (subst \<open>x = Some t\<close>)
        apply simp
        apply (subst x_conv1)
        apply (subst x_conv2)
        unfolding pointed_image.simps
                  \<open>x = Some t\<close>
        apply simp
        apply (subst eq1)
        apply (subst eq2)
        apply (subst \<open>c = Some (Id' (fst (snd (the c))))\<close>)
        unfolding Id'_def 
        apply (simp add: \<open>fst (fst t) \<in> snd (fst (snd (the c)))\<close>)
        apply (subst \<open>c = Some (Id' (fst (snd (the c))))\<close>)
        unfolding Id'_def
        by (simp add: \<open>fst (snd t) \<in> snd (fst (snd (the c)))\<close>)
    next
      have "fst (snd (the c)) = snd (snd (the c))"
        apply (rule_tac reverse_equality)
        apply (subst \<open>c = Some (Id' (fst (snd (the c))))\<close>)
        unfolding Id'_def by simp
      show "partial_magma.null (finiteSubsetCat.comp (snd (snd (the c)))) =
    partial_magma.null (finiteSubsetCat.comp (fst (snd (the c))))"
        apply (subst \<open>fst (snd (the c)) = snd (snd (the c))\<close>)
        by simp
    qed
  qed
next
  fix g f

  assume "S.seq g f"
  from \<open>S.seq g f\<close> have "S.arr f" by blast
  from \<open>S.seq g f\<close> have "S.arr g" by blast
  from \<open>S.seq g f\<close> have "S.dom g = S.cod f" by blast

  from \<open>S.arr f\<close> have "Arr' (the f)"
    unfolding arr_char by simp
  from \<open>S.arr g\<close> have "Arr' (the g)"
    unfolding arr_char by simp
  from \<open>S.dom g = S.cod f\<close> have "snd (snd (the f)) = fst (snd (the g))"
    unfolding dom_char [OF \<open>S.arr g\<close>]
              cod_char [OF \<open>S.arr f\<close>]
              Id'_def
    by simp

    


  have dom_gf : "fst (snd (the (pointed_set_comp g f))) = fst (snd (the f))"
    using S.dom_comp [OF \<open>S.seq g f\<close>]
    unfolding dom_char [OF \<open>S.arr f\<close>]
              dom_char [OF \<open>S.seq g f\<close>]
              Id'_def
    by simp
  have cod_gf : "snd (snd (the (pointed_set_comp g f))) = snd (snd (the g))"
    using S.cod_comp [OF \<open>S.seq g f\<close>]
    unfolding cod_char [OF \<open>S.arr g\<close>]
              cod_char [OF \<open>S.seq g f\<close>]
              Id'_def
    by simp

  have null_not_arr : "\<not> partial_magma.arr (finiteSubsetCat.comp (fst (snd (the g))))
      (partial_magma.null (finiteSubsetCat.comp (snd (snd (the f)))))"
    unfolding finiteSubsetCat.arr_char
    unfolding finiteSubsetCat.comp_def
    unfolding classical_category.null_char [OF finiteSubsetCat.is_classical_category]
    by simp


  show "finite_subset_image_functor (the (pointed_set_comp g f)) =
           finite_subset_image_functor (the g) \<circ>
           finite_subset_image_functor (the f)"
  proof
    fix x

    have "partial_magma.arr (finiteSubsetCat.comp (fst (snd (the f)))) x \<Longrightarrow>
         (Some
        (pointed_image (fst (the f)) (fst (the x)),
         pointed_image (fst (the f)) (snd (the x)))) =
          finite_subset_image_functor (the f) x"
      unfolding finite_subset_image_functor_def
      by simp

    then have arr_fx: "partial_magma.arr (finiteSubsetCat.comp (fst (snd (the f)))) x \<Longrightarrow>
          (partial_magma.arr (finiteSubsetCat.comp (fst (snd (the g))))
      (Some
        (pointed_image (fst (the f)) (fst (the x)),
         pointed_image (fst (the f)) (snd (the x)))))"
      apply simp
      using functor.preserves_arr [OF
            finite_subset_image_functor [OF \<open>Arr' (the f)\<close>]]
      unfolding \<open>snd (snd (the f)) = fst (snd (the g))\<close>
      by simp


    show "finite_subset_image_functor (the (pointed_set_comp g f)) x =
         (finite_subset_image_functor (the g) \<circ>
          finite_subset_image_functor (the f)) x"
      unfolding finite_subset_image_functor_def
      apply (simp add: dom_gf cod_gf null_not_arr arr_fx)
      apply safe
    proof-
      assume arr_x : "partial_magma.arr (finiteSubsetCat.comp (fst (snd (the f)))) x"
      then have x_prop: "(fst (fst (the x)) \<in> snd (fst (the x)) \<and>
   fst (fst (the x)) = fst (fst (snd (the f))) \<and>
   snd (fst (the x)) \<subseteq> snd (fst (snd (the f))) \<and> finite (snd (fst (the x)))) \<and>
  (fst (snd (the x)) \<in> snd (snd (the x)) \<and>
   fst (snd (the x)) = fst (fst (snd (the f))) \<and>
   snd (snd (the x)) \<subseteq> snd (fst (snd (the f))) \<and> finite (snd (snd (the x)))) \<and>
  snd (fst (the x)) \<subseteq> snd (snd (the x))"
        unfolding finiteSubsetCat.arr_char
                  finiteSubsetCat.XArr_def
                  pointed_finset_triangle_def
                  pointed_finset_def
                  Obj'_def
        by blast

      have x_conv : "(fst (the x)) = (fst (fst (the x)), snd (fst (the x)))" by simp

      show "
    pointed_image (fst (the (pointed_set_comp g f))) (fst (the x)) =
    pointed_image (fst (the g)) (pointed_image (fst (the f)) (fst (the x)))"
        unfolding comp_char [OF \<open>S.arr f\<close> \<open>S.arr g\<close> \<open>S.dom g = S.cod f\<close>]
        unfolding Comp'_def
        apply (simp add: \<open>Arr' (the f)\<close> \<open>Arr' (the g)\<close> \<open>snd (snd (the f)) = fst (snd (the g))\<close>)
        apply (subst x_conv)
        apply (subst pointed_image.simps)
        apply (rule_tac reverse_equality)
        apply (subst x_conv)
        apply (subst pointed_image.simps)
        using x_prop by auto

      have x_conv : "(snd (the x)) = (fst (snd (the x)), snd (snd (the x)))" by simp


      show "pointed_image (fst (the (pointed_set_comp g f))) (snd (the x)) =
    pointed_image (fst (the g)) (pointed_image (fst (the f)) (snd (the x)))"
        unfolding comp_char [OF \<open>S.arr f\<close> \<open>S.arr g\<close> \<open>S.dom g = S.cod f\<close>]
        unfolding Comp'_def
        apply (simp add: \<open>Arr' (the f)\<close> \<open>Arr' (the g)\<close> \<open>snd (snd (the f)) = fst (snd (the g))\<close>)
        apply (subst x_conv)
        apply (subst pointed_image.simps)
        apply (rule_tac reverse_equality)
        apply (subst x_conv)
        apply (subst pointed_image.simps)
        using x_prop by auto
    qed
  qed
qed

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


context begin


interpretation pointed_set.

interpretation C: category pointed_set_comp
  using is_category.

interpretation S: category pointed_finite_subcat
  using finite_subcat_is_category.


lemma functor_to_cat_overX:
     "functor_to_cat_overX pointed_set_comp pointed_finite_subcat
     (\<lambda>t. finiteSubsetCat.comp (fst (snd (the t))))
     (\<lambda>t. finite_subset_image_functor (the t))
     (\<lambda>t. finite_subset_image_nattrafo (the t))"
  unfolding functor_to_cat_overX_def
  apply safe
    apply (rule_tac functor_to_cat)
   apply (rule_tac S.category_axioms)
  unfolding functor_to_cat_overX_axioms_def
  apply safe
proof-
  fix c
  assume "C.ide c"
  then have "Arr' (the c)"
    unfolding C.ide_char
              arr_char
    by simp
  from \<open>C.ide c\<close> have "c = (Some (Id' (fst (snd (the c)))))"
    using ide_char by blast

  show "functor (finiteSubsetCat.comp (fst (snd (the c))))
          pointed_finite_subcat (finite_subset_image_nattrafo (the c))"
    apply (subst finite_subset_image_nattrafo_id [OF \<open>C.ide c\<close>])
    using finite_subset_inclusion_functor.
next
  fix c
  assume "C.arr c"
  then have "Arr' (the c)"
    unfolding arr_char by simp
  show "natural_transformation
          (finiteSubsetCat.comp (fst (snd (the (C.dom c)))))
          pointed_finite_subcat (finite_subset_image_nattrafo (the (C.dom c)))
          (finite_subset_image_nattrafo (the (C.cod c)) \<circ>
           finite_subset_image_functor (the c))
          (finite_subset_image_nattrafo (the c))"
    apply (subst finite_subset_image_nattrafo_id [OF C.ide_dom [OF \<open>C.arr c\<close>]])
    apply (subst finite_subset_image_nattrafo_id [OF C.ide_cod [OF \<open>C.arr c\<close>]])
    unfolding dom_char [OF \<open>C.arr c\<close>]
    unfolding cod_char [OF \<open>C.arr c\<close>]
    unfolding Id'_def apply simp
    using finite_subset_image_nattrafo [OF \<open>Arr' (the c)\<close>].
next
  fix g f
  assume arr_gf: "C.seq g f"
  from \<open>C.seq g f\<close> have "C.arr f" by blast
  then have "Arr' (the f)"
    unfolding arr_char by simp
  from \<open>C.seq g f\<close> have "C.arr g" by blast
  then have "Arr' (the g)"
    unfolding arr_char by simp
  from \<open>C.seq g f\<close> have "C.dom g = C.cod f" by blast
  then have seq: "snd (snd (the f)) = fst (snd (the g))"
    unfolding dom_char [OF \<open>C.arr g\<close>]
    unfolding cod_char [OF \<open>C.arr f\<close>]
    unfolding Id'_def
    by simp


  have hori_comp : "horizontal_composite (finiteSubsetCat.comp (fst (snd (the f)))) 
     (finiteSubsetCat.comp (snd (snd (the f)))) 
     pointed_finite_subcat (finite_subset_image_functor (the f))
     (finite_subset_image_functor (the f))
     (finite_subset_inclusion_functor (snd (snd (the f))))
     (finite_subset_inclusion_functor (snd (snd (the g))) \<circ>
      finite_subset_image_functor (the g))
     (finite_subset_image_functor (the f))
     (finite_subset_image_nattrafo (the g))"
    unfolding horizontal_composite_def
    apply safe
            apply (rule_tac finiteSubsetCat.is_category)
           apply (rule_tac finiteSubsetCat.is_category)
          apply (rule_tac finite_subcat_is_category)
         apply (rule_tac finite_subset_image_functor [OF \<open>Arr' (the f)\<close>])
        apply (rule_tac finite_subset_image_functor [OF \<open>Arr' (the f)\<close>])
       apply (rule_tac finite_subset_inclusion_functor)
      apply (rule_tac functor_comp)
       apply (subst seq)
       apply (rule_tac finite_subset_image_functor [OF \<open>Arr' (the g)\<close>])
      apply (rule_tac finite_subset_inclusion_functor)
     apply (rule_tac functor_is_transformation)
     apply (rule_tac finite_subset_image_functor [OF \<open>Arr' (the f)\<close>])
    unfolding seq
    by (rule_tac finite_subset_image_nattrafo [OF \<open>Arr' (the g)\<close>])

  have vert_comp : "vertical_composite (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
     pointed_finite_subcat 
     (finite_subset_inclusion_functor (Dom' (the f)))
     (finite_subset_inclusion_functor (Cod' (the f)) \<circ> 
      finite_subset_image_functor (the f))
     (finite_subset_inclusion_functor (Cod' (the g)) \<circ> 
      finite_subset_image_functor (the g) \<circ>
      finite_subset_image_functor (the f))
     (finite_subset_image_nattrafo (the f))
     (finite_subset_image_nattrafo (the g) \<circ>
      finite_subset_image_functor (the f))"
    unfolding dom_char [OF \<open>C.arr f\<close>]
              Id'_def
    apply simp
    unfolding vertical_composite_def
    apply safe
          apply (rule_tac finiteSubsetCat.is_category)
         apply (rule_tac finite_subcat_is_category)
        apply (rule_tac finite_subset_inclusion_functor)
       apply (rule_tac functor_comp)
        apply (rule_tac finite_subset_image_functor [OF \<open>Arr' (the f)\<close>])
       apply (rule_tac finite_subset_inclusion_functor)
      apply (rule_tac functor_comp)
       apply (rule_tac finite_subset_image_functor [OF \<open>Arr' (the f)\<close>])
      apply (rule_tac functor_comp)
       apply (subst seq)
       apply (rule_tac finite_subset_image_functor [OF \<open>Arr' (the g)\<close>])
      apply (rule_tac finite_subset_inclusion_functor)
     apply (rule_tac finite_subset_image_nattrafo [OF \<open>Arr' (the f)\<close>])
    apply (rule_tac horizontal_composite.is_natural_transformation)
    using hori_comp.


  show "finite_subset_image_nattrafo (the (pointed_set_comp g f)) =
           vertical_composite.map
            (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
            pointed_finite_subcat (finite_subset_image_nattrafo (the f))
            (finite_subset_image_nattrafo (the g) \<circ>
             finite_subset_image_functor (the f))"
  proof
    fix x
    show "finite_subset_image_nattrafo (the (pointed_set_comp g f)) x =
         vertical_composite.map
          (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
          pointed_finite_subcat (finite_subset_image_nattrafo (the f))
          (finite_subset_image_nattrafo (the g) \<circ>
           finite_subset_image_functor (the f)) x"
      unfolding vertical_composite.map_def [OF vert_comp]
      apply auto
    proof-
      have dom_eq1: "fst (snd (the (pointed_set_comp g f))) = fst (snd (the (C.dom f)))"
        using reverse_equality [OF C.dom_comp [OF arr_gf]]
        unfolding dom_char [OF arr_gf]
        apply simp
        unfolding Id'_def
        by simp
      have dom_eq2 : "fst (snd (the f)) = fst (snd (the (C.dom f)))"
        unfolding dom_char [OF \<open>C.arr f\<close>]
                  Id'_def by simp
      show "\<not> partial_magma.arr (finiteSubsetCat.comp (fst (snd (the (C.dom f))))) x \<Longrightarrow>
    finite_subset_image_nattrafo (the (pointed_set_comp g f)) x = S.null"
        unfolding finite_subset_image_nattrafo_def
        apply (subst dom_eq1)
        apply simp
        unfolding pointed_finite_subcat_def
        unfolding subcategory.null_char [OF finite_subcat]
        by simp
      assume arr_x : "partial_magma.arr (finiteSubsetCat.comp (fst (snd (the (C.dom f))))) x"
      have arr_fx : "partial_magma.arr (finiteSubsetCat.comp (fst (snd (the g))))
      (finite_subset_image_functor (the f)
        (partial_magma.cod (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
          x))"
        using functor.preserves_arr [OF 
              finite_subset_image_functor [OF \<open>Arr' (the f)\<close>]]
        unfolding dom_eq2 seq
        using category.arr_cod [OF finiteSubsetCat.is_category arr_x]
        by simp

      have comp_helper1 : "FiniteArr' (finite_subset_image_nattrafo (the f) x) \<and>
        FiniteArr'
         (finite_subset_image_nattrafo (the g)
           (finite_subset_image_functor (the f)
             (partial_magma.cod
               (finiteSubsetCat.comp (fst (snd (the (C.dom f))))) x))) \<and>
        C.seq
         (finite_subset_image_nattrafo (the g)
           (finite_subset_image_functor (the f)
             (partial_magma.cod
               (finiteSubsetCat.comp (fst (snd (the (C.dom f))))) x)))
         (finite_subset_image_nattrafo (the f) x)"
        apply safe
        apply (rule_tac nat_trafo_factorization.lands_in_subcat [OF 
              finite_subset_image_nattrafo_factors])
        using \<open>Arr' (the f)\<close> apply simp
        using arr_x dom_eq2 apply simp
        apply (rule_tac nat_trafo_factorization.lands_in_subcat [OF 
              finite_subset_image_nattrafo_factors])
        using \<open>Arr' (the g)\<close> apply simp
        using arr_fx apply simp
        apply (rule_tac C.seqI)
          apply (rule_tac finite_subset_image_nattrafo_arr [OF \<open>Arr' (the f)\<close>])
        using arr_x dom_eq2 apply simp
         apply (rule_tac finite_subset_image_nattrafo_arr [OF \<open>Arr' (the g)\<close>])
        using arr_fx apply simp
        apply (subst finite_subset_image_nattrafo_dom [OF \<open>Arr' (the g)\<close> arr_fx])
        apply (subst finite_subset_image_nattrafo_cod [OF \<open>Arr' (the f)\<close>])
        using arr_x dom_eq2 apply simp
        unfolding dom_eq2 reverse_equality [OF seq]
        apply (subst finite_subset_image_functor_dom [OF \<open>Arr' (the f)\<close>])
        using category.arr_cod [OF finiteSubsetCat.is_category arr_x]
        unfolding dom_eq2 apply simp
        apply (subst category.ideD(2) [OF finiteSubsetCat.is_category])
        using category.ide_cod [OF finiteSubsetCat.is_category arr_x] apply simp
        by simp


      show "finite_subset_image_nattrafo (the (pointed_set_comp g f)) x =
    pointed_finite_subcat
     (finite_subset_image_nattrafo (the g)
       (finite_subset_image_functor (the f)
         (partial_magma.cod (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
           x)))
     (finite_subset_image_nattrafo (the f) x)"
        unfolding pointed_finite_subcat_def
        apply (subst subcategory.comp_char [OF finite_subcat])
        unfolding subcategory.arr_char [OF finite_subcat]
        apply (simp add: comp_helper1)
        apply (rule_tac reverse_equality)
        apply (subst comp_char)
      proof-
        show arr_if: "C.arr (finite_subset_image_nattrafo (the f) x)"
           apply (rule_tac finite_subset_image_nattrafo_arr [OF \<open>Arr' (the f)\<close>])
          using arr_x dom_eq2 by simp
        show arr_ig: "C.arr
     (finite_subset_image_nattrafo (the g)
       (finite_subset_image_functor (the f)
         (partial_magma.cod (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
           x)))"
          apply (rule_tac finite_subset_image_nattrafo_arr [OF \<open>Arr' (the g)\<close>])
        unfolding reverse_equality [OF seq]
          apply (rule_tac finite_subset_image_functor_arr [OF \<open>Arr' (the f)\<close>])
        using category.ide_cod [OF finiteSubsetCat.is_category arr_x]
        unfolding dom_eq2 category.ide_char [OF finiteSubsetCat.is_category]
        by simp
      show "C.dom
     (finite_subset_image_nattrafo (the g)
       (finite_subset_image_functor (the f)
         (partial_magma.cod (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
           x))) =
    C.cod (finite_subset_image_nattrafo (the f) x)"
        apply (subst finite_subset_image_nattrafo_dom [OF \<open>Arr' (the g)\<close> arr_fx])
        apply (subst finite_subset_image_nattrafo_cod [OF \<open>Arr' (the f)\<close>])
        using arr_x dom_eq2 apply simp
        unfolding dom_eq2 reverse_equality [OF seq]
        apply (subst finite_subset_image_functor_dom [OF \<open>Arr' (the f)\<close>])
        using category.arr_cod [OF finiteSubsetCat.is_category arr_x]
        unfolding dom_eq2 apply simp
        apply (subst category.ideD(2) [OF finiteSubsetCat.is_category])
        using category.ide_cod [OF finiteSubsetCat.is_category arr_x] apply simp
        by simp

      have arr_igf : "C.arr (finite_subset_image_nattrafo (the (pointed_set_comp g f)) x)" 
        apply (rule_tac finite_subset_image_nattrafo_arr)
        using arr_gf
        unfolding arr_char apply simp
        using dom_eq1 arr_x
        by simp

        have EQ: "the (finite_subset_image_nattrafo (the (pointed_set_comp g f)) x) =
     (the (finite_subset_image_nattrafo (the g)
            (finite_subset_image_functor (the f)
              (partial_magma.cod
                (finiteSubsetCat.comp (fst (snd (the (C.dom f))))) x))) \<cdot>
      the (finite_subset_image_nattrafo (the f) x))"
          apply (rule_tac reverse_equality)
          apply (rule_tac comp_eq_char)
          using arr_ig
          unfolding arr_char apply simp
          using arr_if
          unfolding arr_char apply simp
          using arr_igf
          unfolding arr_char apply simp
        proof-
          show "fst (snd (the (finite_subset_image_nattrafo (the f) x))) =
    fst (snd (the (finite_subset_image_nattrafo (the (pointed_set_comp g f))
                    x)))"
            apply (subst comp_char [OF \<open>C.arr f\<close> \<open>C.arr g\<close> \<open>C.dom g = C.cod f\<close>])
            unfolding Comp'_def
            apply (simp add: \<open>Arr' (the f)\<close> \<open>Arr' (the g)\<close> seq)
            unfolding finite_subset_image_nattrafo_def apply (simp add: arr_x dom_eq2)
            unfolding MkArr_def by simp
          have arr_cod_x : "partial_magma.arr (finiteSubsetCat.comp (fst (snd (the f))))
     (partial_magma.cod (finiteSubsetCat.comp (fst (snd (the (C.dom f))))) x)"
            using category.ide_cod [OF finiteSubsetCat.is_category arr_x]
            unfolding dom_eq2
                      category.ide_char [OF finiteSubsetCat.is_category]
            by simp
          have arr_f_cod_x : "(partial_magma.arr (finiteSubsetCat.comp (fst (snd (the g))))
      (finite_subset_image_functor (the f)
        (partial_magma.cod (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
          x)))"
            unfolding reverse_equality [OF seq]
            apply (rule_tac finite_subset_image_functor_arr [OF \<open>Arr' (the f)\<close>])
            using category.ide_cod [OF finiteSubsetCat.is_category arr_x]
            unfolding dom_eq2
                      category.ide_char [OF finiteSubsetCat.is_category]
            by simp

          have cod_eq1: "snd (snd (the (pointed_set_comp g f))) = snd (snd (the g))"
            using C.cod_comp [OF arr_gf]
            unfolding cod_char [OF arr_gf]
                      cod_char [OF \<open>C.arr g\<close>]
                      Id'_def
            by simp

          have "C.cod (finite_subset_image_nattrafo (the g)
                    (finite_subset_image_functor (the f)
                      (partial_magma.cod
                        (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
                        x))) =
    C.cod (finite_subset_image_nattrafo (the (pointed_set_comp g f))
                    x)"
            apply (subst finite_subset_image_nattrafo_cod [OF \<open>Arr' (the g)\<close>])
            using arr_f_cod_x apply simp
            apply (subst reverse_equality [OF seq])
            apply (subst finite_subset_image_functor_cod [OF \<open>Arr' (the f)\<close>])
            using arr_cod_x apply simp
            apply (subst dom_eq2)
            apply (subst category.ideD(3) [OF finiteSubsetCat.is_category
                  category.ide_cod [OF finiteSubsetCat.is_category]])
            using arr_x apply simp
            apply (subst finite_subset_image_nattrafo_cod)
            using arr_gf
            unfolding arr_char apply simp
            using dom_eq1 arr_x apply simp
            apply (subst functor_to_cat.Ffun_comp [OF functor_to_cat arr_gf])
            using dom_eq1 cod_eq1 by simp
            

          then show "snd (snd (the (finite_subset_image_nattrafo (the g)
                    (finite_subset_image_functor (the f)
                      (partial_magma.cod
                        (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
                        x))))) =
    snd (snd (the (finite_subset_image_nattrafo (the (pointed_set_comp g f))
                    x)))"
            unfolding cod_char [OF arr_ig]
                      cod_char [OF arr_igf]
                      Id'_def
            by simp
          have "C.dom (finite_subset_image_nattrafo (the g)
                    (finite_subset_image_functor (the f)
                      (partial_magma.cod
                        (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
                        x))) = C.cod (finite_subset_image_nattrafo (the f) x)"
            apply (subst finite_subset_image_nattrafo_dom [OF \<open>Arr' (the g)\<close>])
            using arr_f_cod_x apply simp
            unfolding reverse_equality [OF seq]
            apply (subst finite_subset_image_functor_dom [OF \<open>Arr' (the f)\<close>])
            using arr_cod_x apply simp
            unfolding dom_eq2
            apply (subst category.ideD(2) [OF finiteSubsetCat.is_category
                  category.ide_cod [OF finiteSubsetCat.is_category]])
            using arr_x apply simp
            apply (subst finite_subset_image_nattrafo_cod [OF \<open>Arr' (the f)\<close>])
            using arr_x dom_eq2 apply simp
            using dom_eq2 by simp

          then show "fst (snd (the (finite_subset_image_nattrafo (the g)
                    (finite_subset_image_functor (the f)
                      (partial_magma.cod
                        (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
                        x))))) =
    snd (snd (the (finite_subset_image_nattrafo (the f) x)))"
            unfolding dom_char [OF arr_ig]
                      cod_char [OF arr_if]
                      Id'_def
            by simp
          fix z
          assume "z \<in> snd (fst (snd (the (finite_subset_image_nattrafo (the f)
                                    x))))"
          then have z_in_dom : "z \<in> snd (fst (the x))"
            unfolding finite_subset_image_nattrafo_def
            apply (simp add: arr_x dom_eq2)
            unfolding MkArr_def by simp
          then have z_in_snd_x : "z \<in> snd (snd (the x))"
            using arr_x
            unfolding reverse_equality [OF dom_eq2]
                      finiteSubsetCat.arr_char
                      finiteSubsetCat.XArr_def
                      pointed_finset_triangle_def
            by auto
          then have z_in_f_dom : "z \<in> snd (fst (snd (the f)))"
            using arr_x
            unfolding reverse_equality [OF dom_eq2]
                      finiteSubsetCat.arr_char
                      finiteSubsetCat.XArr_def
                      pointed_finset_triangle_def
                      pointed_finset_def
            by auto

          have f_z_in_dom : "fst (the f) z
     \<in> snd (fst (the (finite_subset_image_functor (the f)
                        (partial_magma.cod
                          (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
                          x))))"
            unfolding finiteSubsetCat.cod_char
            apply (simp add: arr_x)
            apply (subst reverse_equality [OF finite_subset_image_functor_id])
               apply (simp add: \<open>Arr' (the f)\<close>)
            using arr_x dom_eq2 apply simp
            using arr_x
            unfolding reverse_equality [OF dom_eq2]
                      finiteSubsetCat.arr_char
                      finiteSubsetCat.XArr_def
                      pointed_finset_triangle_def
             apply simp
            unfolding finiteSubsetCat.XId_def
            apply (simp add: pointed_image_simps)
            using z_in_snd_x by simp

          show "fst (the (finite_subset_image_nattrafo (the g)
                     (finite_subset_image_functor (the f)
                       (partial_magma.cod
                         (finiteSubsetCat.comp (fst (snd (the (C.dom f)))))
                         x))))
           (fst (the (finite_subset_image_nattrafo (the f) x)) z) =
          fst (the (finite_subset_image_nattrafo (the (pointed_set_comp g f))
                     x))
           z"
            unfolding finite_subset_image_nattrafo_def
            apply (simp add: arr_x dom_eq2 dom_eq1 arr_f_cod_x)
            unfolding MkArr_def
            apply (simp add: z_in_dom f_z_in_dom)
            apply (subst comp_char)
               apply (simp_all add: \<open>C.arr f\<close> \<open>C.arr g\<close> \<open>C.dom g = C.cod f\<close>)
            unfolding Comp'_def
            by (simp add: \<open>Arr' (the f)\<close> \<open>Arr' (the g)\<close> seq z_in_f_dom)
        qed
        show "Some
     (the (finite_subset_image_nattrafo (the g)
            (finite_subset_image_functor (the f)
              (partial_magma.cod
                (finiteSubsetCat.comp (fst (snd (the (C.dom f))))) x))) \<cdot>
      the (finite_subset_image_nattrafo (the f) x)) =
    finite_subset_image_nattrafo (the (pointed_set_comp g f)) x"
          apply (subst reverse_equality [OF EQ])
          unfolding finite_subset_image_nattrafo_def 
          by (simp add: arr_x dom_eq1)
      qed
    qed
  qed
qed



end



locale finsubset_colimit =
  F : "functor" "finiteSubsetCat.comp X" pointed_set.pointed_set_comp F
  for X :: "'a pointed_set.LC pointed_set"
  and F :: "('a pointed_set.LC pointed_set \<times> 'a pointed_set.LC pointed_set) option 
             \<Rightarrow> 'a pointed_set.LC pointed_set.parr option" +
assumes obj_X: "pointed_set.Obj' X"
begin

interpretation pointed_set.



definition A_some where
  "A_some = (\<lambda>t. Dom' (the (F (Some (t, t) ))))"
 
definition F_some where
  "F_some = (\<lambda>t s. the (F (Some (t, s))))"

definition \<sigma>_some where
  "\<sigma>_some \<sigma> = (\<lambda>S. (if pointed_finset X S 
                    then the (\<sigma> (Some (S, S)))
                    else (F_some S S)))"

lemma A_some_\<sigma>_some :
  assumes pf_eq: "(\<forall>S. pointed_finset X S \<longrightarrow> A_some S = Dom' (\<sigma>_some \<sigma> S))" 
  shows "A_some = (\<lambda>k. Dom' (\<sigma>_some \<sigma> k))"
proof
  fix k
  show "A_some k = fst (snd (\<sigma>_some \<sigma> k))"
    unfolding A_some_def \<sigma>_some_def F_some_def
    apply simp
  proof
    assume "pointed_finset X k"
    then have "A_some k = Dom' (\<sigma>_some \<sigma> k)"
      using pf_eq by blast
    then show "fst (snd (the (F (Some (k, k))))) = fst (snd (the (\<sigma> (Some (k, k)))))"
      unfolding A_some_def \<sigma>_some_def F_some_def
      by (simp add: \<open>pointed_finset X k\<close>)
  qed
qed
    




definition colimit_obj where
  "colimit_obj = (Some (Id' (colimitOverFinsets X 
                     A_some F_some)))"

definition colimit_cocone where
  "colimit_cocone = MkFunctor (finiteSubsetCat.comp X) 
                      pointed_set_comp
                     (\<lambda>t. Some (colim_finset_inclusion X 
                     A_some F_some
                      (fst (the t)) ))"

definition colimit_UP_map where
  "colimit_UP_map = (\<lambda>x \<sigma>. Some (colim_finset_UP_map X 
                        (\<sigma>_some \<sigma>) F_some
                        (Dom' (the x))))"


lemma cocone_obj_some :
 shows "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A_some S)"
  unfolding A_some_def
  apply (rule_tac allI)
proof
  fix S
  assume "pointed_finset X S"
  have "partial_magma.arr (finiteSubsetCat.comp X) (Some (S, S))"
    unfolding finiteSubsetCat.arr_char
    apply simp
    unfolding finiteSubsetCat.XArr_def
              pointed_finset_triangle_def
    by (simp add: \<open>pointed_finset X S\<close>)
  then have "F.B.arr (F (Some (S, S)))"
    using functor.preserves_arr [OF F.functor_axioms]
    by simp
  then have arr: "Arr' (the (F (Some (S, S))))"
    unfolding arr_char by simp
  show "Obj' (fst (snd (the (F (Some (S, S))))))"
    using classical_category.Obj_Dom [OF ccpf arr].
qed


lemma arr_f_to_pf1 :
  assumes arr_f: "F.A.arr f"
  shows "pointed_finset X (fst (the f))"
  using arr_f
  unfolding finiteSubsetCat.arr_char
            finiteSubsetCat.XArr_def
            pointed_finset_triangle_def
  by simp

lemma colimit_cocone_arr : 
  assumes arr_f : "F.A.arr f"
  shows "F.B.arr (colimit_cocone f)"
  unfolding arr_char
            colimit_cocone_def
  apply (simp add: arr_f)
  apply (rule_tac colim_finset_inclusion_arr [OF cocone_obj_some])
  using arr_f_to_pf1 [OF arr_f].


lemma constant_functor_map_simps :
  assumes arr_f : "F.A.arr f"
  shows "constant_functor.map (finiteSubsetCat.comp X) pointed_set_comp colimit_obj f = 
         colimit_obj"
  apply (subst constant_functor.map_def)
  unfolding constant_functor_def
              constant_functor_axioms_def
   apply (simp add: F.A.category_axioms F.B.category_axioms)
  unfolding colimit_obj_def ide_char
   apply simp
   apply (rule_tac conjI)
    apply (rule_tac classical_category.Arr_Id [OF ccpf])
  using colimitOverFinsets_obj [OF cocone_obj_some obj_X] apply simp
   apply (simp add: Id'_def)
  apply (simp add: F.A.ide_cod [OF arr_f])
  unfolding cod_char [OF colimit_cocone_arr [OF arr_f]]
  unfolding colimit_cocone_def
  by (simp add: arr_f)


lemma cocone_nat_dom :
  assumes arr_f : "F.A.arr f"
  shows "F.B.dom (colimit_cocone f) = F (F.A.dom f)"
proof-
have arr_dom_f : "F.A.arr (Some (fst (the f), fst (the f)))"
    unfolding finiteSubsetCat.arr_char
    apply simp
    unfolding finiteSubsetCat.XArr_def
              pointed_finset_triangle_def
    apply simp
    using arr_f_to_pf1 [OF arr_f].


  have dom_eq1: "F.B.dom (F (Some (fst (the f), fst (the f)))) = F.B.dom (F f)"
    unfolding F.preserves_dom [OF arr_f]
              F.preserves_dom [OF arr_dom_f]
    unfolding finiteSubsetCat.dom_char
    by (simp add: arr_f arr_dom_f)

  have dom_eq2: "fst (snd (the (colimit_cocone f))) = fst (snd (the (F f)))" 
    unfolding colimit_cocone_def
    apply (simp add: arr_f)
    unfolding colim_finset_inclusion_dom [OF cocone_obj_some arr_f_to_pf1 [OF arr_f]]
    unfolding A_some_def
    using dom_eq1
    unfolding dom_char [OF F.preserves_arr [OF arr_f]]
              dom_char [OF F.preserves_arr [OF arr_dom_f]]
    unfolding Id'_def
    by simp
  show "F.B.dom (colimit_cocone f) = F (F.A.dom f)"
    unfolding dom_char [OF colimit_cocone_arr [OF arr_f]]
    apply (subst reverse_equality [OF F.preserves_dom [OF arr_f]])
    unfolding dom_char [OF F.preserves_arr [OF arr_f]]
    using dom_eq2 by simp
qed

lemma cocone_nat_cod :
  assumes arr_f : "F.A.arr f"
  shows "F.B.cod (colimit_cocone f) = colimit_obj"
  unfolding cod_char [OF colimit_cocone_arr [OF arr_f]]
  unfolding colimit_cocone_def colimit_obj_def
  apply (simp add: arr_f)
  using colim_finset_inclusion_cod [OF cocone_obj_some arr_f_to_pf1 [OF arr_f]]
  by simp

lemma cocone_nat :
    shows "natural_transformation (finiteSubsetCat.comp X) pointed_set_comp F
     (constant_functor.map (finiteSubsetCat.comp X) pointed_set_comp
       colimit_obj) colimit_cocone"
  unfolding natural_transformation_def
  apply safe
      apply (rule_tac finiteSubsetCat.is_category)
     apply (rule_tac is_category)
    apply (rule_tac F.functor_axioms)
   apply (rule_tac constant_functor.is_functor)
   apply (subst constant_functor_def)
   apply (simp add: finiteSubsetCat.is_category is_category)
  unfolding constant_functor_axioms_def
   apply (subst colimit_obj_def)
   apply (subst ide_char)
   apply auto
    apply (rule_tac classical_category.Arr_Id [OF ccpf])
    apply (rule_tac colimitOverFinsets_obj 
           [OF cocone_obj_some])
  using obj_X apply simp
  unfolding Id'_def apply simp
  unfolding natural_transformation_axioms_def
  apply safe
proof-
  fix f
  show "\<not> F.A.arr f \<Longrightarrow> colimit_cocone f = F.B.null"
    unfolding colimit_cocone_def by simp
  assume arr_f: "F.A.arr f"

  show "F.B.dom (colimit_cocone f) = F (F.A.dom f)"
    using cocone_nat_dom arr_f by simp
  

  show "F.B.cod (colimit_cocone f) = constant_functor.map (finiteSubsetCat.comp X) pointed_set_comp colimit_obj (F.A.cod f)"
    apply (subst constant_functor_map_simps)
     apply (simp add: F.A.ide_cod [OF arr_f])
    using cocone_nat_cod [OF arr_f].

  have ide_colimit_obj : "F.B.ide colimit_obj"
    unfolding ide_char colimit_obj_def
    apply auto
     apply (rule_tac classical_category.Arr_Id [OF ccpf])
    using colimitOverFinsets_obj [OF cocone_obj_some obj_X] apply simp
    by (simp add: Id'_def)

  have ide_const :"F.B.ide (constant_functor.map (finiteSubsetCat.comp X) pointed_set_comp colimit_obj f)"
    apply (subst constant_functor_map_simps [OF arr_f])
    using ide_colimit_obj.

  show "pointed_set_comp (constant_functor.map (finiteSubsetCat.comp X) pointed_set_comp colimit_obj f) (colimit_cocone (F.A.dom f)) =
         colimit_cocone f"
    apply (subst F.B.comp_ide_arr [OF ide_const])
    unfolding constant_functor_map_simps [OF arr_f]
  proof-
    show "F.B.seq colimit_obj (colimit_cocone (F.A.dom f))"
      apply (rule_tac F.B.seqI)
        apply (rule_tac colimit_cocone_arr 
               [OF F.A.ideD(1) [OF F.A.ide_dom [OF arr_f]]])
      using ide_colimit_obj apply simp
      unfolding dom_char [OF F.B.ideD(1) [OF ide_colimit_obj]]
      unfolding cod_char [OF colimit_cocone_arr 
                      [OF F.A.ideD(1) [OF F.A.ide_dom [OF arr_f]]]]
      unfolding colimit_obj_def colimit_cocone_def
      apply (simp add: F.A.ide_dom [OF arr_f])
      apply (subst colim_finset_inclusion_cod [OF cocone_obj_some arr_f_to_pf1])
       apply (simp add: F.A.ide_dom [OF arr_f])
      by (simp add: Id'_def)
    show "colimit_cocone (F.A.dom f) = colimit_cocone f"
      unfolding colimit_cocone_def
      apply (simp add: arr_f)
      unfolding finiteSubsetCat.dom_char
      apply (simp add: arr_f)
      unfolding finiteSubsetCat.XId_def
      by simp
  qed

  have arr_cod : "F.A.arr (F.A.cod f)"
    using F.A.ide_cod [OF arr_f] by simp


  show "pointed_set_comp (colimit_cocone (F.A.cod f)) (F f) = colimit_cocone f"
    apply (rule_tac comp_eq_char2)
  proof-
    show "F.B.seq (colimit_cocone (F.A.cod f)) (F f)"
      apply (rule_tac F.B.seqI)
        apply (rule_tac F.preserves_arr [OF arr_f])
       apply (rule_tac colimit_cocone_arr [OF arr_cod])
      apply (subst cocone_nat_dom [OF arr_cod])
      unfolding F.A.dom_cod [OF arr_f]
      using F.preserves_cod [OF arr_f] by simp
    show "F.B.arr (colimit_cocone f)"
      using colimit_cocone_arr [OF arr_f].
    show "F.B.dom (F f) = F.B.dom (colimit_cocone f)"
      unfolding cocone_nat_dom [OF arr_f]
      using F.preserves_dom [OF arr_f] by simp
    show "F.B.cod (colimit_cocone (F.A.cod f)) = F.B.cod (colimit_cocone f)"
      unfolding cocone_nat_cod [OF arr_f]
            cocone_nat_cod [OF arr_cod]
      by simp
    fix x
    assume x_in_Ff: "x \<in> snd (fst (snd (the (F f))))"
    assume x_in_cc : "x \<in> snd (fst (snd (the (colimit_cocone f))))"
    assume fx_in_dom : "fst (the (F f)) x
         \<in> snd (fst (snd (the (colimit_cocone (F.A.cod f)))))"

    from x_in_Ff have "x \<in> snd (Dom' (the (F.B.dom (F f))))"
      unfolding dom_char [OF F.preserves_arr [OF arr_f]]
      unfolding Id'_def 
      by simp
    then have x_in_A: "x \<in> snd (A_some (fst (the f)))"
      unfolding A_some_def
      unfolding F.preserves_dom [OF arr_f]
      unfolding finiteSubsetCat.dom_char
      apply (simp add: arr_f)
      unfolding finiteSubsetCat.XId_def
      by simp



    define R where "R = (colimit_relation X A_some F_some)"
    define inc :: "(('a LC \<times> 'a LC set) \<times> 'a LC \<times> 'a LC set) option \<Rightarrow> 
                   'a LC parr" 
      where "inc = (\<lambda>x. cop_finset_inclusion X A_some (fst (the x)))"
    have inc_cod: "cop_finset_inclusion X A_some (fst (the (F.A.cod f))) =
          inc (F.A.cod f)"
      unfolding inc_def by simp
    have inc_f : "cop_finset_inclusion X A_some (fst (the f)) =
          inc f"
      unfolding inc_def by simp


    have pf_cod : "pointed_finset X (fst (the (F.A.cod f)))"
      using arr_cod
      unfolding finiteSubsetCat.arr_char
                finiteSubsetCat.XArr_def
                pointed_finset_triangle_def
      by simp

    term "(colim_finset_inclusion X A_some F_some
                       (fst (the (F.A.cod f))))"

    show "fst (the (colimit_cocone (F.A.cod f))) (fst (the (F f)) x) =
         fst (the (colimit_cocone f)) x"
      using fx_in_dom
      unfolding colimit_cocone_def
      apply (simp add: arr_cod arr_f)
      apply (subst colim_finset_inclusion_fst [OF cocone_obj_some pf_cod])
      unfolding colim_finset_inclusion_dom [OF cocone_obj_some pf_cod]
      unfolding cop_finset_inclusion_dom [OF cocone_obj_some pf_cod]
       apply simp
    proof-
      show "fst (quotient_proj (coproductOverFinsets X A_some)
          (colimit_relation X A_some F_some))
     (fst (cop_finset_inclusion X A_some (fst (the (F.A.cod f))))
       (fst (the (F f)) x)) =
    fst (colim_finset_inclusion X A_some F_some (fst (the f))) x"
        apply (subst colim_finset_inclusion_fst [OF cocone_obj_some 
                     arr_f_to_pf1 [OF arr_f]])
        using x_in_cc
        unfolding colimit_cocone_def
         apply (simp add: arr_f)
        unfolding colim_finset_inclusion_dom [OF cocone_obj_some 
                         arr_f_to_pf1 [OF arr_f]]
        unfolding cop_finset_inclusion_dom [OF cocone_obj_some
                          arr_f_to_pf1 [OF arr_f]]
         apply simp
        apply (rule_tac R_implies_quot_eq)
           apply (rule_tac colimit_relation_equiv)
      proof-
        show "colimit_relation X A_some F_some
     (fst (cop_finset_inclusion X A_some (fst (the (F.A.cod f))))
       (fst (the (F f)) x))
     (fst (cop_finset_inclusion X A_some (fst (the f))) x)"
          unfolding colimit_relation_def
                    generated_equiv_rel_def
          apply auto
        proof-
          fix Q
          assume Q_equiv : "equiv (snd (coproductOverFinsets X A_some)) {(x, y). Q x y}"
          then have sym_rule : "\<And>x y. Q x y \<Longrightarrow> Q y x"
            using Q_equiv unfolding equiv_def sym_def by simp
          assume RQ: "\<forall>x y. colimit_prerelation X A_some F_some x y \<longrightarrow> Q x y"
          then have RQ_rule : "\<And>x y. colimit_prerelation X A_some F_some x y \<Longrightarrow> Q x y" by simp
          show "Q (fst (cop_finset_inclusion X A_some (fst (the (F.A.cod f))))
             (fst (the (F f)) x))
          (fst (cop_finset_inclusion X A_some (fst (the f))) x)"
            apply (rule_tac sym_rule)
            apply (rule_tac RQ_rule)
            unfolding colimit_prerelation_def
            apply (rule_tac exI)
            apply (rule_tac exI)
            apply (rule_tac exI)
            apply (rule_tac exI)
            apply auto
          proof-
            show "pointed_finset_triangle X (fst (the f)) (fst (the (F.A.cod f)))"
              unfolding finiteSubsetCat.cod_char
              using arr_f apply simp
              unfolding finiteSubsetCat.arr_char
              unfolding finiteSubsetCat.XArr_def
              unfolding finiteSubsetCat.XId_def
              by simp

            show "x \<in> snd (A_some (fst (the f)))"
              using x_in_A.
            have dom_eq: "Some (finiteSubsetCat.XId (fst (the (F.A.cod f)))) =
                  F.A.dom (F.A.cod f)"
              unfolding finiteSubsetCat.dom_char
              by (simp add: arr_cod)
            show "fst (the (F f)) x \<in> snd (A_some (fst (the (F.A.cod f))))"
              using fx_in_dom
              unfolding colimit_cocone_def
              apply (simp add: arr_cod)
              unfolding colim_finset_inclusion_dom 
                        [OF cocone_obj_some pf_cod]
              by simp
            show "fst (F_some (fst (the f)) (fst (the (F.A.cod f)))) x = fst (the (F f)) x"
              unfolding F_some_def
              unfolding finiteSubsetCat.cod_char
              apply (simp add: arr_f)
              unfolding finiteSubsetCat.XId_def
              apply simp
              using arr_f
              unfolding finiteSubsetCat.arr_char
              by simp
          qed
        qed
        show "\<forall>S. pointed_finset X S \<longrightarrow> Obj' (A_some S)"
          using cocone_obj_some.

        have "(fst (the (F f)) x)
    \<in> snd (Dom' (cop_finset_inclusion X A_some (fst (the (F.A.cod f)))))"
          using fx_in_dom
          unfolding colimit_cocone_def
          apply (simp add: arr_f)
          unfolding colim_finset_inclusion_dom [OF cocone_obj_some pf_cod]
          unfolding cop_finset_inclusion_dom [OF cocone_obj_some pf_cod]
          by simp

        then have "fst (cop_finset_inclusion X A_some (fst (the (F.A.cod f))))
     (fst (the (F f)) x)
    \<in> snd (Cod' (cop_finset_inclusion X A_some (fst (the (F.A.cod f)))))"
          using cop_finset_inclusion_arr [OF cocone_obj_some pf_cod]
          unfolding Arr'_def setcat.Arr_def
          by auto

        then show "fst (cop_finset_inclusion X A_some (fst (the (F.A.cod f))))
     (fst (the (F f)) x)
    \<in> snd (coproductOverFinsets X A_some)"
          using cop_finset_inclusion_cod [OF cocone_obj_some pf_cod]
          by simp

        have "x \<in> snd (Dom' (cop_finset_inclusion X A_some (fst (the f))))"
          unfolding cop_finset_inclusion_dom [OF cocone_obj_some
                arr_f_to_pf1 [OF arr_f]]
          using x_in_A.
          
        then show "fst (cop_finset_inclusion X A_some (fst (the f))) x
    \<in> snd (coproductOverFinsets X A_some)"
          unfolding reverse_equality [OF 
                cop_finset_inclusion_cod [OF cocone_obj_some
                arr_f_to_pf1 [OF arr_f]]]
          using cop_finset_inclusion_arr [OF cocone_obj_some
                 arr_f_to_pf1 [OF arr_f]]
          unfolding Arr'_def setcat.Arr_def
          by auto
      qed
    qed
  qed
qed








lemma colimit_existence : 
    shows "colimit (finiteSubsetCat.comp X) pointed_set_comp F
           colimit_cocone colimit_obj colimit_UP_map"
  unfolding colimit_def
  using cocone_nat
  unfolding natural_transformation_def
  apply simp
proof-
  show "colimit_axioms (finiteSubsetCat.comp X) pointed_set_comp F colimit_cocone
     colimit_obj colimit_UP_map"
    unfolding colimit_axioms_def
    apply safe
  proof-
    show "F.B.ide colimit_obj"
      unfolding ide_char
      unfolding colimit_obj_def
      apply auto
       apply (rule_tac classical_category.Arr_Id [OF ccpf])
      using colimitOverFinsets_obj [OF cocone_obj_some obj_X] apply simp
      by (simp add: Id'_def)
    show "cocone (finiteSubsetCat.comp X) pointed_set_comp F colimit_obj
     colimit_cocone"
      unfolding cocone_def
      using cocone_nat.
    fix \<sigma> x
    assume cocone: "cocone (finiteSubsetCat.comp X) pointed_set_comp F x \<sigma>"
    then have \<sigma>nat : "natural_transformation (finiteSubsetCat.comp X) pointed_set_comp F
   (constant_functor.map (finiteSubsetCat.comp X) pointed_set_comp x) \<sigma>"
      unfolding cocone_def.
    assume "F.B.ide x"

    have cocone_obj : "\<forall>S. pointed_finset X S \<longrightarrow>
        Arr' (\<sigma>_some \<sigma> S) \<and>
        fst (snd (\<sigma>_some \<sigma> S)) = A_some S \<and>
        snd (snd (\<sigma>_some \<sigma> S)) = fst (snd (the x))"
      apply auto
    proof-
      fix s S
      assume pf_s: "pointed_finset X (s, S)"
      have arr_s: "F.A.arr (Some ((s, S), s, S))"
        unfolding finiteSubsetCat.arr_char
                  finiteSubsetCat.XArr_def
                  pointed_finset_triangle_def
        by (simp add: \<open>pointed_finset X (s, S)\<close>)

      have arr_\<sigma>s:"F.B.arr (\<sigma> (Some ((s, S), s, S)))"
        unfolding natural_transformation.preserves_reflects_arr [OF \<sigma>nat]
        using arr_s.

      then show "Arr' (\<sigma>_some \<sigma> (s, S))"
        unfolding \<sigma>_some_def
                  arr_char
        by (simp add: pf_s)
  
      have "F.B.dom (\<sigma> ((Some ((s, S), s, S)))) = F (F.A.dom (Some ((s, S), s, S)))"
        using natural_transformation.preserves_dom [OF \<sigma>nat arr_s].
      then show "fst (snd (\<sigma>_some \<sigma> (s, S))) = A_some (s, S)"
        unfolding dom_char [OF arr_\<sigma>s]
        unfolding reverse_equality [OF F.preserves_dom [OF arr_s]]
        unfolding dom_char [OF F.preserves_arr [OF arr_s]]
        unfolding A_some_def
                  \<sigma>_some_def
        by (simp add: Id'_def pf_s)


      have "x = Some (Id' (fst (snd (the x))))"
        using \<open>F.B.ide x\<close>
        unfolding ide_char by simp

      have "constant_functor.map (finiteSubsetCat.comp X) pointed_set_comp x
   (F.A.cod (Some ((s, S), s, S))) = x"
        apply (subst constant_functor.map_def)
        unfolding constant_functor_def
                  constant_functor_axioms_def
         apply (simp add: F.A.category_axioms F.B.category_axioms \<open>F.B.ide x\<close>)
        by (simp add: F.A.ide_cod [OF arr_s])
      then have "F.B.cod (\<sigma> (Some ((s, S), s, S))) = Some (Id' (fst (snd (the x))))"
        apply (subst reverse_equality [OF \<open>x = Some (Id' (fst (snd (the x))))\<close>])
        using natural_transformation.preserves_cod [OF \<sigma>nat arr_s]
        by simp
      then show "snd (snd (\<sigma>_some \<sigma> (s, S))) = fst (snd (the x))"
        unfolding cod_char [OF arr_\<sigma>s] \<sigma>_some_def
        using \<open>F.B.ide x\<close>
        by (simp add: Id'_def pf_s)
    qed
    then have cocone_obj' : 
           "\<forall>S. pointed_finset X S \<longrightarrow>
           Arr' (\<sigma>_some \<sigma> S) \<and>
           snd (snd (\<sigma>_some \<sigma> S)) = fst (snd (the x)) "
      by simp

    have cocone_arr : "\<forall>S T. pointed_finset_triangle X S T 
                   \<longrightarrow> \<sigma>_some \<sigma> T \<cdot> F_some S T = \<sigma>_some \<sigma> S"
      apply auto
    proof-
      fix s S t T
      assume pft : "pointed_finset_triangle X (s, S) (t, T)"
      then have pf_s : "pointed_finset X (s, S)"
        unfolding pointed_finset_triangle_def by simp
      from pft have pf_t : "pointed_finset X (t, T)"
        unfolding pointed_finset_triangle_def by simp
      have arr_st: "F.A.arr (Some ((s, S), t, T))"
        unfolding finiteSubsetCat.arr_char
                  finiteSubsetCat.XArr_def
        by (simp add: pft)
      have arr_cod : "F.A.arr (F.A.cod (Some ((s, S), t, T)))"
        using F.A.ideD(1) [OF F.A.ide_cod [OF arr_st]].

      have x_cod: "F.B.cod (\<sigma> (F.A.dom (Some ((s, S), t, T)))) = x" 
        unfolding natural_transformation.preserves_cod [OF \<sigma>nat
                      F.A.ideD(1) [OF F.A.ide_dom [OF arr_st]]]
         apply (subst constant_functor.map_def)
        unfolding constant_functor_def
                  constant_functor_axioms_def
          apply (simp add: F.A.category_axioms F.B.category_axioms \<open>F.B.ide x\<close>)
         apply (subst F.A.cod_dom [OF arr_st])
         by (simp add: F.A.ideD(1) [OF F.A.ide_dom [OF arr_st]])

      have \<sigma>eq1: "\<sigma>_some \<sigma> (s, S) = the (\<sigma> (Some ((s, S), t, T)))"
        unfolding \<sigma>_some_def
        apply (simp add: pf_s)
        unfolding reverse_equality [OF 
              natural_transformation.is_natural_1 [OF \<sigma>nat arr_st]]
        apply (subst constant_functor.map_def)
        unfolding constant_functor_def
                  constant_functor_axioms_def
         apply (simp add: F.A.category_axioms F.B.category_axioms \<open>F.B.ide x\<close>)
        apply (simp add: arr_st)
        apply (subst F.B.comp_cod_arr)
        unfolding natural_transformation.preserves_reflects_arr [OF \<sigma>nat]
        using F.A.ide_dom [OF arr_st] apply simp
        using x_cod apply simp
        unfolding finiteSubsetCat.dom_char
        apply (simp add: arr_st)
        unfolding finiteSubsetCat.XId_def
        by simp

      have comp_char2: "pointed_set_comp (\<sigma> (F.A.cod (Some ((s, S), t, T))))
            (F (Some ((s, S), t, T))) = 
             Some (\<sigma>_some \<sigma> (t, T) \<cdot> F_some (s, S) (t, T))"
        apply (subst comp_char)
           apply (rule_tac F.preserves_arr [OF arr_st])
          apply (subst natural_transformation.preserves_reflects_arr [OF \<sigma>nat])
          apply (rule_tac arr_cod)
        unfolding natural_transformation.preserves_dom [OF \<sigma>nat arr_cod]
        unfolding F.A.dom_cod [OF arr_st]
        using F.preserves_cod [OF arr_st] apply simp
        unfolding \<sigma>_some_def F_some_def
        apply (simp add: pf_t)
        unfolding finiteSubsetCat.cod_char
        apply (simp add: arr_st)
        unfolding finiteSubsetCat.XId_def
        by simp


      show "\<sigma>_some \<sigma> (t, T) \<cdot> F_some (s, S) (t, T) = \<sigma>_some \<sigma> (s, S)"
        apply (subst \<sigma>eq1)
        using reverse_equality [OF
              natural_transformation.is_natural_2 [OF \<sigma>nat arr_st]]
        unfolding comp_char2
        unfolding \<sigma>_some_def
        by simp
    qed

    have A\<sigma> : "\<forall>S. pointed_finset X S \<longrightarrow> A_some S = fst (snd (\<sigma>_some \<sigma> S))"
      unfolding A_some_def \<sigma>_some_def
      apply auto
    proof-
      fix s S
      assume "pointed_finset X (s, S)"
      then have arr_s : "F.A.arr (Some ((s, S), (s, S)))"
        unfolding finiteSubsetCat.arr_char
                  finiteSubsetCat.XArr_def
                  pointed_finset_triangle_def
        by simp
      have arr_\<sigma>s: "F.B.arr (\<sigma> (Some ((s, S), s, S)))"
        unfolding natural_transformation.preserves_reflects_arr [OF \<sigma>nat]
        using arr_s.
      have "F.B.dom (F (Some ((s, S), s, S))) =
            F.B.dom (\<sigma> (Some ((s, S), s, S)))"
        unfolding natural_transformation.preserves_dom [OF \<sigma>nat arr_s]
        using F.preserves_dom [OF arr_s].
      then show "fst (snd (the (F (Some ((s, S), s, S))))) =
           fst (snd (the (\<sigma> (Some ((s, S), s, S)))))"
        unfolding dom_char [OF F.preserves_arr [OF arr_s]]
        unfolding dom_char [OF arr_\<sigma>s]
        by (simp add: Id'_def)
    qed

    have fac: "finset_arrow_collection X (\<lambda>k. fst (snd (\<sigma>_some \<sigma> k))) F_some"
      unfolding finset_arrow_collection_def
      apply auto
    proof-
      fix s S t T
      assume pft : "pointed_finset_triangle X (s, S) (t, T)"
      then have arr_st: "F.A.arr (Some ((s, S), (t, T)))"
        unfolding finiteSubsetCat.arr_char
                  finiteSubsetCat.XArr_def
        by simp
      then have "F.B.arr (F (Some ((s, S), t, T)))"
        using F.preserves_arr by simp
      then show "Arr' (F_some (s, S) (t, T))"
        unfolding F_some_def
        using arr_char by blast
      from pft have pf_s :" pointed_finset X (s, S)"
        unfolding pointed_finset_triangle_def
        by simp
      then have arr_s: "F.A.arr (Some ((s, S), s, S))"
        unfolding finiteSubsetCat.arr_char
                  finiteSubsetCat.XArr_def
        unfolding pointed_finset_triangle_def
        by simp
      from pft have pf_t :" pointed_finset X (t, T)"
        unfolding pointed_finset_triangle_def
        by simp
      then have arr_t: "F.A.arr (Some ((t, T), t, T))"
        unfolding finiteSubsetCat.arr_char
                  finiteSubsetCat.XArr_def
        unfolding pointed_finset_triangle_def
        by simp

      have arr_\<sigma>s: "F.B.arr (\<sigma> (Some ((s, S), s, S)))"
        unfolding natural_transformation.preserves_reflects_arr [OF \<sigma>nat]
        using arr_s.

      have arr_\<sigma>t: "F.B.arr (\<sigma> (Some ((t, T), t, T)))"
        unfolding natural_transformation.preserves_reflects_arr [OF \<sigma>nat]
        using arr_t.

      have "F.B.dom (F (Some ((s, S), t, T))) =
            F.B.dom (\<sigma> (Some ((s, S), s, S)))"
        unfolding natural_transformation.preserves_dom [OF \<sigma>nat arr_s]
        unfolding F.preserves_dom [OF arr_st]
        unfolding finiteSubsetCat.dom_char
        by (simp add: arr_st arr_s)
        
      then show "fst (snd (F_some (s, S) (t, T))) = fst (snd (\<sigma>_some \<sigma> (s, S)))"
        unfolding F_some_def \<sigma>_some_def
        apply (simp add: pf_s)
        unfolding dom_char [OF F.preserves_arr [OF arr_st]]
        unfolding dom_char [OF arr_\<sigma>s]
        by (simp add: Id'_def)

      have "F.B.cod (F (Some ((s, S), t, T))) =
            F.B.dom (\<sigma> (Some ((t, T), t, T)))"
        unfolding natural_transformation.preserves_dom [OF \<sigma>nat arr_t]
        unfolding F.preserves_cod [OF arr_st]
        unfolding finiteSubsetCat.cod_char
                  finiteSubsetCat.dom_char
        by (simp add: arr_st arr_t)

      then show "snd (snd (F_some (s, S) (t, T))) = fst (snd (\<sigma>_some \<sigma> (t, T)))"
        unfolding F_some_def \<sigma>_some_def
        apply (simp add: pf_t)
        unfolding cod_char [OF F.preserves_arr [OF arr_st]]
        unfolding dom_char [OF arr_\<sigma>t]
        by (simp add: Id'_def)
    qed

    have UP_ex : "Arr' (colim_finset_UP_map X (\<sigma>_some \<sigma>) F_some (fst (snd (the x)))) \<and>
  fst (snd (colim_finset_UP_map X (\<sigma>_some \<sigma>) F_some (fst (snd (the x))))) =
  colimitOverFinsets X (\<lambda>k. fst (snd (\<sigma>_some \<sigma> k))) F_some \<and>
  snd (snd (colim_finset_UP_map X (\<sigma>_some \<sigma>) F_some (fst (snd (the x))))) =
  fst (snd (the x)) \<and>
  (\<forall>S. pointed_finset X S \<longrightarrow>
       colim_finset_UP_map X (\<sigma>_some \<sigma>) F_some (fst (snd (the x))) \<cdot>
       colim_finset_inclusion X (\<lambda>k. fst (snd (\<sigma>_some \<sigma> k))) F_some S =
       \<sigma>_some \<sigma> S)"
      apply (rule_tac colim_finset_UP_existence)
      using cocone_obj' apply simp
      using cocone_arr apply simp
      using fac apply simp
      using obj_X apply simp
      apply (rule_tac classical_category.Obj_Dom [OF ccpf])
      using \<open>F.B.ide x\<close>
      unfolding ide_char
      by simp

    show "F.B.in_hom (colimit_UP_map x \<sigma>) colimit_obj x"
      apply (rule_tac F.B.in_homI)
    proof-
      show arr_up: "F.B.arr (colimit_UP_map x \<sigma>)"
        unfolding colimit_UP_map_def
        unfolding arr_char
        using UP_ex by simp
      show "F.B.dom (colimit_UP_map x \<sigma>) = colimit_obj"
        unfolding dom_char [OF arr_up]
        unfolding colimit_UP_map_def
                  colimit_obj_def
        apply (subst A_some_\<sigma>_some [OF A\<sigma>])
        using UP_ex by simp
      show "F.B.cod (colimit_UP_map x \<sigma>) = x"
        unfolding cod_char [OF arr_up]
        unfolding colimit_UP_map_def
        apply (simp add: UP_ex)
        using \<open>F.B.ide x\<close>
        unfolding ide_char
        by simp
    qed
    show "\<And>c. F.A.ide c \<Longrightarrow>
       \<sigma> c = pointed_set_comp (colimit_UP_map x \<sigma>) (colimit_cocone c)"
    proof-
      fix c
      assume "F.A.ide c"
      define S where "S = fst (the c)"
      have "pointed_finset X S"
        using F.A.ideD(1) [OF \<open>F.A.ide c\<close>]
        unfolding finiteSubsetCat.arr_char
                  finiteSubsetCat.XArr_def
                  pointed_finset_triangle_def
                  S_def
        by simp
      then have EQ: "colim_finset_UP_map X (\<sigma>_some \<sigma>) F_some (fst (snd (the x))) \<cdot>
       colim_finset_inclusion X A_some F_some S =
       \<sigma>_some \<sigma> S"
        unfolding A_some_\<sigma>_some [OF A\<sigma>]
        using UP_ex by blast

      show "\<sigma> c = pointed_set_comp (colimit_UP_map x \<sigma>) (colimit_cocone c)"
        unfolding colimit_UP_map_def colimit_cocone_def
        apply (simp add: \<open>F.A.ide c\<close>)
        apply (subst comp_char)
      proof-
        show arr1: "F.B.arr (Some (colim_finset_inclusion X A_some F_some (fst (the c))))"
          unfolding arr_char
                    reverse_equality [OF S_def]
          using colim_finset_inclusion_arr [OF cocone_obj_some \<open>pointed_finset X S\<close>]
          by simp
        show arr2: "F.B.arr
     (Some (colim_finset_UP_map X (\<sigma>_some \<sigma>) F_some (fst (snd (the x)))))"
          unfolding arr_char
          apply simp
          apply (rule_tac colim_finset_UP_map_arr [OF cocone_obj obj_X])
          apply (rule_tac classical_category.Obj_Dom [OF ccpf])
          using F.B.ideD(1) [OF \<open>F.B.ide x\<close>]
          using arr_char by blast
        show "F.B.dom
     (Some (colim_finset_UP_map X (\<sigma>_some \<sigma>) F_some (fst (snd (the x))))) =
    F.B.cod (Some (colim_finset_inclusion X A_some F_some (fst (the c))))"
          unfolding cod_char [OF arr1]
          unfolding dom_char [OF arr2]
          unfolding reverse_equality [OF S_def]
          apply simp
          apply (subst colim_finset_inclusion_cod 
                [OF cocone_obj_some \<open>pointed_finset X S\<close>])
          apply (subst A_some_\<sigma>_some [OF A\<sigma>])
          using UP_ex by simp
        show "\<sigma> c = Some
     (the (Some (colim_finset_UP_map X (\<sigma>_some \<sigma>) F_some (fst (snd (the x))))) \<cdot>
      the (Some (colim_finset_inclusion X A_some F_some (fst (the c)))))"
          unfolding reverse_equality [OF S_def]
          apply (simp add: EQ)
          unfolding \<sigma>_some_def
          apply (simp add: \<open>pointed_finset X S\<close>)
        proof-
          have "c = (Some (S, S))"
            unfolding S_def
            using \<open>F.A.ide c\<close>
            using classical_category.ide_char [OF finiteSubsetCat.is_classical_category]
            unfolding finiteSubsetCat.comp_def
                      finiteSubsetCat.XId_def
            by blast
          have "F.B.arr (\<sigma> c)"
            unfolding natural_transformation.preserves_reflects_arr [OF \<sigma>nat]
            using F.A.ideD(1) \<open>F.A.ide c\<close> by blast
          then have "\<sigma> c = Some (the (\<sigma> c))"
            unfolding arr_char by simp
          then show "\<sigma> c = Some (the (\<sigma> (Some (S, S))))"
            using \<open>c = (Some (S, S))\<close> by simp
        qed
      qed
    qed

    fix f
    assume f_in_hom: "F.B.in_hom f colimit_obj x"
    have arr_f: "F.B.arr f"
      using F.B.in_homE [OF f_in_hom] by auto

    assume f_prop: "\<forall>c. F.A.ide c 
     \<longrightarrow> \<sigma> c = pointed_set_comp f (colimit_cocone c)"

    have the_eq: "(the f) = the (colimit_UP_map x \<sigma>)"
      unfolding colimit_UP_map_def
      apply simp
      apply (rule_tac colim_finset_UP_uniqueness 
             [OF cocone_obj' cocone_arr fac])
      using obj_X apply simp
      apply (rule_tac classical_category.Obj_Dom [OF ccpf])
      using \<open>F.B.ide x\<close>
      unfolding ide_char
       apply simp
      apply auto
    proof-
      from arr_f show "Arr' (the f)"
        unfolding arr_char by simp
      have "F.B.dom f = colimit_obj"
        using F.B.in_homE [OF f_in_hom] by auto
      then show "fst (snd (the f)) =
    colimitOverFinsets X (\<lambda>k. fst (snd (\<sigma>_some \<sigma> k))) F_some"
        unfolding colimit_obj_def
        unfolding A_some_\<sigma>_some [OF A\<sigma>]
        unfolding dom_char [OF arr_f]
        by (simp add: Id'_def)
      have "F.B.cod f = x"
        using F.B.in_homE [OF f_in_hom] by auto
      then have "F.B.cod f = Some (Id' (Dom' (the x)))"
        using \<open>F.B.ide x\<close>
        unfolding ide_char by simp
      then show "snd (snd (the f)) = fst (snd (the x))"
        unfolding cod_char [OF arr_f]
        by (simp add: Id'_def)
      fix s S
      assume "pointed_finset X (s, S)"
      define c where "c = Some ((s, S), s, S)"
      have "F.A.ide c"
        unfolding finiteSubsetCat.comp_def
        unfolding classical_category.ide_char 
              [OF finiteSubsetCat.is_classical_category]
        unfolding finiteSubsetCat.XArr_def
                  finiteSubsetCat.XId_def
                  pointed_finset_triangle_def
        unfolding c_def
        by (simp add: \<open>pointed_finset X (s, S)\<close>)
      then have EQ: "\<sigma> c = pointed_set_comp f (colimit_cocone c)"
        using f_prop by simp
      have "F.B.seq f (colimit_cocone c)"
        apply (subst reverse_equality [OF EQ])
        unfolding natural_transformation.preserves_reflects_arr [OF \<sigma>nat]
        using \<open>F.A.ide c\<close> by simp
      have "the (pointed_set_comp f (colimit_cocone c)) = 
            the f \<cdot> the (colimit_cocone c)"
        apply (subst comp_char)
        using \<open>F.B.seq f (colimit_cocone c)\<close> apply blast
        using \<open>F.B.seq f (colimit_cocone c)\<close> apply blast
        using \<open>F.B.seq f (colimit_cocone c)\<close> apply blast
        by simp
      then have "the (pointed_set_comp f
          (colimit_cocone c)) =
    the f \<cdot> colim_finset_inclusion X A_some F_some (fst (the c))"
        unfolding colimit_cocone_def
        by (simp add: \<open>F.A.ide c\<close>)
      then have comp_char: "the (pointed_set_comp f
          (colimit_cocone c)) =
    the f \<cdot> colim_finset_inclusion X A_some F_some (s, S)"
        unfolding c_def by simp

      show "the f \<cdot>
           colim_finset_inclusion X (\<lambda>k. fst (snd (\<sigma>_some \<sigma> k))) F_some
            (s, S) =
           \<sigma>_some \<sigma> (s, S)"
        unfolding reverse_equality [OF A_some_\<sigma>_some [OF A\<sigma>]]
        unfolding reverse_equality [OF comp_char]
        unfolding reverse_equality [OF EQ]
        unfolding \<sigma>_some_def
        apply (simp add: \<open>pointed_finset X (s, S)\<close>)
        unfolding c_def
        by simp
    qed
    show "f = colimit_UP_map x \<sigma>"
      using reverse_equality [OF the_eq]
      unfolding colimit_UP_map_def
      apply simp
      using arr_f
      unfolding arr_char
      by simp
  qed
qed
      



end




locale gammaset_as_endofunctor =
  M : "functor" pointed_fin_set.comp pointed_set.pointed_set_comp M
  for
  M :: "gamma \<Rightarrow> 's pointed_set.LC pointed_set.parr option"
begin

interpretation pointed_set.


definition I where
  "I = inclusion_inverse"

definition MIFunctor where
  "MIFunctor t = (M \<circ> I) \<circ> (finite_subset_image_nattrafo (the t))"

interpretation S : category pointed_set_comp
  using is_category.

interpretation FTCOX : functor_to_cat_overX pointed_set_comp pointed_finite_subcat
   "(\<lambda>t. finiteSubsetCat.comp (fst (snd (the t))))"
   "(\<lambda>t. finite_subset_image_functor (the t))"
   "(\<lambda>t. finite_subset_image_nattrafo (the t))"
  using functor_to_cat_overX.


interpretation Colimit_Functoriality: 
       colimit_functoriality
       pointed_set_comp
       pointed_set_comp
       "(\<lambda>t. finiteSubsetCat.comp (Dom' (the t)))"
       "(\<lambda>t. finite_subset_image_functor (the t))"
       MIFunctor
       "(\<lambda>t. finsubset_colimit.colimit_obj (Dom' (the t)) (MIFunctor t))"
       "(\<lambda>t. finsubset_colimit.colimit_cocone (Dom' (the t)) (MIFunctor t))"
       "(\<lambda>t. finsubset_colimit.colimit_UP_map (Dom' (the t)) (MIFunctor t))"
  unfolding colimit_functoriality_def MIFunctor_def
  apply safe
   apply (rule_tac functor_to_cat_overX.extend_by_functor)
  using functor_to_cat_overX apply simp
   apply (rule_tac functor_comp)
    apply (subst I_def)
  using finset_equivalence
  unfolding equivalence_of_categories_def
    apply blast
  using M.functor_axioms apply simp
  unfolding colimit_functoriality_axioms_def
  apply safe
  apply (rule_tac finsubset_colimit.colimit_existence)
  unfolding finsubset_colimit_def
              finsubset_colimit_axioms_def
  apply safe
proof-
  fix c :: "'a LC parr option"
  assume "S.ide c"
  show "functor (finiteSubsetCat.comp (fst (snd (the c)))) pointed_set_comp
          (M \<circ> I \<circ> finite_subset_image_nattrafo (the c))"
    apply (rule_tac functor_comp)
    using FTCOX.\<tau>fun [OF \<open>S.ide c\<close>] apply simp
    apply (rule_tac functor_comp)
    unfolding I_def
  using finset_equivalence
  unfolding equivalence_of_categories_def
    apply blast
  using M.functor_axioms.
  show "Obj' (fst (snd (the c)))"
    apply (rule_tac classical_category.Obj_Dom [OF ccpf])
    using \<open>S.ide c\<close>
    unfolding ide_char arr_char by simp
qed


definition map where
  "map = Colimit_Functoriality.colim_functor"

lemma is_functor: "functor pointed_set_comp pointed_set_comp map"
  unfolding map_def
  using Colimit_Functoriality.is_functor.


end

end
