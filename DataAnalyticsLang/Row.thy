theory Row imports HOLCF "HOLCF-extra.Distributive" Subdomain
begin
default_sort type
class two = assumes exTwo: "\<exists>x y :: 'a. x \<noteq> y"
begin

lemma obtain_neq: obtains y :: 'a where "x \<noteq> y"
proof -
  from exTwo obtain a b :: 'a where "a \<noteq> b" by blast
  consider "x = a" | "x \<noteq> a" by fast
  then show thesis apply cases using \<open>a \<noteq> b\<close> that by simp_all
qed

end

pcpodef ('a::type, 'b) tuple = "UNIV :: ('a \<Rightarrow> 'b::pcpo) set"
  morphisms "tget" "Abs_tuple"
  by simp_all

lemma Abs_tuple_inverse': "tget (Abs_tuple t) = t" using Abs_tuple_inverse by simp

definition "ctget \<equiv> \<Lambda> t a. tget t (undiscr a)"

lemma ctget_beta: "ctget\<cdot>t\<cdot>a = tget t (undiscr a)"
  unfolding ctget_def
  by (simp add: cont2cont_fun cont_tget)

definition "ctabs \<equiv> \<Lambda> f. Abs_tuple (\<lambda>a. f\<cdot>(Discr a))"

lemma ctabs_beta: "ctabs\<cdot>f = Abs_tuple (\<lambda>a. f\<cdot>(Discr a))"
  unfolding ctabs_def
  by (simp add: cont_apply cont_Abs_tuple )

lemma ctabs_ctget_inverse[simp]: "ctabs\<cdot>(ctget\<cdot>t) = t"
  by (simp add: ctabs_beta ctget_beta tget_inverse)

lemma ctget_ctabs_inverse[simp]: "ctget\<cdot>(ctabs\<cdot>t) = t"
  by (intro cfun_eqI) (simp add: ctget_beta ctabs_beta Abs_tuple_inverse')

lemma approx_chain_tuple:
"approx_chain a \<Longrightarrow> approx_chain (\<lambda>i. ctabs oo (a i) oo ctget)"
  by (simp add: approx_chain_iso)

instance tuple :: (countable, bifinite) bifinite
proof
  show "\<exists>a::nat\<Rightarrow>('a, 'b) tuple\<rightarrow>('a, 'b) tuple. approx_chain a"
    using approx_chain_tuple bifinite by blast
qed

instantiation tuple :: (countable, "domain") "domain"
begin
definition
  "emb = emb oo ctget"
definition
  "prj = ctabs oo prj"
definition
  "defl (t :: ('a, 'b) tuple itself) = DEFL('a discr \<rightarrow> 'b)"
definition
  "(liftemb :: ('a, 'b) tuple u \<rightarrow> udom u) = u_map\<cdot>emb"
definition
  "(liftprj :: udom u \<rightarrow> ('a, 'b) tuple u) = u_map\<cdot>prj"
definition
  "liftdefl (t :: ('a, 'b) tuple itself) = liftdefl_of\<cdot>(DEFL(('a, 'b) tuple))"

instance proof
  have "ep_pair ctget ctabs" by standard simp_all
  then show "ep_pair emb (prj :: udom \<rightarrow> ('a, 'b) tuple)"
    unfolding emb_tuple_def prj_tuple_def
    by (intro ep_pair_comp ep_pair_emb_prj)
  show "cast\<cdot>DEFL(('a, 'b) tuple) = emb oo (prj :: udom \<rightarrow> ('a, 'b) tuple)"
    unfolding emb_tuple_def prj_tuple_def defl_tuple_def
    by (simp add: cast_DEFL cfcomp1)
qed (fact liftemb_tuple_def liftprj_tuple_def liftdefl_tuple_def)+

end

notation
  tget (\<open>(\<open>notation=\<open>infix tget\<close>\<close>_\<langle>_\<rangle>)\<close> [999, 0] 999)

definition tupd :: "'a \<Rightarrow> ('a, 'b::pcpo) tuple \<rightarrow> 'b \<rightarrow> ('a, 'b) tuple" where
"tupd a \<equiv> \<Lambda> t b. Abs_tuple ((tget t)(a := b))"

lemma tupd_beta: "tupd a\<cdot>t\<cdot>b = Abs_tuple ((tget t)(a := b))"
  unfolding tupd_def
  by (simp add: cont2cont_fun cont_apply cont_tget cont_Abs_tuple)

lemma tupd_fupd: "tget (tupd a\<cdot>t\<cdot>b) = (tget t)(a := b)"
  by (simp add: tupd_beta Abs_tuple_inverse')

definition "tcut (A :: 'a::type set) \<equiv> \<Lambda> t. Abs_tuple (\<lambda>a. if a \<in> A then tget t a else \<bottom>)"

lemma tcut_beta: "tcut A\<cdot>t = Abs_tuple (\<lambda>a. if a \<in> A then tget t a else \<bottom>)"
  unfolding tcut_def
  by (simp add: cont2cont_fun cont_tget cont_Abs_tuple)

lemma tcut_tget: "tcut A\<cdot>t\<langle>a\<rangle> = (if a \<in> A then tget t a else \<bottom>)"
  by (simp add: tcut_beta Abs_tuple_inverse')

lemma tcut_mem[simp]: "a \<in> A \<Longrightarrow> tcut A\<cdot>t\<langle>a\<rangle> = t\<langle>a\<rangle>"
  by (simp add: tcut_tget)

lemma tcut_nomem[simp]: "a \<notin> A \<Longrightarrow> tcut A\<cdot>t\<langle>a\<rangle> = \<bottom>"
  by (simp add: tcut_tget)

lemma tuple_eqI: "(\<And>x. a\<langle>x\<rangle> = b\<langle>x\<rangle>) \<Longrightarrow> a = b" unfolding tget_inject[symmetric]
  by auto

lemma tuple_bounded_complete:
  fixes A :: "('a, 'b::bounded_complete) tuple set" and b
  assumes "A <| b"
  shows "A <<| Abs_tuple (lub (tget ` A))"
proof -
  from assms have ub: "tget ` A <| tget b" by (auto simp: is_ub_def below_tuple_def)
  from ex_bound_lub[OF ub] have lubA: "tget ` A <<| lub (tget ` A)" .
  show "A <<| Abs_tuple (lub (tget ` A))"
  proof (rule is_lubI)
    show "A <| Abs_tuple (lub (tget ` A))"
    proof (rule is_ubI)
      fix t assume "t \<in> A"
      hence "tget t \<sqsubseteq> lub (tget ` A)" using lubA by (meson imageI is_lubD1 is_ubD)
      thus "t \<sqsubseteq> Abs_tuple (lub (tget ` A))" by (simp add: below_tuple_def Abs_tuple_inverse')
    qed
  next
    fix u assume "A <| u"
    hence "tget ` A <| tget u" by (auto simp: is_ub_def below_tuple_def)
    with lubA have "lub (tget ` A) \<sqsubseteq> tget u" by (rule is_lubD2)
    thus "Abs_tuple (lub (tget ` A)) \<sqsubseteq> u" by (simp add: below_tuple_def Abs_tuple_inverse')
  qed
qed

instance tuple :: (type, bounded_complete) bounded_complete
  by intro_classes (blast intro: tuple_bounded_complete)

lemma tuple_lub:
  fixes A :: "('a, 'b::bounded_complete) tuple set"
  assumes "A <| b"
  shows "lub A = Abs_tuple (lub (tget ` A))"
  using lub_eqI[OF tuple_bounded_complete, OF assms] .

lemma tget_join:
  fixes a b :: "('a, 'b::bounded_complete) tuple"
  assumes "a \<Up> b"
  shows "tget (a \<squnion> b) = (\<lambda>p. tget a p \<squnion> tget b p)"
proof -
  from assms obtain z where az: "a \<sqsubseteq> z" and bz: "b \<sqsubseteq> z" by (auto simp: joinable_def)
  hence abf: "tget a \<Up> tget b" by (auto simp: below_tuple_def intro: joinableI)
  from az bz have zub: "{a, b} <| z" by (auto simp: is_ub_def)
  have "tget (a \<squnion> b) = lub (tget ` {a, b})"
    unfolding join_def using zub by (simp add: tuple_lub Abs_tuple_inverse')
  also have "... = tget a \<squnion> tget b" by (simp add: join_def)
  also have "... = (\<lambda>p. tget a p \<squnion> tget b p)" using abf by (rule fun_join)
  finally show ?thesis .
qed

lemma tget_meet:
  fixes a b :: "('a, 'b::bounded_complete) tuple"
  shows "tget (a \<sqinter> b) = (\<lambda>p. tget a p \<sqinter> tget b p)"
proof -
  let ?X = "Abs_tuple (\<lambda>p. tget a p \<sqinter> tget b p)"
  have le: "tget (a \<sqinter> b) p \<sqsubseteq> tget a p" "tget (a \<sqinter> b) p \<sqsubseteq> tget b p" for p
    using meet_below1[of a b, unfolded below_tuple_def, THEN fun_belowD]
          meet_below2[of a b, unfolded below_tuple_def, THEN fun_belowD] by auto
  have "a \<sqinter> b = ?X"
  proof (rule below_antisym)
    show "a \<sqinter> b \<sqsubseteq> ?X" unfolding below_tuple_def Abs_tuple_inverse'
      by (auto simp: fun_below_iff le intro: meet_greatest)
    show "?X \<sqsubseteq> a \<sqinter> b"
    proof (rule meet_greatest)
      show "?X \<sqsubseteq> a" unfolding below_tuple_def Abs_tuple_inverse'
        by (auto simp: fun_below_iff meet_below1)
      show "?X \<sqsubseteq> b" unfolding below_tuple_def Abs_tuple_inverse'
        by (auto simp: fun_below_iff meet_below2)
    qed
  qed
  thus ?thesis by (simp add: Abs_tuple_inverse')
qed

instance tuple :: (type, distributive_cpo) distributive_cpo
proof
  fix a b c :: "('a, 'b) tuple"
  assume ab: "a \<Up> b"
  hence ptw: "tget a p \<Up> tget b p" for p
    by (auto simp: joinable_def below_tuple_def intro: joinableI dest: fun_belowD)
  have cab: "(c \<sqinter> a) \<Up> (c \<sqinter> b)" by (rule joinableI[OF meet_below1 meet_below1])
  have "tget (c \<sqinter> (a \<squnion> b)) = (\<lambda>p. tget c p \<sqinter> (tget a p \<squnion> tget b p))"
    using ab by (simp add: tget_meet tget_join)
  also have "... = (\<lambda>p. (tget c p \<sqinter> tget a p) \<squnion> (tget c p \<sqinter> tget b p))"
    using ptw by (simp add: meet_join_distrib)
  also have "... = tget ((c \<sqinter> a) \<squnion> (c \<sqinter> b))"
    using cab by (simp add: tget_join tget_meet)
  finally show "c \<sqinter> (a \<squnion> b) = (c \<sqinter> a) \<squnion> (c \<sqinter> b)" by (simp add: tget_inject)
qed

instance tuple :: (countable, scott_domain) scott_domain ..

interpretation tcut_deflation: deflation "tcut A" for A
proof
  fix t :: "('a, 'b) tuple"
  show "tcut A\<cdot>(tcut A\<cdot>t) = tcut A\<cdot>t"
    by (rule tuple_eqI) (simp add: tcut_tget)
  show "tcut A\<cdot>t \<sqsubseteq> t"
    unfolding below_tuple_def below_fun_def
    by (simp add: tcut_tget)
qed

lemmas tcut_deflation = tcut_deflation.deflation_axioms

lemma tcut_mono: "A \<subseteq> B \<Longrightarrow> tcut A \<sqsubseteq> tcut B"
  unfolding below_cfun_def below_fun_def below_tuple_def
  by (auto simp add: tcut_tget)

lemma tcut_bot[simp]: "tcut {} = \<bottom>"
  by (intro cfun_eqI tuple_eqI) (simp add: tcut_tget tget_strict)

lemma deflation_le_cut: 
  assumes "deflation g"
    "deflation h"
    "g \<sqsubseteq> h"
    and fg: "f = f oo g"
  shows
    "f = f oo h"
proof -
  from assms have "g\<cdot>(h\<cdot>x) = g\<cdot>x" for x by (auto intro: deflation_below_comp1)
  then have 1: "g oo h = g" by (simp add: cfun_eq_iff)
  from fg have "f oo h = (f oo g) oo h" by simp
  also have "... = f oo (g oo h)" by (simp add: cfun_eq_iff)
  also note 1
  also note fg[symmetric]
  finally show ?thesis ..
qed

default_sort type

definition functions_with_support where
  "functions_with_support = {(A, f). f = f oo tcut A}"

typedef ('a, 'b::pcpo, 'c::cpo) tattr = "functions_with_support :: ('a set \<times> (('a, 'b) tuple \<rightarrow> 'c)) set"
proof
  show "({}::'a set, (\<Lambda> _.c)) \<in> functions_with_support" for c
    by (simp add: functions_with_support_def cfun_eq_iff)
qed

lemma tattr_liftI[intro]: "(\<And>x. f\<cdot>x = f\<cdot>(tcut A\<cdot>x)) \<Longrightarrow> (A, f) \<in> functions_with_support"
  unfolding functions_with_support_def by (simp add: cfun_eq_iff)

lemma tattr_liftE[elim]: "p \<in> functions_with_support \<Longrightarrow>
  (\<And>A f. p = (A, f) \<Longrightarrow> f = f oo tcut A \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  unfolding functions_with_support_def
  by (simp split: prod.splits)

setup_lifting type_definition_tattr

lift_definition tattr_const :: "'c \<Rightarrow> ('a, 'b::pcpo, 'c::cpo) tattr" is "\<lambda>x. ({}, (\<Lambda> _.x))"
  by auto

lemma tattr_Un: "f = f oo tcut A \<Longrightarrow> f = f oo tcut (A\<union>B)"
  by (rule deflation_le_cut[of "tcut A"]) (auto simp add: tcut_deflation intro: tcut_mono)

lemma tattr_Un': "f = f oo tcut A \<Longrightarrow> f\<cdot>x = f\<cdot>(tcut (A\<union>B)\<cdot>x)"
  by (drule tattr_Un[of f A B]) (simp add: cfun_eq_iff)

lift_definition tattr_slice :: "'a set \<Rightarrow> ('a, 'b::pcpo, 'c::cpo) tattr \<Rightarrow> ('a, 'b, 'c) tattr"
  is "\<lambda>B (A, f). (A\<union>B, f)"
  by (auto intro: tattr_Un')

lemma cont_tget_fix[simp]: "(\<Lambda> t. t\<langle>a\<rangle>)\<cdot>t = t\<langle>a\<rangle>" by (simp add: cont2cont_fun cont_tget)

lift_definition tattr_dim :: "'a \<Rightarrow> ('a, 'b::pcpo, 'b) tattr"
is "\<lambda>a. ({a}, (\<Lambda> t. t\<langle>a\<rangle>))"
  by (auto intro!: cfun_eqI)

lemma tattr_apply:
  assumes "f1 = f1 oo tcut A"
    "f2 = f2 oo tcut B"
  shows "(\<Lambda> t. f1\<cdot>t\<cdot>(f2\<cdot>t))\<cdot>t = (\<Lambda> t. f1\<cdot>t\<cdot>(f2\<cdot>t))\<cdot>(tcut (A\<union>B)\<cdot>t)"
  using tattr_Un'[OF assms(1), of t B] tattr_Un'[OF assms(2), of t A]
  by (simp add: sup_commute)

lift_definition tattr_apply :: "('a, 'b::pcpo, 'c::cpo \<rightarrow>'d::cpo) tattr \<Rightarrow> ('a, 'b, 'c) tattr \<Rightarrow> ('a, 'b, 'd) tattr"
is "\<lambda>(A, f1) (B, f2). (A\<union>B, (\<Lambda> t. f1\<cdot>t\<cdot>(f2\<cdot>t)))"
  by (auto intro: tattr_apply)

lift_definition tattr_dims :: "('a, 'b::pcpo, 'c::cpo) tattr \<Rightarrow> 'a set"
is "fst".

lift_definition tattr_eval :: "('a, 'b::pcpo, 'c::cpo) tattr \<Rightarrow> ('a, 'b) tuple \<rightarrow> 'c"
is "snd" .

abbreviation "tattr_eval' t f \<equiv> tattr_eval f\<cdot>t"
abbreviation "tattr_slice' f B \<equiv> tattr_slice B f"

notation
  tattr_const (\<open>(\<open>notation=\<open>prefix tattr_const\<close>\<close>\<star>_)\<close> [1000]1000)
  and tattr_dim (\<open>(\<open>notation=\<open>postfix tattr_const\<close>\<close>\<star>\<langle>_\<rangle>)\<close> [0]1000)
  and tattr_slice' (infixl \<open>\<star>'/\<close> 300)
  and tattr_apply (infixl \<open>\<star>$\<close> 200)
  and tattr_eval' (infix \<open>eval\<close> 100)
  and tattr_dims (\<open>\<D>\<close>)

lemma tattr_eval_const[simp]: "t eval \<star>c = c"
  by transfer' simp

lemma tattr_eval_dim[simp]: "t eval \<star>\<langle>a\<rangle> = t\<langle>a\<rangle>"
  by transfer' simp

lemma tattr_eval_slice[simp]: "t eval f \<star>/ A = t eval f"
  by transfer' (simp split: prod.splits)

lemma tattr_eval_apply[simp]: "t eval (a \<star>$ b) = (t eval a)\<cdot>(t eval b)"
  by transfer' (simp split: prod.splits)

lemma tattr_dims_const[simp]: "\<D>(\<star>c) = {}"
  by transfer' simp

lemma tattr_dims_dim[simp]: "\<D>(\<star>\<langle>d\<rangle>) = {d}"
  by transfer' simp

lemma tattr_dims_slice[simp]: "\<D>(f \<star>/ A) = \<D>(f) \<union> A"
  by transfer' (simp split: prod.splits)

lemma tattr_dims_apply[simp]: "\<D>(f \<star>$ g) = \<D>(f) \<union> \<D>(g)"
  by transfer' (simp split: prod.splits)

lemmas tattr_eval_simps =
  tattr_eval_const
  tattr_eval_dim
  tattr_eval_slice
  tattr_eval_apply

lemmas tattr_dims_simps =
  tattr_dims_const
  tattr_dims_dim
  tattr_dims_slice
  tattr_dims_apply

subsection \<open>Componentwise reasoning on tuples\<close>

lemma tuple_below_iff: "x \<sqsubseteq> y \<longleftrightarrow> (\<forall>d. x\<langle>d\<rangle> \<sqsubseteq> y\<langle>d\<rangle>)"
  by (simp add: below_tuple_def fun_below_iff)

lemma tuple_eq_iff: "x = y \<longleftrightarrow> (\<forall>d. x\<langle>d\<rangle> = y\<langle>d\<rangle>)"
  by (auto simp: po_eq_conv tuple_below_iff)

lemma tuple_joinableI:
  fixes x y :: "('d, 'v::bounded_complete) tuple"
  assumes "\<And>d. x\<langle>d\<rangle> \<Up> y\<langle>d\<rangle>"
  shows "x \<Up> y"
proof (rule joinableI)
  let ?z = "Abs_tuple (\<lambda>d. x\<langle>d\<rangle> \<squnion> y\<langle>d\<rangle>) :: ('d, 'v) tuple"
  show "x \<sqsubseteq> ?z" "y \<sqsubseteq> ?z"
    using joinableD[OF assms] by (simp_all add: tuple_below_iff Abs_tuple_inverse')
qed

text \<open>The single-key record \<open>tupd d\<cdot>\<bottom>\<cdot>x\<close>.\<close>

lemma tupd_bot_tget: "(tupd d\<cdot>\<bottom>\<cdot>x)\<langle>e\<rangle> = (if e = d then x else \<bottom>)"
  by (simp add: tupd_fupd tget_strict)

text \<open>The componentwise map of a family of functions.\<close>

definition tmap :: "('d \<Rightarrow> 'v::pcpo \<rightarrow> 'v) \<Rightarrow> ('d, 'v) tuple \<rightarrow> ('d, 'v) tuple" where
  "tmap f = (\<Lambda> t. Abs_tuple (\<lambda>d. f d\<cdot>(t\<langle>d\<rangle>)))"

lemma tmap_tget [simp]: "(tmap f\<cdot>t)\<langle>d\<rangle> = f d\<cdot>(t\<langle>d\<rangle>)"
  unfolding tmap_def
  by (subst beta_cfun)
    (simp_all add: cont_Abs_tuple cont2cont_lambda cont2cont_fun cont_tget Abs_tuple_inverse')

text \<open>The component at \<open>d\<close> of a function on tuples, read off the single-key records.\<close>

definition tcomp :: "'d \<Rightarrow> (('d, 'v::pcpo) tuple \<rightarrow> ('d, 'v) tuple) \<Rightarrow> 'v \<rightarrow> 'v" where
  "tcomp d p = (\<Lambda> t. t\<langle>d\<rangle>) oo p oo tupd d\<cdot>\<bottom>"

lemma tcomp_beta: "tcomp d p\<cdot>x = (p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>x))\<langle>d\<rangle>"
  by (simp add: tcomp_def)

lemma tcomp_tmap [simp]: "tcomp d (tmap f) = f d"
  by (rule cfun_eqI) (simp add: tcomp_beta tupd_bot_tget)

subsection \<open>Semi-factors of the tuple domain\<close>

text \<open>Records are ordered pointwise and their keys are independent, so a semi-factor of the
  tuples acts on each key separately: it is the componentwise map of its components, and these
  are semi-factors.  Hence the semi-factors of the tuples are the families of semi-factors.\<close>

lemma semi_factor_defl_tmap:
  fixes f :: "'d::countable \<Rightarrow> 'v::{bifinite, distributive_cpo} \<rightarrow> 'v"
  assumes f: "\<And>d. semi_factor_defl (f d)"
  shows "semi_factor_defl (tmap f)"
proof (rule semi_factor_deflI)
  have sf: "stable_defl (f d)" for d by (rule semi_factor_defl.axioms(1)[OF f])
  note df = stable_defl.deflation[OF sf]
  show "stable_defl (tmap f)"
  proof standard
    fix t show "tmap f\<cdot>(tmap f\<cdot>t) = tmap f\<cdot>t" by (simp add: tuple_eq_iff deflation.idem[OF df])
  next
    fix t show "tmap f\<cdot>t \<sqsubseteq> t" by (simp add: tuple_below_iff deflation.below[OF df])
  next
    fix x y :: "('d, 'v) tuple" assume "tmap f\<cdot>y = y" "x \<sqsubseteq> y"
    then show "tmap f\<cdot>x = x"
      by (auto simp: tuple_eq_iff tuple_below_iff intro: stable_defl.downclosed[OF sf])
  qed
  fix x y :: "('d, 'v) tuple" assume y: "tmap f\<cdot>y = y" and le: "tmap f\<cdot>x \<sqsubseteq> y"
  show "x \<Up> y"
  proof (rule tuple_joinableI)
    fix d
    from y have "(tmap f\<cdot>y)\<langle>d\<rangle> = y\<langle>d\<rangle>" by simp
    then have "f d\<cdot>(y\<langle>d\<rangle>) = y\<langle>d\<rangle>" by simp
    moreover from le have "f d\<cdot>(x\<langle>d\<rangle>) \<sqsubseteq> y\<langle>d\<rangle>" by (simp add: tuple_below_iff)
    ultimately show "x\<langle>d\<rangle> \<Up> y\<langle>d\<rangle>" by (rule semi_factor_defl.slide[OF f])
  qed
qed

lemma deflation_tupd:
  fixes p :: "('d, 'v::pcpo) tuple \<rightarrow> ('d, 'v) tuple"
  assumes p: "deflation p"
  shows "p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>x) = tupd d\<cdot>\<bottom>\<cdot>(tcomp d p\<cdot>x)"
proof (rule tuple_eqI)
  fix e
  have "(p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>x))\<langle>e\<rangle> \<sqsubseteq> (tupd d\<cdot>\<bottom>\<cdot>x)\<langle>e\<rangle>"
    using deflation.below[OF p] by (simp add: tuple_below_iff)
  then show "(p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>x))\<langle>e\<rangle> = (tupd d\<cdot>\<bottom>\<cdot>(tcomp d p\<cdot>x))\<langle>e\<rangle>"
    by (cases "e = d") (simp_all add: tupd_bot_tget tcomp_beta)
qed

lemma stable_defl_tget:
  fixes p :: "('d::countable, 'v::{bifinite, distributive_cpo}) tuple \<rightarrow> ('d, 'v) tuple"
  assumes p: "stable_defl p"
  shows "(p\<cdot>t)\<langle>d\<rangle> = tcomp d p\<cdot>(t\<langle>d\<rangle>)"
proof (rule below_antisym)
  interpret P: stable_defl p by (rule p)
  let ?s = "tupd d\<cdot>\<bottom>\<cdot>(t\<langle>d\<rangle>)" and ?u = "tupd d\<cdot>\<bottom>\<cdot>((p\<cdot>t)\<langle>d\<rangle>)"
  have "?u \<sqsubseteq> p\<cdot>t" by (simp add: tuple_below_iff tupd_bot_tget)
  then have "p\<cdot>?u = ?u" by (rule P.lower_fixed)
  moreover have "?u \<sqsubseteq> ?s" using P.below[of t] by (simp add: tuple_below_iff tupd_bot_tget)
  ultimately have "?u \<sqsubseteq> p\<cdot>?s" by (rule P.below_image)
  then have "?u\<langle>d\<rangle> \<sqsubseteq> (p\<cdot>?s)\<langle>d\<rangle>" by (simp add: tuple_below_iff)
  then show "(p\<cdot>t)\<langle>d\<rangle> \<sqsubseteq> tcomp d p\<cdot>(t\<langle>d\<rangle>)" by (simp add: tupd_bot_tget tcomp_beta)
  have "?s \<sqsubseteq> t" by (simp add: tuple_below_iff tupd_bot_tget)
  then have "p\<cdot>?s \<sqsubseteq> p\<cdot>t" by (rule monofun_cfun_arg)
  then have "(p\<cdot>?s)\<langle>d\<rangle> \<sqsubseteq> (p\<cdot>t)\<langle>d\<rangle>" by (simp add: tuple_below_iff)
  then show "tcomp d p\<cdot>(t\<langle>d\<rangle>) \<sqsubseteq> (p\<cdot>t)\<langle>d\<rangle>" by (simp add: tcomp_beta)
qed

lemma tmap_tcomp:
  fixes p :: "('d::countable, 'v::{bifinite, distributive_cpo}) tuple \<rightarrow> ('d, 'v) tuple"
  assumes "stable_defl p" shows "tmap (\<lambda>d. tcomp d p) = p"
  by (rule cfun_eqI) (simp add: tuple_eq_iff stable_defl_tget[OF assms])

lemma semi_factor_defl_tcomp:
  fixes p :: "('d::countable, 'v::{bifinite, distributive_cpo}) tuple \<rightarrow> ('d, 'v) tuple"
  assumes p: "semi_factor_defl p"
  shows "semi_factor_defl (tcomp d p)"
proof (rule semi_factor_deflI)
  interpret P: semi_factor_defl p by (rule p)
  note single = deflation_tupd[OF P.deflation]
  show "stable_defl (tcomp d p)"
  proof standard
    fix x
    have "tcomp d p\<cdot>(tcomp d p\<cdot>x) = (p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>(tcomp d p\<cdot>x)))\<langle>d\<rangle>" by (rule tcomp_beta)
    also have "\<dots> = (p\<cdot>(p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>x)))\<langle>d\<rangle>" by (simp only: single)
    also have "\<dots> = tcomp d p\<cdot>x" by (simp add: P.idem tcomp_beta)
    finally show "tcomp d p\<cdot>(tcomp d p\<cdot>x) = tcomp d p\<cdot>x" .
  next
    fix x
    have "(p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>x))\<langle>d\<rangle> \<sqsubseteq> (tupd d\<cdot>\<bottom>\<cdot>x)\<langle>d\<rangle>" using P.below by (simp add: tuple_below_iff)
    then show "tcomp d p\<cdot>x \<sqsubseteq> x" by (simp add: tcomp_beta tupd_bot_tget)
  next
    fix x y assume y: "tcomp d p\<cdot>y = y" and xy: "x \<sqsubseteq> y"
    have "p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>y) = tupd d\<cdot>\<bottom>\<cdot>y" by (simp add: single y)
    moreover have "tupd d\<cdot>\<bottom>\<cdot>x \<sqsubseteq> tupd d\<cdot>\<bottom>\<cdot>y" using xy by (rule monofun_cfun_arg)
    ultimately have "p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>x) = tupd d\<cdot>\<bottom>\<cdot>x" by (rule P.downclosed)
    then show "tcomp d p\<cdot>x = x" by (simp add: tcomp_beta tupd_bot_tget)
  qed
  fix x y assume y: "tcomp d p\<cdot>y = y" and le: "tcomp d p\<cdot>x \<sqsubseteq> y"
  have fy: "p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>y) = tupd d\<cdot>\<bottom>\<cdot>y" by (simp add: single y)
  have "p\<cdot>(tupd d\<cdot>\<bottom>\<cdot>x) \<sqsubseteq> tupd d\<cdot>\<bottom>\<cdot>y" unfolding single using le by (rule monofun_cfun_arg)
  with fy have j: "tupd d\<cdot>\<bottom>\<cdot>x \<Up> tupd d\<cdot>\<bottom>\<cdot>y" by (rule P.slide)
  have "(tupd d\<cdot>\<bottom>\<cdot>x)\<langle>d\<rangle> \<sqsubseteq> (tupd d\<cdot>\<bottom>\<cdot>x \<squnion> tupd d\<cdot>\<bottom>\<cdot>y)\<langle>d\<rangle>"
    "(tupd d\<cdot>\<bottom>\<cdot>y)\<langle>d\<rangle> \<sqsubseteq> (tupd d\<cdot>\<bottom>\<cdot>x \<squnion> tupd d\<cdot>\<bottom>\<cdot>y)\<langle>d\<rangle>"
    using joinableD[OF j] by (simp_all add: tuple_below_iff)
  then show "x \<Up> y" by (simp add: tupd_bot_tget) (rule joinableI)
qed

text \<open>The isomorphism between families of semi-factors and semi-factors of the tuples.\<close>

definition semi_factor_of_family ::
  "('d::countable \<Rightarrow> 'v::{bifinite, distributive_cpo} semi_factor) \<Rightarrow> ('d, 'v) tuple semi_factor"
  where "semi_factor_of_family F = semi_factor_of_defl (tmap (\<lambda>d. semi_factor_p (F d)))"

definition family_of_semi_factor ::
  "('d::countable, 'v::{bifinite, distributive_cpo}) tuple semi_factor \<Rightarrow> 'd \<Rightarrow> 'v semi_factor"
  where "family_of_semi_factor G d = semi_factor_of_defl (tcomp d (semi_factor_p G))"

lemma semi_factor_p_of_family:
  "semi_factor_p (semi_factor_of_family F) = tmap (\<lambda>d. semi_factor_p (F d))"
  unfolding semi_factor_of_family_def
  by (rule semi_factor_p_of_defl, rule semi_factor_defl_tmap, rule semi_factor_defl_semi_factor_p)

lemma semi_factor_p_family_of:
  "semi_factor_p (family_of_semi_factor G d) = tcomp d (semi_factor_p G)"
  unfolding family_of_semi_factor_def
  by (rule semi_factor_p_of_defl, rule semi_factor_defl_tcomp, rule semi_factor_defl_semi_factor_p)

lemma family_of_semi_factor_of_family [simp]: "family_of_semi_factor (semi_factor_of_family F) = F"
  by (rule ext) (simp add: semi_factor_p_inject[symmetric] semi_factor_p_family_of
      semi_factor_p_of_family)

lemma semi_factor_of_family_of_semi_factor [simp]:
  "semi_factor_of_family (family_of_semi_factor G) = G"
  using semi_factor_defl.axioms(1)[OF semi_factor_defl_semi_factor_p[of G]]
  by (simp add: semi_factor_p_inject[symmetric] semi_factor_p_of_family semi_factor_p_family_of
      tmap_tcomp)

lemma tmap_below_iff: "tmap f \<sqsubseteq> tmap g \<longleftrightarrow> (\<forall>d. f d \<sqsubseteq> g d)"
proof
  assume fg: "tmap f \<sqsubseteq> tmap g"
  show "\<forall>d. f d \<sqsubseteq> g d"
  proof (intro allI cfun_belowI)
    fix d x
    have "(tmap f\<cdot>(tupd d\<cdot>\<bottom>\<cdot>x))\<langle>d\<rangle> \<sqsubseteq> (tmap g\<cdot>(tupd d\<cdot>\<bottom>\<cdot>x))\<langle>d\<rangle>"
      using monofun_cfun_fun[OF fg] by (simp add: tuple_below_iff)
    then show "f d\<cdot>x \<sqsubseteq> g d\<cdot>x" by (simp add: tupd_bot_tget)
  qed
qed (auto intro!: cfun_belowI simp: tuple_below_iff monofun_cfun_fun)

lemma semi_factor_of_family_below_iff:
  "semi_factor_of_family F \<sqsubseteq> semi_factor_of_family F' \<longleftrightarrow> F \<sqsubseteq> F'"
  by (simp add: semi_factor_below_iff_p semi_factor_p_of_family tmap_below_iff fun_below_iff)

lemma family_of_semi_factor_below_iff:
  "family_of_semi_factor G \<sqsubseteq> F \<longleftrightarrow> G \<sqsubseteq> semi_factor_of_family F"
  by (metis semi_factor_of_family_below_iff semi_factor_of_family_of_semi_factor)

lemma below_family_of_semi_factor_iff:
  "F \<sqsubseteq> family_of_semi_factor G \<longleftrightarrow> semi_factor_of_family F \<sqsubseteq> G"
  by (metis semi_factor_of_family_below_iff semi_factor_of_family_of_semi_factor)

text \<open>Being an order isomorphism, it preserves all glbs and lubs.\<close>

lemma semi_factor_of_family_glb:
  "semi_factor_of_family (glb A) = glb (semi_factor_of_family ` A)"
proof (rule below_antisym)
  show "semi_factor_of_family (glb A) \<sqsubseteq> glb (semi_factor_of_family ` A)"
    by (rule lattice_glb_greatest) (auto simp: semi_factor_of_family_below_iff intro: glb_below)
  show "glb (semi_factor_of_family ` A) \<sqsubseteq> semi_factor_of_family (glb A)"
    unfolding family_of_semi_factor_below_iff[symmetric]
    by (rule lattice_glb_greatest) (simp add: family_of_semi_factor_below_iff glb_below)
qed

lemma semi_factor_of_family_lub:
  "semi_factor_of_family (lub A) = lub (semi_factor_of_family ` A)"
proof (rule below_antisym)
  show "semi_factor_of_family (lub A) \<sqsubseteq> lub (semi_factor_of_family ` A)"
    unfolding below_family_of_semi_factor_iff[symmetric]
    by (rule lattice_lub_least) (simp add: is_ub_def below_family_of_semi_factor_iff lattice_lub_upper)
  show "lub (semi_factor_of_family ` A) \<sqsubseteq> semi_factor_of_family (lub A)"
    by (rule lattice_lub_least)
      (auto simp: is_ub_def semi_factor_of_family_below_iff intro: lattice_lub_upper)
qed

lemma semi_factor_of_family_inf:
  "semi_factor_of_family (F \<sqinter> G) = semi_factor_of_family F \<sqinter> semi_factor_of_family G"
  unfolding meet_def using semi_factor_of_family_glb[of "{F, G}"] by simp

lemma semi_factor_of_family_sup:
  "semi_factor_of_family (F \<squnion> G) = semi_factor_of_family F \<squnion> semi_factor_of_family G"
  unfolding join_def using semi_factor_of_family_lub[of "{F, G}"] by simp

lemma semi_factor_of_family_top: "semi_factor_of_family \<top> = \<top>"
  by (rule below_antisym) (simp_all add: family_of_semi_factor_below_iff[symmetric])

lemma semi_factor_of_family_bot: "semi_factor_of_family \<bottom> = \<bottom>"
  by (rule bottomI) (subst below_family_of_semi_factor_iff[symmetric], rule minimal)

lemma semi_factor_of_family_proj [simp]: "(t \<downharpoonright> semi_factor_of_family F)\<langle>d\<rangle> = t\<langle>d\<rangle> \<downharpoonright> F d"
  by (simp add: semi_factor_p_of_family)

subsection \<open>Dimension sets as semi-factors of the tuple domain\<close>

text \<open>The coordinate cut is the family that is the top on the dimensions and \<open>\<bottom>\<close> elsewhere.\<close>

definition dcut :: "'a::countable set \<Rightarrow> ('a, 'b::scott_domain) tuple semi_factor" where
  "dcut A = semi_factor_of_family (\<lambda>d. if d \<in> A then \<top> else \<bottom>)"

lemma semi_factor_p_dcut:
  "semi_factor_p (dcut A) = (tcut A :: ('a::countable, 'b::scott_domain) tuple \<rightarrow> ('a,'b) tuple)"
  by (rule cfun_eqI, rule tuple_eqI)
    (simp add: dcut_def semi_factor_p_of_family tcut_tget semi_factor_p_top semi_factor_p_bot)

text \<open>Projecting a tuple onto the dimensions of an LOD is exactly the coordinate cut.\<close>
lemma dcut_proj: "x \<downharpoonright> dcut A = tcut A\<cdot>x"
  by (simp add: semi_factor_p_dcut)

text \<open>A semi-factor is determined by its projection.\<close>
lemma semi_factor_eqI:
  assumes "semi_factor_p F = semi_factor_p G" shows "F = G"
  using assms by (simp add: semi_factor_p_inject)

lemma tcut_compose: "tcut B\<cdot>(tcut A\<cdot>t) = tcut (A \<inter> B)\<cdot>t"
  by (rule tuple_eqI) (simp add: tcut_tget)

text \<open>@{const dcut} is a lattice homomorphism, as the indicator families are.\<close>
lemma dcut_inf: "dcut (A \<inter> B) = dcut A \<sqinter> dcut B"
  unfolding dcut_def semi_factor_of_family_inf[symmetric]
  by (rule arg_cong[where f = semi_factor_of_family]) (simp add: fun_eq_iff fun_meet lattice_meet_idem lattice_meet_bot_left lattice_meet_bot_right)

lemma tcut_joinable: "tcut A\<cdot>t \<Up> tcut B\<cdot>t"
  by (rule joinableI[OF tcut_deflation.below tcut_deflation.below])

lemma tcut_join: "tcut A\<cdot>t \<squnion> tcut B\<cdot>t = tcut (A \<union> B)\<cdot>t"
  for t :: "('a, 'b::bounded_complete) tuple"
proof (rule tuple_eqI)
  fix a
  have "tget (tcut A\<cdot>t \<squnion> tcut B\<cdot>t) a = tget (tcut A\<cdot>t) a \<squnion> tget (tcut B\<cdot>t) a"
    by (subst tget_join[OF tcut_joinable]) simp
  thus "(tcut A\<cdot>t \<squnion> tcut B\<cdot>t)\<langle>a\<rangle> = (tcut (A \<union> B)\<cdot>t)\<langle>a\<rangle>"
    by (cases "a \<in> A"; cases "a \<in> B") (simp_all add: tcut_tget)
qed

lemma dcut_sup: "dcut (A \<union> B) = dcut A \<squnion> dcut B"
  unfolding dcut_def semi_factor_of_family_sup[symmetric]
  by (rule arg_cong[where f = semi_factor_of_family]) (simp add: fun_eq_iff fun_join lattice_join_bot_left lattice_join_bot_right)

lemma dcut_bot: "dcut {} = \<bottom>"
  by (simp add: dcut_def semi_factor_of_family_bot lambda_strict)

lemma dcut_top: "dcut UNIV = \<top>"
  by (simp add: dcut_def semi_factor_of_family_top[unfolded lattice_top_fun])

lemma tcut_below: "tcut A\<cdot>t \<sqsubseteq> t"
  by (simp add: below_tuple_def fun_below_iff tcut_tget)

lemma tcut_mono_set: "A \<subseteq> B \<Longrightarrow> tcut A\<cdot>t \<sqsubseteq> tcut B\<cdot>t"
  by (auto simp: below_tuple_def fun_below_iff tcut_tget)

text \<open>The support of a tuple: the coordinates it defines.  A key carries its own dimensions.\<close>

definition tsupp :: "('d, 'v::pcpo) tuple \<Rightarrow> 'd set" where
  "tsupp K = {d. K\<langle>d\<rangle> \<noteq> \<bottom>}"

lemma tsupp_tcut: "tsupp (tcut A\<cdot>K) = tsupp K \<inter> A"
  by (auto simp: tsupp_def tcut_tget)

lemma tcut_tsupp: "tcut (tsupp K)\<cdot>K = K"
  by (rule tuple_eqI) (simp add: tcut_tget tsupp_def)

lemma tcut_below_tcut: "tsupp K \<inter> A \<subseteq> B \<Longrightarrow> tcut A\<cdot>K \<sqsubseteq> tcut B\<cdot>K"
  by (auto simp: below_tuple_def fun_below_iff tcut_tget tsupp_def)

lemma tsupp_mono: "x \<sqsubseteq> y \<Longrightarrow> tsupp x \<subseteq> tsupp y"
  by (auto simp: tsupp_def below_tuple_def fun_below_iff) (metis bottomI)

lemma adm_finite_bex: "finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> adm (P a)) \<Longrightarrow> adm (\<lambda>x. \<exists>a\<in>A. P a x)"
  by (induct rule: finite_induct) simp_all

text \<open>Being defined on finitely many dimensions is an open condition.\<close>

lemma adm_not_tsupp: "finite D \<Longrightarrow> adm (\<lambda>t. \<not> D \<subseteq> tsupp t)"
proof -
  assume "finite D"
  then have "adm (\<lambda>t. \<exists>d\<in>D. t\<langle>d\<rangle> \<sqsubseteq> \<bottom>)"
    by (rule adm_finite_bex) (intro adm_below cont_const, simp add: cont2cont_fun cont_tget)
  then show ?thesis by (simp add: tsupp_def subset_iff Bex_def)
qed

text \<open>With chain-finite (e.g.\ flat) values, a cut to finitely many dimensions is compact, and
  so is a key with finite support.\<close>

lemma compact_tcut:
  fixes t :: "('d, 'v::{pcpo, chfin}) tuple"
  assumes "finite A"
  shows "compact (tcut A\<cdot>t)"
proof (rule compactI)
  have "(\<not> tcut A\<cdot>t \<sqsubseteq> u) \<longleftrightarrow> (\<exists>a\<in>A. \<not> t\<langle>a\<rangle> \<sqsubseteq> u\<langle>a\<rangle>)" for u
    by (auto simp: below_tuple_def fun_below_iff tcut_tget)
  moreover have "adm (\<lambda>u. \<exists>a\<in>A. \<not> t\<langle>a\<rangle> \<sqsubseteq> u\<langle>a\<rangle>)"
    using assms by (rule adm_finite_bex) (simp add: cont2cont_fun cont_tget)
  ultimately show "adm (\<lambda>u. \<not> tcut A\<cdot>t \<sqsubseteq> u)" by simp
qed

lemma compact_tsupp:
  fixes K :: "('d, 'v::{pcpo, chfin}) tuple"
  assumes "finite (tsupp K)"
  shows "compact K"
  using compact_tcut[OF assms, of K] by (simp add: tcut_tsupp)

lemma tget_lub: "chain Y \<Longrightarrow> (\<Squnion>i. Y i)\<langle>d\<rangle> = (\<Squnion>i. (Y i)\<langle>d\<rangle>)"
  by (simp add: lub_tuple Abs_tuple_inverse' lub_fun ch2ch_cont cont_tget)

text \<open>Conversely, a compact key has finite support (whatever the values): otherwise cutting
  away ever smaller tails of an infinite sequence in its support approximates it by a chain of
  keys none of which is above it.  So compactness, the finitely observable keys, is what keys
  should be; for chain-finite values it is exactly finite support.\<close>

lemma compact_finite_tsupp:
  fixes K :: "('d, 'v::pcpo) tuple"
  assumes "compact K"
  shows "finite (tsupp K)"
proof (rule ccontr)
  assume "infinite (tsupp K)"
  then obtain f :: "nat \<Rightarrow> 'd" where f: "inj f" "range f \<subseteq> tsupp K"
    using infinite_countable_subset by blast
  define Y where "Y i = tcut (- f ` {i..})\<cdot>K" for i
  have Y: "chain Y"
    by (rule chainI) (auto simp: Y_def intro: tcut_mono_set)
  have "K \<sqsubseteq> (\<Squnion>i. Y i)"
  proof -
    have "K\<langle>d\<rangle> \<sqsubseteq> (\<Squnion>i. (Y i)\<langle>d\<rangle>)" for d
    proof -
      have ch: "chain (\<lambda>i. (Y i)\<langle>d\<rangle>)"
        using Y by (simp add: chain_def below_tuple_def fun_below_iff)
      obtain j where "(Y j)\<langle>d\<rangle> = K\<langle>d\<rangle>"
      proof (cases "d \<in> range f")
        case True
        then obtain j where d: "d = f j" by blast
        have "(Y (Suc j))\<langle>d\<rangle> = K\<langle>d\<rangle>"
          unfolding Y_def by (simp add: tcut_tget d inj_image_mem_iff[OF f(1)])
        then show ?thesis by (rule that)
      next
        case False
        then have "(Y 0)\<langle>d\<rangle> = K\<langle>d\<rangle>" by (auto simp: Y_def tcut_tget)
        then show ?thesis by (rule that)
      qed
      then show ?thesis using is_ub_thelub[OF ch, of j] by simp
    qed
    then show ?thesis by (simp add: below_tuple_def fun_below_iff tget_lub[OF Y])
  qed
  then obtain i where "K \<sqsubseteq> Y i" using assms Y compact_below_lub_iff by blast
  then have "K\<langle>f i\<rangle> \<sqsubseteq> (Y i)\<langle>f i\<rangle>" by (simp add: below_tuple_def fun_below_iff)
  moreover have "(Y i)\<langle>f i\<rangle> = \<bottom>" by (simp add: Y_def tcut_tget)
  moreover have "K\<langle>f i\<rangle> \<noteq> \<bottom>" using f(2) by (auto simp: tsupp_def)
  ultimately show False by simp
qed

text \<open>Cutting a compact key leaves it compact.\<close>

lemma compact_tcut_compact:
  fixes K :: "('d, 'v::pcpo) tuple"
  assumes "compact K"
  shows "compact (tcut A\<cdot>K)"
proof (rule compactI2)
  fix Y assume Y: "chain Y" and below: "tcut A\<cdot>K \<sqsubseteq> (\<Squnion>i. Y i)"
  define Z where "Z i = Abs_tuple (\<lambda>d. if d \<in> A then (Y i)\<langle>d\<rangle> else K\<langle>d\<rangle>)" for i
  have Zd: "(Z i)\<langle>d\<rangle> = (if d \<in> A then (Y i)\<langle>d\<rangle> else K\<langle>d\<rangle>)" for i d
    by (simp add: Z_def Abs_tuple_inverse')
  have Z: "chain Z"
    using Y by (auto intro!: chainI simp: below_tuple_def fun_below_iff Zd chain_def)
  have "K \<sqsubseteq> (\<Squnion>i. Z i)"
  proof -
    have "K\<langle>d\<rangle> \<sqsubseteq> (\<Squnion>i. (Z i)\<langle>d\<rangle>)" for d
    proof (cases "d \<in> A")
      case True
      from below have "(tcut A\<cdot>K)\<langle>d\<rangle> \<sqsubseteq> (\<Squnion>i. Y i)\<langle>d\<rangle>" by (simp add: below_tuple_def fun_below_iff)
      with True show ?thesis by (simp add: Zd tget_lub[OF Y] tcut_tget)
    next
      case False then show ?thesis by (simp add: Zd)
    qed
    then show ?thesis by (simp add: below_tuple_def fun_below_iff tget_lub[OF Z])
  qed
  then obtain i where "K \<sqsubseteq> Z i" using assms Z compact_below_lub_iff by blast
  then have "tcut A\<cdot>K \<sqsubseteq> Y i"
    by (auto simp: below_tuple_def fun_below_iff Zd tcut_tget split: if_splits)
  then show "\<exists>i. tcut A\<cdot>K \<sqsubseteq> Y i" ..
qed

subsection \<open>Compact tuples\<close>


text \<open>A tuple is compact exactly when it has finite support and compact components.  A component
  of a compact tuple is compact: a chain approximating the component, placed into the tuple,
  approximates the whole tuple.\<close>

lemma compact_tget:
  fixes K :: "('d, 'v::pcpo) tuple"
  assumes "compact K" shows "compact (K\<langle>d\<rangle>)"
proof (rule compactI2)
  fix Y :: "nat \<Rightarrow> 'v" assume Y: "chain Y" and le: "K\<langle>d\<rangle> \<sqsubseteq> (\<Squnion>i. Y i)"
  define Z where "Z i = Abs_tuple ((tget K)(d := Y i))" for i
  have Zd: "(Z i)\<langle>e\<rangle> = (if e = d then Y i else K\<langle>e\<rangle>)" for i e
    by (simp add: Z_def Abs_tuple_inverse')
  have Z: "chain Z"
    using Y by (simp add: chain_def tuple_below_iff Zd)
  have "K \<sqsubseteq> (\<Squnion>i. Z i)"
    using le by (simp add: tuple_below_iff tget_lub[OF Z] Zd Y)
  then obtain i where "K \<sqsubseteq> Z i" using compactD2[OF assms Z] by blast
  then have "K\<langle>d\<rangle> \<sqsubseteq> (Z i)\<langle>d\<rangle>" by (simp add: tuple_below_iff)
  then show "\<exists>i. K\<langle>d\<rangle> \<sqsubseteq> Y i" by (auto simp: Zd)
qed

lemma compact_tupleI:
  fixes K :: "('d, 'v::pcpo) tuple"
  assumes "finite (tsupp K)" and "\<And>d. compact (K\<langle>d\<rangle>)"
  shows "compact K"
proof (rule compactI)
  have "(\<not> K \<sqsubseteq> u) \<longleftrightarrow> (\<exists>d\<in>tsupp K. \<not> K\<langle>d\<rangle> \<sqsubseteq> u\<langle>d\<rangle>)" for u
    by (auto simp: tuple_below_iff tsupp_def) (metis minimal)
  moreover have "adm (\<lambda>u. \<exists>d\<in>tsupp K. \<not> K\<langle>d\<rangle> \<sqsubseteq> u\<langle>d\<rangle>)"
    using assms(1) proof (rule adm_finite_bex)
    show "adm (\<lambda>u. \<not> K\<langle>d\<rangle> \<sqsubseteq> u\<langle>d\<rangle>)" for d
      by (rule adm_compact_not_below[OF assms(2)]) (simp add: cont2cont_fun cont_tget)
  qed
  ultimately show "adm (\<lambda>u. \<not> K \<sqsubseteq> u)" by simp
qed

end