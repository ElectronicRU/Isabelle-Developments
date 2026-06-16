theory ValsetBase imports HOLCF "HOLCF-extra.Cpo_Topology"
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

term Least

pcpodef ('a::type, 'b) tuple = "UNIV :: ('a \<Rightarrow> 'b::pcpo) set"
  morphisms "tget" "Abs_tuple"
  by simp_all

lemma Abs_tuple_inverse': "tget (Abs_tuple t) = t" using Abs_tuple_inverse by simp

find_theorems name: tuple name: ValsetBase

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

definition tupd :: "'a \<Rightarrow> ('a, 'b) tuple \<rightarrow> 'b \<rightarrow> ('a, 'b) tuple" where
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

find_theorems name: tattr_eval

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

end