theory ValsetBase imports HOLCF "HOLCF-extra.Cpo_Topology" "HOLCF-extra.Bounded_Complete" Subdomain
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

definition tupd :: "'a \<Rightarrow> ('a, 'b::domain) tuple \<rightarrow> 'b \<rightarrow> ('a, 'b) tuple" where
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

subsection \<open>Dimension sets as semi-factors of the tuple domain\<close>

lemma stable_subdomain_tcut:
  "stable_subdomain {t :: ('a::countable, 'b::scott_domain) tuple. tcut A\<cdot>t = t}"
proof (rule deflation_stable_subdomainI[OF tcut_deflation])
  fix x y :: "('a, 'b) tuple"
  assume y: "tcut A\<cdot>y = y" and xy: "x \<sqsubseteq> y"
  show "tcut A\<cdot>x = x"
  proof (rule tuple_eqI)
    fix a show "(tcut A\<cdot>x)\<langle>a\<rangle> = x\<langle>a\<rangle>"
    proof (cases "a \<in> A")
      case True thus ?thesis by simp
    next
      case False
      hence "y\<langle>a\<rangle> = \<bottom>" using y by (metis tcut_nomem)
      moreover from xy have "x\<langle>a\<rangle> \<sqsubseteq> y\<langle>a\<rangle>" by (metis below_tuple_def fun_belowD)
      ultimately have "x\<langle>a\<rangle> = \<bottom>" by simp
      with False show ?thesis by simp
    qed
  qed
qed

lemma set_of_subdom_tcut:
  "set_of_subdom (subdom_of_set {t. tcut A\<cdot>t = t} :: ('a::countable, 'b::scott_domain) tuple stable_subdom)
     = {t. tcut A\<cdot>t = t}"
  by (simp add: subdom_of_set_inverse stable_subdomain_tcut)

lemma p_subdom_tcut:
  "stable_subdom_p (subdom_of_set {t. tcut A\<cdot>t = t})
     = (tcut A :: ('a::countable, 'b::scott_domain) tuple \<rightarrow> ('a,'b) tuple)"
  by (simp add: stable_subdom_p.rep_eq set_of_subdom_tcut
        stable_subdomain_deflation[OF tcut_deflation stable_subdomain_tcut, symmetric])

lemma is_strong_tcut:
  "is_strong (subdom_of_set {t. tcut A\<cdot>t = t} :: ('a::countable, 'b::scott_domain) tuple stable_subdom)"
proof (rule is_strongI)
  fix x y :: "('a, 'b) tuple"
  assume "y \<in> set_of_subdom (subdom_of_set {t. tcut A\<cdot>t = t})"
  hence yfix: "tcut A\<cdot>y = y" by (simp add: set_of_subdom_tcut)
  assume "stable_subdom_p (subdom_of_set {t. tcut A\<cdot>t = t})\<cdot>x \<sqsubseteq> y"
  hence le: "tcut A\<cdot>x \<sqsubseteq> y" by (simp add: p_subdom_tcut)
  let ?z = "Abs_tuple (\<lambda>a. if a \<in> A then y\<langle>a\<rangle> else x\<langle>a\<rangle>)"
  have xz: "x \<sqsubseteq> ?z" unfolding below_tuple_def Abs_tuple_inverse' fun_below_iff
  proof
    fix a show "x\<langle>a\<rangle> \<sqsubseteq> (if a \<in> A then y\<langle>a\<rangle> else x\<langle>a\<rangle>)"
    proof (cases "a \<in> A")
      case True
      have "(tcut A\<cdot>x)\<langle>a\<rangle> \<sqsubseteq> y\<langle>a\<rangle>" using le by (metis below_tuple_def fun_belowD)
      thus ?thesis using True by simp
    next
      case False thus ?thesis by simp
    qed
  qed
  have yz: "y \<sqsubseteq> ?z" unfolding below_tuple_def Abs_tuple_inverse' fun_below_iff
  proof
    fix a show "y\<langle>a\<rangle> \<sqsubseteq> (if a \<in> A then y\<langle>a\<rangle> else x\<langle>a\<rangle>)"
    proof (cases "a \<in> A")
      case True thus ?thesis by simp
    next
      case False
      hence "y\<langle>a\<rangle> = \<bottom>" using yfix by (metis tcut_nomem)
      thus ?thesis using False by simp
    qed
  qed
  from xz yz show "x \<Up> y" by (rule joinableI)
qed

definition dcut :: "'a::countable set \<Rightarrow> ('a, 'b::scott_domain) tuple semi_factor" where
  "dcut A = factor_of_subdom (subdom_of_set {t. tcut A\<cdot>t = t})"

lemma semi_factor_p_dcut:
  "semi_factor_p (dcut A) = (tcut A :: ('a::countable, 'b::scott_domain) tuple \<rightarrow> ('a,'b) tuple)"
  unfolding dcut_def semi_factor_p.rep_eq
  by (simp add: factor_of_subdom_inverse is_strong_tcut p_subdom_tcut)

text \<open>Projecting a tuple onto the dimensions of an LOD is exactly the coordinate cut.\<close>
lemma dcut_proj: "x \<downharpoonright> dcut A = tcut A\<cdot>x"
  by (simp add: semi_factor_p_dcut)

text \<open>A semi-factor is determined by its projection.\<close>
lemma semi_factor_eqI:
  assumes "semi_factor_p F = semi_factor_p G" shows "F = G"
proof -
  from assms have "stable_subdom_p (subdom_of_factor F) = stable_subdom_p (subdom_of_factor G)"
    by (simp add: semi_factor_p.rep_eq)
  hence "subdom_of_factor F = subdom_of_factor G" by (rule stable_subdom_proj_eqI)
  thus "F = G" by (simp add: subdom_of_factor_inject)
qed

lemma tcut_compose: "tcut B\<cdot>(tcut A\<cdot>t) = tcut (A \<inter> B)\<cdot>t"
  by (rule tuple_eqI) (simp add: tcut_tget)

text \<open>@{const dcut} is a lattice homomorphism: intersection of dimension sets is the
  semi-factor meet.\<close>
lemma dcut_inf: "dcut (A \<inter> B) = inf (dcut A) (dcut B)"
proof (rule semi_factor_eqI, rule cfun_eqI)
  fix x
  have "x \<downharpoonright> dcut (A \<inter> B) = tcut B\<cdot>(tcut A\<cdot>x)" by (simp add: dcut_proj tcut_compose)
  also have "... = x \<downharpoonright> dcut A \<downharpoonright> dcut B" by (simp add: dcut_proj)
  also have "... = x \<downharpoonright> inf (dcut A) (dcut B)" by (rule semi_factor_proj_comp)
  finally show "semi_factor_p (dcut (A \<inter> B))\<cdot>x = semi_factor_p (inf (dcut A) (dcut B))\<cdot>x" .
qed

lemma tcut_joinable: "tcut A\<cdot>t \<Up> tcut B\<cdot>t"
proof (rule joinableI)
  show "tcut A\<cdot>t \<sqsubseteq> tcut (A \<union> B)\<cdot>t" by (intro monofun_cfun_fun tcut_mono) auto
  show "tcut B\<cdot>t \<sqsubseteq> tcut (A \<union> B)\<cdot>t" by (intro monofun_cfun_fun tcut_mono) auto
qed

lemma tcut_join: "tcut A\<cdot>t \<squnion> tcut B\<cdot>t = tcut (A \<union> B)\<cdot>t"
  for t :: "('a, 'b::bounded_complete) tuple"
proof (rule tuple_eqI)
  fix a
  have "tget (tcut A\<cdot>t \<squnion> tcut B\<cdot>t) a = tget (tcut A\<cdot>t) a \<squnion> tget (tcut B\<cdot>t) a"
    by (subst tget_join[OF tcut_joinable]) simp
  thus "(tcut A\<cdot>t \<squnion> tcut B\<cdot>t)\<langle>a\<rangle> = (tcut (A \<union> B)\<cdot>t)\<langle>a\<rangle>"
    by (cases "a \<in> A"; cases "a \<in> B") (simp_all add: tcut_tget)
qed

lemma semi_factor_p_sup:
  "semi_factor_p (sup F G)\<cdot>x = semi_factor_p F\<cdot>x \<squnion> semi_factor_p G\<cdot>x"
  by (simp add: semi_factor_p.rep_eq sup_semi_factor.rep_eq p_sup_join)

lemma semi_factor_p_bot: "semi_factor_p bot = \<bottom>"
  by (rule cfun_eqI)
     (simp add: semi_factor_p.rep_eq bot_semi_factor.rep_eq stable_subdom_p.rep_eq
                bot_stable_subdom.rep_eq p_bot)

lemma dcut_sup: "dcut (A \<union> B) = sup (dcut A) (dcut B)"
proof (rule semi_factor_eqI, rule cfun_eqI)
  fix x
  have "semi_factor_p (dcut (A \<union> B))\<cdot>x = tcut A\<cdot>x \<squnion> tcut B\<cdot>x"
    by (simp add: semi_factor_p_dcut tcut_join)
  also have "... = semi_factor_p (sup (dcut A) (dcut B))\<cdot>x"
    by (simp add: semi_factor_p_sup semi_factor_p_dcut)
  finally show "semi_factor_p (dcut (A \<union> B))\<cdot>x = semi_factor_p (sup (dcut A) (dcut B))\<cdot>x" .
qed

lemma dcut_bot: "dcut {} = bot"
  by (rule semi_factor_eqI) (simp add: semi_factor_p_dcut semi_factor_p_bot)

end