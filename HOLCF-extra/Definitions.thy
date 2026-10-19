theory Definitions imports HOLCF begin

lemma (in pcpo) lub_empty[simp]: "{} <<| \<bottom>" by (simp add: is_lub_def)

context po begin

definition below_strict (infix \<open>\<sqsubset>\<close> 50) where "a \<sqsubset> b = (a \<sqsubseteq> b \<and> \<not>(b \<sqsubseteq> a))"

text \<open>Being a least element, without assuming one exists.\<close>

definition is_bot :: "'a \<Rightarrow> bool" where "is_bot x \<longleftrightarrow> (\<forall>y. x \<sqsubseteq> y)"

text \<open>Classical rules for @{const is_bot} are stated at \<open>po\<close> level only and never mention \<open>\<bottom>\<close>
  (see @{text is_bot_iff} below for why).\<close>

lemma is_botI [intro]: "(\<And>y. x \<sqsubseteq> y) \<Longrightarrow> is_bot x"
  by (simp add: is_bot_def)

lemma is_botD [dest]: "is_bot x \<Longrightarrow> x \<sqsubseteq> y"
  by (simp add: is_bot_def)

text \<open>Stated as a fact rather than a \<open>sublocale\<close>: a sublocale into a locale with derived constants
  breaks later subclasses whose assumptions need a finer sort (Isabelle class bug).\<close>

lemma below_order: "class.order below below_strict"
  by unfold_locales (fact below_strict_def below_refl below_trans below_antisym)+

theorem lub_below_iff': "A <<| a \<Longrightarrow> a \<sqsubseteq> x \<longleftrightarrow> (\<forall>y \<in> A. y \<sqsubseteq> x)"
  using is_lub_below_iff is_ub_def by blast

theorem lub_below_iff_b: "f ` A <<| a \<Longrightarrow> a \<sqsubseteq> x \<longleftrightarrow> (\<forall>y \<in> A. f y \<sqsubseteq> x)"
  using lub_below_iff' by blast

definition join (infixl \<open>\<squnion>\<close> 65) where
  "a \<squnion> b \<equiv> lub {a, b}"

lemma join_sym: "a \<squnion> b = b \<squnion> a"
  by (simp add: join_def insert_commute)

lemma join_idem[simp]: "a \<squnion> a = a"
  by (simp add: join_def)

lemma join_absorb: "a \<sqsubseteq> b \<Longrightarrow> a \<squnion> b = b"
  by (simp add: join_def lub_bin)

lemma join_absorb2: "a \<sqsubseteq> b \<Longrightarrow> b \<squnion> a = b"
  by (simp add: join_sym join_absorb)

lemma bin_join_ex_symm: "{a, b} <<| z \<longleftrightarrow> {b, a} <<| z"
  unfolding insert_commute ..

lemma binLubI:
  assumes "a \<sqsubseteq> w" "b \<sqsubseteq> w" "\<And>z. a \<sqsubseteq> z \<Longrightarrow> b \<sqsubseteq> z \<Longrightarrow> w \<sqsubseteq> z"
  shows "{a, b} <<| w"
  unfolding is_lub_def is_ub_def using assms by blast

definition "is_glb A a \<equiv> \<forall>b. (\<forall>x \<in> A. b \<sqsubseteq> x) \<longleftrightarrow> b \<sqsubseteq> a"

definition "glb A \<equiv> THE a. is_glb A a"

lemma is_glbI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> a \<sqsubseteq> x"
    and "\<And>b. \<forall>x \<in> A. b \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> a"
  shows "is_glb A a"
  unfolding is_glb_def
  using assms
  by (auto simp add: is_glb_def dest: below_trans)

lemma is_glb_unique: "is_glb A a \<Longrightarrow> is_glb A b \<Longrightarrow> a = b"
  unfolding is_glb_def by (blast intro: below_antisym)

lemma is_glb_glb: "is_glb A a \<Longrightarrow> is_glb A (glb A)"
  unfolding glb_def by (rule theI[OF _ is_glb_unique])

lemma glb_eqI: "is_glb A a \<Longrightarrow> glb A = a"
  using is_glb_unique[OF is_glb_glb] .

lemma is_glb_below: "is_glb S a \<Longrightarrow> x \<in> S \<Longrightarrow> a \<sqsubseteq> x"
  unfolding is_glb_def by auto

lemma is_glb_greatest: "is_glb S a \<Longrightarrow> (\<forall>x \<in> S. b \<sqsubseteq> x) \<Longrightarrow> b \<sqsubseteq> a"
  unfolding is_glb_def by auto

definition meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl \<open>\<sqinter>\<close> 70)
  where "a \<sqinter> b = glb {a, b}"

lemma meet_idem: "a \<sqinter> a = a"
  unfolding meet_def
  by (rule glb_eqI) (simp add: is_glb_def)

lemma meet_sym: "a \<sqinter> b = b \<sqinter> a"
  by (simp add: meet_def insert_commute)

lemma meet_absorb: "a \<sqsubseteq> b \<Longrightarrow> a \<sqinter> b = a"
  unfolding meet_def
  by (rule glb_eqI) (auto simp add: is_glb_def dest: below_trans)

lemma meet_absorb2: "a \<sqsubseteq> b \<Longrightarrow> b \<sqinter> a = a"
  by (simp add: meet_sym meet_absorb)

end

text \<open>Binder syntax for @{const glb}, mirroring HOLCF's \<open>\<Squnion>\<close> for @{const lub}.  HOL's \<open>\<Sqinter>\<close> for
  \<open>Inf\<close> lives in the bundle \<open>lattice_syntax\<close>, which \<open>Main\<close> leaves switched off.\<close>

syntax (ASCII)
  "_BGlb" :: "[pttrn, 'a set, 'b] \<Rightarrow> 'b" (\<open>(\<open>indent=3 notation=\<open>binder GLB\<close>\<close>GLB _:_./ _)\<close> [0,0, 10] 10)

syntax
  "_BGlb" :: "[pttrn, 'a set, 'b] \<Rightarrow> 'b" (\<open>(\<open>indent=3 notation=\<open>binder \<Sqinter>\<close>\<close>\<Sqinter>_\<in>_./ _)\<close> [0,0, 10] 10)

syntax_consts
  "_BGlb" \<rightleftharpoons> glb

translations
  "GLB x:A. t" \<rightleftharpoons> "CONST glb ((\<lambda>x. t) ` A)"

context po
begin

abbreviation Glb  (binder \<open>\<Sqinter>\<close> 10)
  where "\<Sqinter>n. t n \<equiv> glb (range t)"

end

text \<open>A constant defined in a class context exists twice: at locale level (\<open>po.meet (\<sqsubseteq>)\<close>) and
  at class level (\<open>(\<sqinter>)\<close>), the latter introduced by a kernel definition stored as
  \<open>po_class.meet_dict: (\<sqinter>) \<equiv> po.meet (\<sqsubseteq>)\<close>.  Collected here (turned around) for use as
  \<open>rewrites\<close> when interpreting our class locales at concrete types, whose obligations and
  facts otherwise come out in locale vocabulary.\<close>

named_theorems class_locale_eqs \<open>locale-level vs class-level copies of class-context constants\<close>

lemmas po_locale_eqs [class_locale_eqs] =
  po_class.is_ub_dict[symmetric] po_class.is_lub_dict[symmetric] po_class.lub_dict[symmetric]
  po_class.is_glb_dict[symmetric] po_class.glb_dict[symmetric]
  po_class.meet_dict[symmetric] po_class.join_dict[symmetric]

text \<open>In a pcpo, @{const is_bot} is just \<open>x = \<bottom>\<close>.  Deliberately \<open>[simp]\<close> only, not \<open>[iff]\<close>: as a
  classical rule it is tried by @{method blast}, which ignores sort constraints during search and
  so applies this \<open>pcpo\<close>-only equation at merely \<open>po\<close> types, blowing up on goals as simple as an
  \<open>obtain\<close> of a non-least element.\<close>

lemma is_bot_iff [simp]: "is_bot (x::'a::pcpo) \<longleftrightarrow> x = \<bottom>"
  by (auto simp: is_bot_def intro: bottomI)

text \<open>The safe half as a classical rule: it only consumes an existing (hence well-sorted)
  hypothesis \<open>x = \<bottom>\<close>, never produces one.\<close>

lemma bottom_is_bot [dest]: "x = \<bottom> \<Longrightarrow> is_bot x"
  by simp

text \<open>For tableau provers, which substitute equations \<open>x = \<bottom>\<close> away and are then left with this.
  Unsafe \<open>[intro]\<close> only: as \<open>[intro!]\<close> it hangs @{method blast} on \<open>po\<close>-level goals (blast's own
  unknowns get committed to an ill-sorted \<open>\<bottom>\<close>).\<close>

lemma is_bot_bottom [intro]: "is_bot (\<bottom>::'a::pcpo)"
  by simp

lemma (in pcpo) join_bottom[simp]: "\<bottom> \<squnion> a = a" "a \<squnion> \<bottom> = a"
  by (simp_all add: join_absorb join_absorb2)


lemma obtain_compact_chain:
  fixes x :: "'a::profinite"
  obtains X where "chain X" "\<forall>i. compact (X i)" "x = (\<Squnion>i. X i)"
proof -
  from compact_basis.obtain_principal_chain
  obtain B' where B': "\<forall>i. B' i \<sqsubseteq> B' (Suc i)" "up\<cdot>x = (\<Squnion>i. Rep_compact_basis (B' i))"
    .
  define X' where "X' i = Rep_compact_basis (B' i)" for i
  have "chain X'" unfolding X'_def using B'(1) by (rule compact_basis.ch2ch_principal)
  have upx: "up\<cdot>x = (\<Squnion>i. X' i)" unfolding X'_def by fact
  have "compact (X' i)" for i unfolding X'_def by simp
  obtain X n where upX: "\<forall>i. up\<cdot>(X i) = X' (i + n)"
    and "chain X" and x: "x = (\<Squnion>i. X i)"
    using \<open>chain X'\<close>
  proof (cases rule: up_chain_cases)
    case 1
    then have "(\<Squnion>i. X' i) = \<bottom>" by simp
    with upx show ?thesis by simp
  next
    case (2 X n)
    with upx show ?thesis using that by simp
  qed
  from upX \<open>\<And>i. compact (X' i)\<close> compact_upD have "\<forall>i. compact (X i)" 
    by metis
  from \<open>chain X\<close> this x show ?thesis by (rule that)
qed

lemma compact_induct':
  fixes x :: "'a::profinite"
  assumes adm: "adm P"
  assumes compact: "\<And>xx. compact xx \<Longrightarrow> xx \<sqsubseteq> x \<Longrightarrow> P xx"
  shows "P x"
proof -
  obtain X where X: "chain X" "\<forall>i. compact (X i)" "x = (\<Squnion>i. X i)"
    by (rule obtain_compact_chain)
  from X(1, 3) have "\<And>i. X i \<sqsubseteq> x" using is_ub_thelub by blast
  from X(2) this have "\<And>i. P (X i)" using compact by blast
  with adm[THEN admD, OF X(1)] X(3) show "P x" by presburger
qed

subsection \<open>Step functions\<close>

text \<open>The step function \<open>stepfn c y\<close> is \<open>y\<close> above \<open>c\<close> and \<open>\<bottom>\<close> elsewhere; it is continuous when
  \<open>c\<close> is compact.  It lies below @{term f} exactly when \<open>y \<sqsubseteq> f\<cdot>c\<close>.\<close>

definition "stepfn c y \<equiv> (\<Lambda> x. if c \<sqsubseteq> x then y else \<bottom>)"

lemma monofun_stepfn: "monofun (\<lambda>x::'a::cpo. if c \<sqsubseteq> x then y else \<bottom>)"
  by (rule monofunI) (auto dest: below_trans)

lemma cont_stepfn: "cont (\<lambda>x::'a::cpo. if c \<sqsubseteq> x then y else \<bottom>)" (is "cont ?f") if "compact c"
proof (rule contI2)
  show "monofun ?f" by (rule monofun_stepfn)
  fix Y :: "nat \<Rightarrow> 'a" assume "chain Y" and chain_F: "chain (\<lambda>i. ?f (Y i))"
  show "?f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. ?f (Y i))"
  proof (cases "c \<sqsubseteq> (\<Squnion>i. Y i)")
    case True
    with \<open>compact c\<close> \<open>chain Y\<close> have "\<exists>i. c \<sqsubseteq> Y i" by (rule compactD2)
    then obtain i where i: "c \<sqsubseteq> Y i" ..
    from i \<open>chain Y\<close>[THEN chain_mono] have Y_mono: "i \<le> j \<Longrightarrow> c \<sqsubseteq> Y j" for j
      by (rule below_trans)
    from i have 1: "?f (Y i) = y" by simp
    with Y_mono have "i \<le> j \<Longrightarrow> ?f (Y i) = ?f (Y j)" for j by simp
    then have max: "max_in_chain i (\<lambda>i. ?f (Y i))" by (rule max_in_chainI)
    from maxinch_is_thelub[OF chain_F] this 1 have 1: "(\<Squnion>i. ?f (Y i)) = y"
      by presburger
    from True have 2: "?f (\<Squnion>i. Y i) = y" by simp
    show ?thesis unfolding 1 2 by (rule below_refl)
  next
    case False
    then have 1: "?f (\<Squnion>i. Y i) = \<bottom>" by simp
    show ?thesis unfolding 1 by (rule minimal)
  qed
qed

lemma stepfn_beta: "stepfn c y\<cdot>x = (if c \<sqsubseteq> x then y else \<bottom>)" if "compact c"
  unfolding stepfn_def
  by (rule beta_cfun) (rule cont_stepfn[OF that])

lemma stepfn_below_iff: assumes "compact c" shows "stepfn c y \<sqsubseteq> f \<longleftrightarrow> y \<sqsubseteq> f\<cdot>c"
  unfolding cfun_below_iff stepfn_beta[OF assms]
  apply (simp only: minimal split: if_splits)
  by simp (blast intro: monofun_cfun_arg[of c _ f] below_trans[of y "f\<cdot>c"])

end