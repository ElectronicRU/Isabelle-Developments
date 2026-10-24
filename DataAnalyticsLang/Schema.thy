theory Schema
  imports LOD "HOLCF-extra.LowerPD_Representation" "HOLCF-extra.Lattice_Complete"
begin

default_sort "{bifinite, distributive_cpo}"

section \<open>Schemas: presence rules and chase rules\<close>

text \<open>A schema on a row domain consists of presence rules and chase rules.

  A presence rule is triggered by a \<^emph>\<open>decisive\<close> antecedent: a predicate of one part of the row,
  false at bottom and constant above every nonbottom value of that part (so it is decided as soon
  as the part is present, as for presence itself or for \<open>is_na\<close> on a separated sum).  Its consequent
  is any up-closed predicate (presence, maximality, a decided value test).

  A chase rule acts on pairs of rows: when its guard holds of \<open>(x, y)\<close> it raises \<open>x\<close> by a
  contribution computed from \<open>x\<close> and \<open>y\<close>, in the rows with a top adjoined (an incompatible
  contribution is a conflict).  Guards are up-closed and Scott-open.  Functional dependencies
  are chase rules (guard: equal maximal determinants, contribution: the partner's dependent part),
  and so are join columns, which stay uncollapsed: under joint presence each key side is raised by
  the other side transported into its coordinates (a unary rule, ignoring the partner).

  Each presence rule is either \<^emph>\<open>upheld\<close> by every chase rule (one step between conforming rows
  produces a row satisfying it) or \<^emph>\<open>repaired\<close> by a set of functional dependencies among the
  chase rules: their determinants lie inside the trigger part and are forced maximal by the
  antecedent, and the consequent is carried along their determinants and dependents.  A triggered
  row then got its trigger part from a conforming source row, and the repairing dependencies copy the
  source's evidence across.\<close>

datatype 'r presence_rule =
  Presence_Rule (trigger: "'r semi_factor") (antecedent: "'r \<Rightarrow> bool") (consequent: "'r \<Rightarrow> bool")

datatype 'r chase_rule =
  Chase_Rule (guard: "'r \<Rightarrow> 'r \<Rightarrow> bool") (contribution: "'r \<rightarrow> 'r \<rightarrow> 'r top")

subsection \<open>Antecedents and consequents\<close>

definition decisive :: "'r semi_factor \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> bool" where
  "decisive p P \<longleftrightarrow> (\<forall>x. P x = P (x \<downharpoonright> p)) \<and> \<not> P \<bottom> \<and>
    (\<forall>x y. x \<downharpoonright> p \<noteq> \<bottom> \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> P y = P x)"

definition up_closed :: "('r::po \<Rightarrow> bool) \<Rightarrow> bool" where
  "up_closed C \<longleftrightarrow> (\<forall>x y. C x \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> C y)"

lemma decisive_part: "decisive p P \<Longrightarrow> P x = P (x \<downharpoonright> p)"
  unfolding decisive_def by blast

lemma decisive_bot: "decisive p P \<Longrightarrow> \<not> P \<bottom>"
  unfolding decisive_def by blast

lemma decisive_above: "decisive p P \<Longrightarrow> x \<downharpoonright> p \<noteq> \<bottom> \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> P y = P x"
  unfolding decisive_def by blast

lemma decisive_present: "decisive p P \<Longrightarrow> P x \<Longrightarrow> x \<downharpoonright> p \<noteq> \<bottom>"
  unfolding decisive_def by metis

lemma up_closedD: "up_closed C \<Longrightarrow> C x \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> C y"
  unfolding up_closed_def by blast

text \<open>Decisive antecedents are Scott-open, so their negations are admissible; up-closed
  consequents are admissible outright.\<close>

lemma adm_not_decisive:
  assumes P: "decisive p P"
  shows "adm (\<lambda>x. \<not> P x)"
proof (rule admI)
  fix Y assume Y: "chain Y" and nP: "\<forall>i. \<not> P (Y i)"
  show "\<not> P (\<Squnion>i. Y i)"
  proof
    assume lub: "P (\<Squnion>i. Y i)"
    have "(\<Squnion>i. Y i) \<downharpoonright> p \<noteq> \<bottom>" using decisive_present[OF P lub] .
    then have "(\<Squnion>i. Y i \<downharpoonright> p) \<noteq> \<bottom>" using Y by (simp add: contlub_cfun_arg)
    then obtain i where i: "Y i \<downharpoonright> p \<noteq> \<bottom>" by fastforce
    have "P (\<Squnion>i. Y i) = P (Y i)" by (rule decisive_above[OF P i is_ub_thelub[OF Y]])
    with lub nP show False by simp
  qed
qed

lemma adm_up_closed: "up_closed C \<Longrightarrow> adm C"
  by (rule admI) (blast intro: up_closedD is_ub_thelub)

subsection \<open>Guards\<close>

definition open_guard :: "('r \<Rightarrow> 'r \<Rightarrow> bool) \<Rightarrow> bool" where
  "open_guard g \<longleftrightarrow> (\<forall>x y x' y'. g x y \<longrightarrow> x \<sqsubseteq> x' \<longrightarrow> y \<sqsubseteq> y' \<longrightarrow> g x' y') \<and>
    (\<forall>X Y. chain X \<longrightarrow> chain Y \<longrightarrow> g (\<Squnion>i. X i) (\<Squnion>i. Y i) \<longrightarrow> (\<exists>i. g (X i) (Y i)))"

lemma open_guard_up: "open_guard g \<Longrightarrow> g x y \<Longrightarrow> x \<sqsubseteq> x' \<Longrightarrow> y \<sqsubseteq> y' \<Longrightarrow> g x' y'"
  unfolding open_guard_def by blast

lemma open_guard_lub:
  "open_guard g \<Longrightarrow> chain X \<Longrightarrow> chain Y \<Longrightarrow> g (\<Squnion>i. X i) (\<Squnion>i. Y i) \<Longrightarrow> \<exists>i. g (X i) (Y i)"
  unfolding open_guard_def by blast

lemma open_guard_lub1: "open_guard g \<Longrightarrow> chain X \<Longrightarrow> g (\<Squnion>i. X i) y \<Longrightarrow> \<exists>i. g (X i) y"
  using open_guard_lub[of g X "\<lambda>_. y"] by simp

lemma open_guard_lub2: "open_guard g \<Longrightarrow> chain Y \<Longrightarrow> g x (\<Squnion>i. Y i) \<Longrightarrow> \<exists>i. g x (Y i)"
  using open_guard_lub[of g "\<lambda>_. x" Y] by simp

text \<open>A maximal part does not move under refinement, and with finitary determinants it is
  compact, so it is reached after finitely many approximants.\<close>

lemma chain_part_reaches:
  assumes C: "chain C" and k: "(\<Squnion>i. C i) \<downharpoonright> p = k" and ck: "compact k"
  obtains n where "\<And>j. n \<le> j \<Longrightarrow> C j \<downharpoonright> p = k"
proof -
  have lub: "k = (\<Squnion>i. C i \<downharpoonright> p)" using k C by (simp add: contlub_cfun_arg)
  have Cp: "chain (\<lambda>i. C i \<downharpoonright> p)" using C by simp
  obtain n where n: "k \<sqsubseteq> C n \<downharpoonright> p"
    using compact_below_lub_iff[OF ck Cp] lub by auto
  have "C j \<downharpoonright> p = k" if j: "n \<le> j" for j
  proof (rule below_antisym)
    show "C j \<downharpoonright> p \<sqsubseteq> k" unfolding lub by (rule is_ub_thelub[OF Cp])
    show "k \<sqsubseteq> C j \<downharpoonright> p" using n monofun_cfun_arg[OF chain_mono[OF C j]] by (rule below_trans)
  qed
  then show ?thesis by (rule that)
qed

subsection \<open>Functional dependencies and key joins as chase rules\<close>

text \<open>A set of rows satisfies a strong functional dependency \<open>a \<rightarrow> b\<close> when rows whose
  \<open>a\<close>-parts are equal and maximal have equal \<open>b\<close>-parts.  A maximal \<open>a\<close>-part does not move under
  refinement.\<close>

definition fd :: "'r semi_factor \<Rightarrow> 'r semi_factor \<Rightarrow> 'r set \<Rightarrow> bool" where
  "fd a b R \<longleftrightarrow>
    (\<forall>x\<in>R. \<forall>y\<in>R. maximal_at a (x \<downharpoonright> a) \<longrightarrow> x \<downharpoonright> a = y \<downharpoonright> a \<longrightarrow> x \<downharpoonright> b = y \<downharpoonright> b)"

lemma fdD:
  "fd a b R \<Longrightarrow> x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> maximal_at a (x \<downharpoonright> a) \<Longrightarrow> x \<downharpoonright> a = y \<downharpoonright> a \<Longrightarrow>
    x \<downharpoonright> b = y \<downharpoonright> b"
  unfolding fd_def by blast

lemma maximal_at_proj_above:
  assumes m: "maximal_at a (x \<downharpoonright> a)" and le: "x \<sqsubseteq> y"
  shows "y \<downharpoonright> a = x \<downharpoonright> a"
proof (rule maximal_at_eq[OF m])
  show "proj a\<cdot>(y \<downharpoonright> a) = y \<downharpoonright> a" by simp
  show "x \<downharpoonright> a \<sqsubseteq> y \<downharpoonright> a" using le by (rule monofun_cfun_arg)
qed

definition fd_guard :: "'r semi_factor \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> bool" where
  "fd_guard a x y \<longleftrightarrow> maximal_at a (x \<downharpoonright> a) \<and> x \<downharpoonright> a = y \<downharpoonright> a"

definition fd_rule :: "'r semi_factor \<Rightarrow> 'r semi_factor \<Rightarrow> 'r chase_rule" where
  "fd_rule a b = Chase_Rule (fd_guard a) (\<Lambda> x y. down\<cdot>(y \<downharpoonright> b))"

lemma fd_rule_simps [simp]:
  "guard (fd_rule a b) = fd_guard a" "contribution (fd_rule a b)\<cdot>x\<cdot>y = down\<cdot>(y \<downharpoonright> b)"
  by (simp_all add: fd_rule_def)

lemma open_fd_guard:
  assumes a: "finitary_semi_factor a"
  shows "open_guard (fd_guard a)"
  unfolding open_guard_def
proof (intro conjI allI impI)
  fix x y x' y' assume g: "fd_guard a x y" and x: "x \<sqsubseteq> x'" and y: "y \<sqsubseteq> y'"
  have m: "maximal_at a (x \<downharpoonright> a)" and eq: "x \<downharpoonright> a = y \<downharpoonright> a" using g unfolding fd_guard_def by auto
  have my: "maximal_at a (y \<downharpoonright> a)" using m eq by simp
  show "fd_guard a x' y'"
    using m maximal_at_proj_above[OF m x] maximal_at_proj_above[OF my y] eq
    by (simp add: fd_guard_def)
next
  fix X Y :: "nat \<Rightarrow> _" assume X: "chain X" and Y: "chain Y" and g: "fd_guard a (\<Squnion>i. X i) (\<Squnion>i. Y i)"
  define k where "k = (\<Squnion>i. X i) \<downharpoonright> a"
  have m: "maximal_at a k" and yk: "(\<Squnion>i. Y i) \<downharpoonright> a = k" using g by (auto simp add: fd_guard_def k_def)
  have ck: "compact k" using a by (simp add: k_def finitary_semi_factor_def finitary_def)
  obtain n where n: "\<And>j. n \<le> j \<Longrightarrow> X j \<downharpoonright> a = k" using chain_part_reaches[OF X k_def[symmetric] ck] by blast
  obtain n' where n': "\<And>j. n' \<le> j \<Longrightarrow> Y j \<downharpoonright> a = k" using chain_part_reaches[OF Y yk ck] by blast
  have "fd_guard a (X (max n n')) (Y (max n n'))" using n n' m by (simp add: fd_guard_def)
  then show "\<exists>i. fd_guard a (X i) (Y i)" by blast
qed

text \<open>A key join between parts \<open>S\<close> and \<open>T\<close> (the two key sides), with transports \<open>\<phi>\<close> from
  \<open>S\<close>-coordinates to \<open>T\<close>-coordinates and \<open>\<psi>\<close> back: under joint presence each side is raised
  by the other.\<close>

definition both_present :: "'r semi_factor \<Rightarrow> 'r semi_factor \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> bool" where
  "both_present S T x y \<longleftrightarrow> x \<downharpoonright> S \<noteq> \<bottom> \<and> x \<downharpoonright> T \<noteq> \<bottom>"

definition key_join_rules :: "'r semi_factor \<Rightarrow> 'r semi_factor \<Rightarrow> ('r \<rightarrow> 'r) \<Rightarrow> ('r \<rightarrow> 'r) \<Rightarrow> 'r chase_rule set" where
  "key_join_rules S T \<phi> \<psi> =
    {Chase_Rule (both_present S T) (\<Lambda> x y. down\<cdot>(\<phi>\<cdot>(x \<downharpoonright> S))),
     Chase_Rule (both_present S T) (\<Lambda> x y. down\<cdot>(\<psi>\<cdot>(x \<downharpoonright> T)))}"

lemma present_lub: "chain X \<Longrightarrow> (\<Squnion>i. X i) \<downharpoonright> S \<noteq> \<bottom> \<Longrightarrow> \<exists>n. \<forall>j\<ge>n. X j \<downharpoonright> S \<noteq> \<bottom>"
proof -
  assume X: "chain X" and p: "(\<Squnion>i. X i) \<downharpoonright> S \<noteq> \<bottom>"
  then have "(\<Squnion>i. X i \<downharpoonright> S) \<noteq> \<bottom>" by (simp add: contlub_cfun_arg)
  then obtain n where n: "X n \<downharpoonright> S \<noteq> \<bottom>" by fastforce
  have "X j \<downharpoonright> S \<noteq> \<bottom>" if "n \<le> j" for j
    using n monofun_cfun_arg[OF chain_mono[OF X that], of "proj S"] by (auto simp add: bottomI)
  then show ?thesis by blast
qed

lemma open_both_present: "open_guard (both_present S T)"
  unfolding open_guard_def
proof (intro conjI allI impI)
  fix x y x' y' assume g: "both_present S T x y" and x: "x \<sqsubseteq> x'"
  have "x \<downharpoonright> S \<sqsubseteq> x' \<downharpoonright> S" "x \<downharpoonright> T \<sqsubseteq> x' \<downharpoonright> T" using x by (simp_all add: monofun_cfun_arg)
  then show "both_present S T x' y'" using g by (auto simp add: both_present_def bottomI)
next
  fix X Y :: "nat \<Rightarrow> _" assume X: "chain X" and g: "both_present S T (\<Squnion>i. X i) (\<Squnion>i. Y i)"
  obtain n where n: "\<forall>j\<ge>n. X j \<downharpoonright> S \<noteq> \<bottom>" using present_lub[OF X] g by (auto simp add: both_present_def)
  obtain n' where n': "\<forall>j\<ge>n'. X j \<downharpoonright> T \<noteq> \<bottom>" using present_lub[OF X] g by (auto simp add: both_present_def)
  have "both_present S T (X (max n n')) (Y (max n n'))" using n n' by (simp add: both_present_def)
  then show "\<exists>i. both_present S T (X i) (Y i)" by blast
qed

lemma open_key_join_rules: "c \<in> key_join_rules S T \<phi> \<psi> \<Longrightarrow> open_guard (guard c)"
  by (auto simp add: key_join_rules_def open_both_present)

subsection \<open>The combined chase step\<close>

text \<open>One step applies every rule to a pair of rows and takes the join of the row and all firing
  contributions, in the complete lattice of rows with a top.\<close>

definition guarded :: "'r chase_rule \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r top" where
  "guarded c x y = (if guard c x y then contribution c\<cdot>x\<cdot>y else \<bottom>)"

definition rules_step :: "'r chase_rule set \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'r top" where
  "rules_step C x y = down\<cdot>x \<squnion> lub ((\<lambda>c. guarded c x y) ` C)"

lemma rules_step_above: "down\<cdot>x \<sqsubseteq> rules_step C x y"
  unfolding rules_step_def by (rule joinableD(1)[OF joinable_lattice])

lemma rules_step_guarded: "c \<in> C \<Longrightarrow> guarded c x y \<sqsubseteq> rules_step C x y"
  unfolding rules_step_def
  by (rule below_trans[OF lattice_lub_upper joinableD(2)[OF joinable_lattice]]) simp

lemma cont_guarded_if:
  assumes up: "\<And>x x'. g x \<Longrightarrow> x \<sqsubseteq> x' \<Longrightarrow> g x'" and op: "\<And>Y. chain Y \<Longrightarrow> g (\<Squnion>i. Y i) \<Longrightarrow> \<exists>i. g (Y i)"
    and f: "cont f"
  shows "cont (\<lambda>x. if g x then f x else \<bottom>)"
proof (rule contI2)
  show "monofun (\<lambda>x. if g x then f x else \<bottom>)"
    by (rule monofunI) (auto dest: up intro: cont2monofunE[OF f])
  fix Y assume Y: "chain Y" and ch: "chain (\<lambda>i. if g (Y i) then f (Y i) else \<bottom>)"
  show "(if g (\<Squnion>i. Y i) then f (\<Squnion>i. Y i) else \<bottom>) \<sqsubseteq> (\<Squnion>i. if g (Y i) then f (Y i) else \<bottom>)"
  proof (cases "g (\<Squnion>i. Y i)")
    case True
    obtain n where n: "g (Y n)" using op[OF Y True] by blast
    have gn: "g (Y (i + n))" for i by (rule up[OF n chain_mono[OF Y]]) simp
    have "f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y (i + n)))"
      by (simp add: cont2contlubE[OF f Y] lub_range_shift[OF ch2ch_cont[OF f Y]])
    also have "\<dots> = (\<Squnion>i. if g (Y (i + n)) then f (Y (i + n)) else \<bottom>)" by (simp add: gn)
    also have "\<dots> = (\<Squnion>i. if g (Y i) then f (Y i) else \<bottom>)" by (rule lub_range_shift[OF ch])
    finally show ?thesis using True by simp
  qed simp
qed

lemma cont_lattice_lub:
  fixes f :: "'i::type \<Rightarrow> 'a::cpo \<Rightarrow> 'b::lattice_complete"
  assumes f: "\<And>i. i \<in> I \<Longrightarrow> cont (f i)"
  shows "cont (\<lambda>x. lub ((\<lambda>i. f i x) ` I))"
proof (rule contI2)
  show "monofun (\<lambda>x. lub ((\<lambda>i. f i x) ` I))"
  proof (rule monofunI, rule lattice_lub_least, rule is_ubI, elim imageE)
    fix x y z i assume xy: "x \<sqsubseteq> y" and z: "z = f i x" and i: "i \<in> I"
    have "f i x \<sqsubseteq> f i y" by (rule cont2monofunE[OF f[OF i] xy])
    also have "f i y \<sqsubseteq> lub ((\<lambda>i. f i y) ` I)" using i by (simp add: lattice_lub_upper)
    finally show "z \<sqsubseteq> lub ((\<lambda>i. f i y) ` I)" by (simp add: z)
  qed
  fix Y assume Y: "chain Y" and ch: "chain (\<lambda>n. lub ((\<lambda>i. f i (Y n)) ` I))"
  show "lub ((\<lambda>i. f i (\<Squnion>n. Y n)) ` I) \<sqsubseteq> (\<Squnion>n. lub ((\<lambda>i. f i (Y n)) ` I))"
  proof (rule lattice_lub_least, rule is_ubI, elim imageE)
    fix z i assume z: "z = f i (\<Squnion>n. Y n)" and i: "i \<in> I"
    have "f i (\<Squnion>n. Y n) = (\<Squnion>n. f i (Y n))" by (rule cont2contlubE[OF f[OF i] Y])
    also have "\<dots> \<sqsubseteq> (\<Squnion>n. lub ((\<lambda>i. f i (Y n)) ` I))"
      by (rule lub_mono[OF ch2ch_cont[OF f[OF i] Y] ch]) (simp add: lattice_lub_upper i)
    finally show "z \<sqsubseteq> (\<Squnion>n. lub ((\<lambda>i. f i (Y n)) ` I))" by (simp add: z)
  qed
qed

lemma cont_lattice_join:
  fixes f g :: "'a::cpo \<Rightarrow> 'b::lattice_complete"
  assumes f: "cont f" and g: "cont g"
  shows "cont (\<lambda>x. f x \<squnion> g x)"
proof -
  have img: "(\<lambda>b. (if b then f else g) x) ` UNIV = {f x, g x}" for x by (auto simp add: UNIV_bool)
  have "(\<lambda>x. f x \<squnion> g x) = (\<lambda>x. lub ((\<lambda>b. (if b then f else g) x) ` UNIV))"
    by (simp add: img lub_eqI[OF joinable_lub[OF joinable_lattice]])
  moreover have "cont (if b then f else g)" for b by (cases b) (simp_all add: f g)
  ultimately show ?thesis using cont_lattice_lub[of UNIV "\<lambda>b. if b then f else g"] by simp
qed

lemma cont_guarded1: "open_guard (guard c) \<Longrightarrow> cont (\<lambda>x. guarded c x y)"
  unfolding guarded_def
  by (rule cont_guarded_if) (auto dest: open_guard_lub1 intro: open_guard_up)

lemma cont_guarded2: "open_guard (guard c) \<Longrightarrow> cont (\<lambda>y. guarded c x y)"
  unfolding guarded_def
  by (rule cont_guarded_if) (auto dest: open_guard_lub2 intro: open_guard_up)

lemma cont_rules_step1: "\<forall>c\<in>C. open_guard (guard c) \<Longrightarrow> cont (\<lambda>x. rules_step C x y)"
  unfolding rules_step_def
  by (intro cont_lattice_join cont_lattice_lub cont_guarded1) simp_all

lemma cont_rules_step2: "\<forall>c\<in>C. open_guard (guard c) \<Longrightarrow> cont (\<lambda>y. rules_step C x y)"
  unfolding rules_step_def
  by (intro cont_lattice_join cont_lattice_lub cont_guarded2) simp_all

definition step_cfun :: "'r chase_rule set \<Rightarrow> 'r \<rightarrow> 'r \<rightarrow> 'r top" where
  "step_cfun C = (\<Lambda> x y. rules_step C x y)"

lemma step_cfun_beta: "\<forall>c\<in>C. open_guard (guard c) \<Longrightarrow> step_cfun C\<cdot>x\<cdot>y = rules_step C x y"
  unfolding step_cfun_def
  by (simp add: cont2cont_LAM cont_rules_step1 cont_rules_step2)

text \<open>Lifted to rows with a top, which is absorbing.\<close>

definition step_top :: "'r chase_rule set \<Rightarrow> 'r top \<rightarrow> 'r top \<rightarrow> 'r top" where
  "step_top C = (\<Lambda> U V. Iftop Top (\<Lambda> u. Iftop Top (step_cfun C\<cdot>u) V) U)"

lemma cont_step_top_inner: "cont (\<lambda>u. Iftop Top (step_cfun C\<cdot>u) V)"
  by (cases V) (simp_all add: Iftop_down Iftop_top)

lemma step_top_down: "step_top C\<cdot>(down\<cdot>u)\<cdot>(down\<cdot>v) = step_cfun C\<cdot>u\<cdot>v"
proof -
  have inner: "(\<Lambda> u. Iftop Top (step_cfun C\<cdot>u) V)\<cdot>w = Iftop Top (step_cfun C\<cdot>w) V" for V w
    by (simp add: cont_step_top_inner)
  have c1: "cont (\<lambda>V. Iftop Top (\<Lambda> u. Iftop Top (step_cfun C\<cdot>u) V) U)" for U
    by (cases U) (simp_all add: Iftop_down Iftop_top inner cont_Iftop)
  have c2: "cont (\<lambda>U. Iftop Top (\<Lambda> u. Iftop Top (step_cfun C\<cdot>u) V) U)" for V
    by (rule cont_Iftop) simp
  show ?thesis
    unfolding step_top_def by (simp add: cont2cont_LAM c1 c2 Iftop_down inner cont_Iftop)
qed

subsection \<open>The chase on the Hoare powerdomain\<close>

text \<open>One round of steps applies the step to every pair of members, as a double bind with no
  explicit sup over the rules.  The chase of \<open>X\<close> is the least \<open>Y\<close> above \<open>X\<close> closed under steps.\<close>

definition chase_steps :: "'r chase_rule set \<Rightarrow> 'r top lower_pd \<rightarrow> 'r top lower_pd" where
  "chase_steps C = (\<Lambda> Y. lower_bind\<cdot>Y\<cdot>(\<Lambda> U. lower_bind\<cdot>Y\<cdot>(\<Lambda> V. {step_top C\<cdot>U\<cdot>V}\<flat>)))"

lemma chase_steps_beta: "chase_steps C\<cdot>Y = lower_bind\<cdot>Y\<cdot>(\<Lambda> U. lower_bind\<cdot>Y\<cdot>(\<Lambda> V. {step_top C\<cdot>U\<cdot>V}\<flat>))"
  by (simp add: chase_steps_def)

definition pd_chase :: "'r chase_rule set \<Rightarrow> 'r top lower_pd \<rightarrow> 'r top lower_pd" where
  "pd_chase C = (\<Lambda> X. fix\<cdot>(\<Lambda> Y. X \<union>\<flat> Y \<union>\<flat> chase_steps C\<cdot>Y))"

lemma pd_chase_beta: "pd_chase C\<cdot>X = fix\<cdot>(\<Lambda> Y. X \<union>\<flat> Y \<union>\<flat> chase_steps C\<cdot>Y)"
  by (simp add: pd_chase_def)

lemma chase_steps_mem:
  assumes U: "U \<in>\<flat> Y" and V: "V \<in>\<flat> Y"
  shows "step_top C\<cdot>U\<cdot>V \<in>\<flat> chase_steps C\<cdot>Y"
proof -
  have "{step_top C\<cdot>U\<cdot>V}\<flat> \<sqsubseteq> lower_bind\<cdot>Y\<cdot>(\<Lambda> V. {step_top C\<cdot>U\<cdot>V}\<flat>)"
    using lower_bind_mem[OF V, of "\<Lambda> V. {step_top C\<cdot>U\<cdot>V}\<flat>"] by simp
  also have "\<dots> \<sqsubseteq> chase_steps C\<cdot>Y"
    using lower_bind_mem[OF U, of "\<Lambda> U. lower_bind\<cdot>Y\<cdot>(\<Lambda> V. {step_top C\<cdot>U\<cdot>V}\<flat>)"]
    by (simp add: chase_steps_beta)
  finally show ?thesis by (simp add: lower_mem_equiv)
qed

lemma chase_steps_below:
  assumes st: "\<And>U V. U \<in>\<flat> Y \<Longrightarrow> V \<in>\<flat> Y \<Longrightarrow> step_top C\<cdot>U\<cdot>V \<in>\<flat> Z"
  shows "chase_steps C\<cdot>Y \<sqsubseteq> Z"
  unfolding chase_steps_beta
proof (rule lower_bind_below, simp)
  fix U assume U: "U \<in>\<flat> Y"
  show "lower_bind\<cdot>Y\<cdot>(\<Lambda> V. {step_top C\<cdot>U\<cdot>V}\<flat>) \<sqsubseteq> Z"
    by (rule lower_bind_below) (simp add: lower_mem_equiv[symmetric] st[OF U])
qed

lemma pd_chase_unfold: "pd_chase C\<cdot>X = X \<union>\<flat> pd_chase C\<cdot>X \<union>\<flat> chase_steps C\<cdot>(pd_chase C\<cdot>X)"
  unfolding pd_chase_beta by (subst fix_eq) simp

lemma pd_chase_above: "X \<sqsubseteq> pd_chase C\<cdot>X"
proof -
  have "X \<sqsubseteq> X \<union>\<flat> pd_chase C\<cdot>X \<union>\<flat> chase_steps C\<cdot>(pd_chase C\<cdot>X)"
    by (rule below_trans[OF lower_plus_below1 lower_plus_below1])
  also have "\<dots> = pd_chase C\<cdot>X" by (rule pd_chase_unfold[symmetric])
  finally show ?thesis .
qed

lemma pd_chase_closed: "chase_steps C\<cdot>(pd_chase C\<cdot>X) \<sqsubseteq> pd_chase C\<cdot>X"
proof -
  have "chase_steps C\<cdot>(pd_chase C\<cdot>X) \<sqsubseteq> X \<union>\<flat> pd_chase C\<cdot>X \<union>\<flat> chase_steps C\<cdot>(pd_chase C\<cdot>X)"
    by (rule lower_plus_below2)
  also have "\<dots> = pd_chase C\<cdot>X" by (rule pd_chase_unfold[symmetric])
  finally show ?thesis .
qed

lemma pd_chase_least: "X \<sqsubseteq> Y \<Longrightarrow> chase_steps C\<cdot>Y \<sqsubseteq> Y \<Longrightarrow> pd_chase C\<cdot>X \<sqsubseteq> Y"
  unfolding pd_chase_beta by (rule fix_least_below) (simp add: lower_plus_least)

subsection \<open>Lawful datasets\<close>

definition obeys :: "'r presence_rule \<Rightarrow> 'r \<Rightarrow> bool" where
  "obeys r x \<longleftrightarrow> (antecedent r x \<longrightarrow> consequent r x)"

definition row_obeys :: "'r presence_rule set \<Rightarrow> 'r \<Rightarrow> bool" where
  "row_obeys R x \<longleftrightarrow> (\<forall>r\<in>R. obeys r x)"

text \<open>Both conditions are stated on compact members, which makes them admissible.  Presence:
  every compact member lies below a conforming member.  Chase: steps between compact members do not
  conflict and land in the set.\<close>

definition obeys_presence_pd :: "'r presence_rule set \<Rightarrow> 'r lower_pd \<Rightarrow> bool" where
  "obeys_presence_pd R X \<longleftrightarrow>
    (\<forall>x. compact x \<longrightarrow> x \<in>\<flat> X \<longrightarrow> (\<exists>l. row_obeys R l \<and> x \<sqsubseteq> l \<and> l \<in>\<flat> X))"

definition chase_closed_pd :: "'r chase_rule set \<Rightarrow> 'r lower_pd \<Rightarrow> bool" where
  "chase_closed_pd C X \<longleftrightarrow> (\<forall>x y. compact x \<longrightarrow> compact y \<longrightarrow> x \<in>\<flat> X \<longrightarrow> y \<in>\<flat> X \<longrightarrow>
    (\<exists>w. w \<in>\<flat> X \<and> rules_step C x y = down\<cdot>w))"

lemma adm_obeys_presence_pd: "adm (obeys_presence_pd (R :: 'r presence_rule set))"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'r lower_pd"
  assume Y: "chain Y" and all: "\<forall>i. obeys_presence_pd R (Y i)"
  show "obeys_presence_pd R (\<Squnion>i. Y i)"
    unfolding obeys_presence_pd_def
  proof (intro allI impI)
    fix x assume x: "compact x" and mem: "x \<in>\<flat> (\<Squnion>i. Y i)"
    obtain i where "x \<in>\<flat> Y i" by (rule lower_mem_compact_lub[OF Y x mem])
    then obtain l where "row_obeys R l" "x \<sqsubseteq> l" "l \<in>\<flat> Y i"
      using all x unfolding obeys_presence_pd_def by blast
    then show "\<exists>l. row_obeys R l \<and> x \<sqsubseteq> l \<and> l \<in>\<flat> (\<Squnion>i. Y i)" using lower_mem_lub[OF Y] by blast
  qed
qed

lemma adm_chase_closed_pd: "adm (chase_closed_pd (C :: 'r chase_rule set))"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'r lower_pd"
  assume Y: "chain Y" and all: "\<forall>i. chase_closed_pd C (Y i)"
  show "chase_closed_pd C (\<Squnion>i. Y i)"
    unfolding chase_closed_pd_def
  proof (intro allI impI)
    fix x y assume x: "compact x" and y: "compact y"
      and mx: "x \<in>\<flat> (\<Squnion>i. Y i)" and my: "y \<in>\<flat> (\<Squnion>i. Y i)"
    obtain i where i: "x \<in>\<flat> Y i" by (rule lower_mem_compact_lub[OF Y x mx])
    obtain j where j: "y \<in>\<flat> Y j" by (rule lower_mem_compact_lub[OF Y y my])
    have "x \<in>\<flat> Y (max i j)" "y \<in>\<flat> Y (max i j)" using lower_mem_chain[OF Y] i j by simp_all
    then obtain w where "w \<in>\<flat> Y (max i j)" "rules_step C x y = down\<cdot>w"
      using all x y unfolding chase_closed_pd_def by blast
    then show "\<exists>w. w \<in>\<flat> (\<Squnion>i. Y i) \<and> rules_step C x y = down\<cdot>w" using lower_mem_lub[OF Y] by blast
  qed
qed

text \<open>With open guards, closure under steps between compact members extends to all members,
  limits included: the steps between the approximants converge to the step between the members.\<close>

theorem chase_closed_pd_mem:
  fixes x y :: 'r
  assumes og: "\<forall>c\<in>C. open_guard (guard c)" and cl: "chase_closed_pd C X"
    and x: "x \<in>\<flat> X" and y: "y \<in>\<flat> X"
  shows "\<exists>w. w \<in>\<flat> X \<and> rules_step C x y = down\<cdot>w"
proof -
  obtain ap :: "nat \<Rightarrow> 'r \<rightarrow> 'r" where ap: "approx_chain ap" using bifinite by blast
  define xs where "xs = (\<lambda>i. ap i\<cdot>x)"
  define ys where "ys = (\<lambda>i. ap i\<cdot>y)"
  have xs: "chain xs" and ys: "chain ys"
    unfolding xs_def ys_def using approx_chain.chain_approx[OF ap] by (simp_all add: ch2ch_Rep_cfunL)
  have lub_x: "(\<Squnion>i. xs i) = x" and lub_y: "(\<Squnion>i. ys i) = y"
    using approx_chain.chain_approx[OF ap] approx_chain.lub_approx[OF ap]
    by (simp_all add: xs_def ys_def flip: contlub_cfun_fun)
  have "\<exists>w. w \<in>\<flat> X \<and> rules_step C (xs i) (ys i) = down\<cdot>w" for i
  proof -
    have "xs i \<in>\<flat> X" "ys i \<in>\<flat> X"
      using x y approx_chain.approx_below[OF ap] by (simp_all add: xs_def ys_def lower_mem_below)
    then show ?thesis using cl approx_chain.compact_approx[OF ap]
      unfolding chase_closed_pd_def xs_def ys_def by blast
  qed
  then obtain ws where ws: "\<And>i. ws i \<in>\<flat> X" and eq: "\<And>i. rules_step C (xs i) (ys i) = down\<cdot>(ws i)"
    by metis
  define s where "s = step_cfun C"
  have s: "s\<cdot>u\<cdot>v = rules_step C u v" for u v by (simp add: s_def step_cfun_beta og)
  have ws_chain: "chain ws"
  proof (rule chainI)
    fix i
    have "s\<cdot>(xs i)\<cdot>(ys i) \<sqsubseteq> s\<cdot>(xs (Suc i))\<cdot>(ys (Suc i))"
      by (intro monofun_cfun_arg monofun_cfun chainE xs ys)
    then show "ws i \<sqsubseteq> ws (Suc i)" by (simp add: s eq)
  qed
  have "rules_step C x y = s\<cdot>(\<Squnion>i. xs i)\<cdot>(\<Squnion>i. ys i)" by (simp add: s lub_x lub_y)
  also have "\<dots> = (\<Squnion>i. s\<cdot>(xs i)\<cdot>(ys i))"
    by (simp add: contlub_cfun_arg[OF xs] lub_APP[OF ch2ch_Rep_cfunR[OF xs] ys])
  also have "\<dots> = (\<Squnion>i. down\<cdot>(ws i))" by (simp add: s eq)
  also have "\<dots> = down\<cdot>(\<Squnion>i. ws i)" by (simp add: contlub_cfun_arg[OF ws_chain])
  finally show ?thesis using admD[OF adm_lower_mem ws_chain] ws by blast
qed

subsection \<open>The chase as the least conforming dataset above\<close>

text \<open>Through \<open>down\<close>, a dataset is closed exactly when one round of steps stays inside it.\<close>

lemma chase_closed_pd_steps:
  assumes og: "\<forall>c\<in>C. open_guard (guard c)"
  shows "chase_closed_pd C X \<longleftrightarrow> chase_steps C\<cdot>(lower_map\<cdot>down\<cdot>X) \<sqsubseteq> lower_map\<cdot>down\<cdot>X"
proof
  assume cl: "chase_closed_pd C X"
  show "chase_steps C\<cdot>(lower_map\<cdot>down\<cdot>X) \<sqsubseteq> lower_map\<cdot>down\<cdot>X"
  proof (rule chase_steps_below)
    fix U V assume "U \<in>\<flat> lower_map\<cdot>down\<cdot>X" "V \<in>\<flat> lower_map\<cdot>down\<cdot>X"
    then obtain u v where u: "u \<in>\<flat> X" "U = down\<cdot>u" and v: "v \<in>\<flat> X" "V = down\<cdot>v"
      by (auto simp add: lower_mem_map_down)
    obtain w where "w \<in>\<flat> X" "rules_step C u v = down\<cdot>w"
      using chase_closed_pd_mem[OF og cl u(1) v(1)] by blast
    then show "step_top C\<cdot>U\<cdot>V \<in>\<flat> lower_map\<cdot>down\<cdot>X"
      by (auto simp add: u v step_top_down step_cfun_beta og lower_mem_map_down)
  qed
next
  assume st: "chase_steps C\<cdot>(lower_map\<cdot>down\<cdot>X) \<sqsubseteq> lower_map\<cdot>down\<cdot>X"
  show "chase_closed_pd C X"
    unfolding chase_closed_pd_def
  proof (intro allI impI)
    fix x y assume x: "x \<in>\<flat> X" and y: "y \<in>\<flat> X"
    have "step_top C\<cdot>(down\<cdot>x)\<cdot>(down\<cdot>y) \<in>\<flat> chase_steps C\<cdot>(lower_map\<cdot>down\<cdot>X)"
      by (intro chase_steps_mem lower_map_mem x y)
    then have "rules_step C x y \<in>\<flat> lower_map\<cdot>down\<cdot>X"
      using st by (auto simp add: lower_mem_equiv step_top_down step_cfun_beta og intro: below_trans)
    then show "\<exists>w. w \<in>\<flat> X \<and> rules_step C x y = down\<cdot>w" by (simp add: lower_mem_map_down)
  qed
qed

theorem pd_chase_fixed_iff:
  assumes og: "\<forall>c\<in>C. open_guard (guard c)"
  shows "pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) = lower_map\<cdot>down\<cdot>X \<longleftrightarrow> chase_closed_pd C X"
proof
  assume fx: "pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) = lower_map\<cdot>down\<cdot>X"
  show "chase_closed_pd C X"
    using pd_chase_closed[of C "lower_map\<cdot>down\<cdot>X"] by (simp add: fx chase_closed_pd_steps[OF og])
next
  assume cl: "chase_closed_pd C X"
  show "pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) = lower_map\<cdot>down\<cdot>X"
  proof (rule below_antisym)
    show "pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) \<sqsubseteq> lower_map\<cdot>down\<cdot>X"
      by (rule pd_chase_least) (simp_all add: chase_closed_pd_steps[OF og, symmetric] cl)
  qed (rule pd_chase_above)
qed

corollary pd_chase_fixed:
  "\<forall>c\<in>C. open_guard (guard c) \<Longrightarrow> chase_closed_pd C X \<Longrightarrow> pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) = lower_map\<cdot>down\<cdot>X"
  by (simp add: pd_chase_fixed_iff)

text \<open>A chase without conflict is again a dataset, and it is closed.\<close>

lemma pd_chase_Top_free:
  assumes og: "\<forall>c\<in>C. open_guard (guard c)" and nT: "\<not> Top \<in>\<flat> pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X)"
  obtains X' where "pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) = lower_map\<cdot>down\<cdot>X'" "X \<sqsubseteq> X'" "chase_closed_pd C X'"
proof -
  obtain X' where eq: "pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) = lower_map\<cdot>down\<cdot>X'"
    using nT by (rule lower_map_down_onto)
  have "X \<sqsubseteq> X'" using pd_chase_above[of "lower_map\<cdot>down\<cdot>X" C] by (simp add: eq lower_map_down_below_iff)
  moreover have "chase_closed_pd C X'"
    using pd_chase_closed[of C "lower_map\<cdot>down\<cdot>X"] by (simp add: eq chase_closed_pd_steps[OF og])
  ultimately show ?thesis using eq that by blast
qed

text \<open>The chase is the least closed dataset above \<open>X\<close>, and it conflicts exactly when there is
  no closed dataset above \<open>X\<close>.\<close>

theorem pd_chase_least_closed:
  assumes og: "\<forall>c\<in>C. open_guard (guard c)" and le: "X \<sqsubseteq> Z" and cl: "chase_closed_pd C Z"
  obtains X' where "pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) = lower_map\<cdot>down\<cdot>X'"
    "X \<sqsubseteq> X'" "chase_closed_pd C X'" "X' \<sqsubseteq> Z"
proof -
  have below: "pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) \<sqsubseteq> lower_map\<cdot>down\<cdot>Z"
    by (rule pd_chase_least)
      (simp_all add: lower_map_down_below_iff le chase_closed_pd_steps[OF og, symmetric] cl)
  have "\<not> Top \<in>\<flat> pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X)"
    using below Top_not_mem_map_down[of Z] by (auto simp add: lower_mem_equiv intro: below_trans)
  then obtain X' where eq: "pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) = lower_map\<cdot>down\<cdot>X'"
    and "X \<sqsubseteq> X'" "chase_closed_pd C X'"
    by (rule pd_chase_Top_free[OF og])
  moreover have "X' \<sqsubseteq> Z" using below by (simp add: eq lower_map_down_below_iff)
  ultimately show ?thesis by (rule that)
qed

theorem pd_chase_conflict_iff:
  assumes og: "\<forall>c\<in>C. open_guard (guard c)"
  shows "Top \<in>\<flat> pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) \<longleftrightarrow> \<not> (\<exists>Z. X \<sqsubseteq> Z \<and> chase_closed_pd C Z)"
proof
  assume T: "Top \<in>\<flat> pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X)"
  show "\<not> (\<exists>Z. X \<sqsubseteq> Z \<and> chase_closed_pd C Z)"
  proof
    assume "\<exists>Z. X \<sqsubseteq> Z \<and> chase_closed_pd C Z"
    then obtain Z where "X \<sqsubseteq> Z" "chase_closed_pd C Z" by blast
    then obtain X' where "pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X) = lower_map\<cdot>down\<cdot>X'"
      by (rule pd_chase_least_closed[OF og])
    with T show False by (simp add: Top_not_mem_map_down)
  qed
next
  assume nc: "\<not> (\<exists>Z. X \<sqsubseteq> Z \<and> chase_closed_pd C Z)"
  show "Top \<in>\<flat> pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X)"
  proof (rule ccontr)
    assume "\<not> Top \<in>\<flat> pd_chase C\<cdot>(lower_map\<cdot>down\<cdot>X)"
    then obtain X' where "X \<sqsubseteq> X'" "chase_closed_pd C X'" by (rule pd_chase_Top_free[OF og])
    with nc show False by blast
  qed
qed

text \<open>Monotonicity is free: the chase is continuous, so conflicts propagate upwards.\<close>

corollary pd_chase_conflict_up:
  "X \<sqsubseteq> Y \<Longrightarrow> Top \<in>\<flat> pd_chase C\<cdot>X \<Longrightarrow> Top \<in>\<flat> pd_chase C\<cdot>Y"
  by (rule lower_mem_below[OF _ below_refl], unfold lower_mem_equiv)
    (erule below_trans, erule monofun_cfun_arg)

subsection \<open>The laws on maximal members\<close>

text \<open>A maximal member absorbs a step exactly when every firing rule contributes below it.  Since
  every member lies below a maximal one and the step is monotone, closure under steps is the same
  as the rules holding at the maximal members.\<close>

lemma rules_step_absorbed:
  "rules_step C m y = down\<cdot>m \<longleftrightarrow> (\<forall>c\<in>C. guard c m y \<longrightarrow> contribution c\<cdot>m\<cdot>y \<sqsubseteq> down\<cdot>m)"
proof (intro iffI ballI impI)
  fix c assume eq: "rules_step C m y = down\<cdot>m" and c: "c \<in> C" and g: "guard c m y"
  show "contribution c\<cdot>m\<cdot>y \<sqsubseteq> down\<cdot>m"
    using rules_step_guarded[OF c, of m y] g by (simp add: eq guarded_def)
next
  assume all: "\<forall>c\<in>C. guard c m y \<longrightarrow> contribution c\<cdot>m\<cdot>y \<sqsubseteq> down\<cdot>m"
  have "lub ((\<lambda>c. guarded c m y) ` C) \<sqsubseteq> down\<cdot>m"
    by (rule lattice_lub_least, rule is_ubI) (auto simp add: guarded_def all)
  then have "rules_step C m y \<sqsubseteq> down\<cdot>m"
    unfolding rules_step_def by (rule join_belowI[OF below_refl])
  then show "rules_step C m y = down\<cdot>m" using rules_step_above by (rule below_antisym)
qed

definition rule_holds :: "'r chase_rule \<Rightarrow> 'r lower_pd \<Rightarrow> bool" where
  "rule_holds c X \<longleftrightarrow>
    (\<forall>m\<in>lower_maximal X. \<forall>y. y \<in>\<flat> X \<longrightarrow> guard c m y \<longrightarrow> contribution c\<cdot>m\<cdot>y \<sqsubseteq> down\<cdot>m)"

theorem chase_closed_pd_iff_rule_holds:
  assumes og: "\<forall>c\<in>C. open_guard (guard c)"
  shows "chase_closed_pd C X \<longleftrightarrow> (\<forall>c\<in>C. rule_holds c X)"
proof
  assume cl: "chase_closed_pd C X"
  show "\<forall>c\<in>C. rule_holds c X"
    unfolding rule_holds_def
  proof (intro ballI allI impI)
    fix c m y assume c: "c \<in> C" and m: "m \<in> lower_maximal X" and y: "y \<in>\<flat> X" and g: "guard c m y"
    have mx: "m \<in>\<flat> X" using m by (simp add: lower_maximal_def)
    obtain w where w: "w \<in>\<flat> X" and eq: "rules_step C m y = down\<cdot>w"
      using chase_closed_pd_mem[OF og cl mx y] by blast
    have "m \<sqsubseteq> w" using rules_step_above[of m C y] by (simp add: eq)
    then have "w = m" using m w by (simp add: lower_maximal_def)
    then have "rules_step C m y = down\<cdot>m" by (simp add: eq)
    then show "contribution c\<cdot>m\<cdot>y \<sqsubseteq> down\<cdot>m" using c g by (simp add: rules_step_absorbed)
  qed
next
  assume all: "\<forall>c\<in>C. rule_holds c X"
  show "chase_closed_pd C X"
    unfolding chase_closed_pd_def
  proof (intro allI impI)
    fix x y assume x: "x \<in>\<flat> X" and y: "y \<in>\<flat> X"
    obtain m where m: "m \<in> lower_maximal X" "x \<sqsubseteq> m" using x by (rule lower_mem_maximal_above)
    have "rules_step C m y = down\<cdot>m"
      using all m(1) y unfolding rules_step_absorbed rule_holds_def by blast
    moreover have "rules_step C x y \<sqsubseteq> rules_step C m y"
      by (rule cont2monofunE[OF cont_rules_step1[OF og] m(2)])
    ultimately have le: "rules_step C x y \<sqsubseteq> down\<cdot>m" by simp
    then obtain w where w: "rules_step C x y = down\<cdot>w" by (cases "rules_step C x y") auto
    have "w \<in>\<flat> X" using le m(1) by (auto simp add: w lower_maximal_def intro: lower_mem_below)
    then show "\<exists>w. w \<in>\<flat> X \<and> rules_step C x y = down\<cdot>w" using w by blast
  qed
qed

text \<open>For a functional dependency the law is the dependency on the maximal members.\<close>

theorem rule_holds_fd: "rule_holds (fd_rule a b) X \<longleftrightarrow> fd a b (lower_maximal X)"
proof
  assume h: "rule_holds (fd_rule a b) X"
  show "fd a b (lower_maximal X)"
    unfolding fd_def
  proof (intro ballI impI)
    fix x y assume x: "x \<in> lower_maximal X" and y: "y \<in> lower_maximal X"
      and m: "maximal_at a (x \<downharpoonright> a)" and eq: "x \<downharpoonright> a = y \<downharpoonright> a"
    have absorbed: "v \<downharpoonright> b \<sqsubseteq> u \<downharpoonright> b"
      if u: "u \<in> lower_maximal X" and v: "v \<in> lower_maximal X" and g: "fd_guard a u v" for u v
    proof -
      have "v \<in>\<flat> X" using v by (simp add: lower_maximal_def)
      then have "v \<downharpoonright> b \<sqsubseteq> u" using h u g by (simp add: rule_holds_def)
      then have "proj b\<cdot>(v \<downharpoonright> b) \<sqsubseteq> u \<downharpoonright> b" by (rule monofun_cfun_arg)
      then show ?thesis by simp
    qed
    have "fd_guard a x y" "fd_guard a y x" using m eq by (auto simp add: fd_guard_def)
    then show "x \<downharpoonright> b = y \<downharpoonright> b"
      using absorbed[OF x y] absorbed[OF y x] by (blast intro: below_antisym)
  qed
next
  assume f: "fd a b (lower_maximal X)"
  show "rule_holds (fd_rule a b) X"
    unfolding rule_holds_def
  proof (intro ballI allI impI)
    fix m y assume m: "m \<in> lower_maximal X" and y: "y \<in>\<flat> X" and g: "guard (fd_rule a b) m y"
    obtain m' where m': "m' \<in> lower_maximal X" "y \<sqsubseteq> m'" using y by (rule lower_mem_maximal_above)
    have ma: "maximal_at a (m \<downharpoonright> a)" and eq: "m \<downharpoonright> a = y \<downharpoonright> a"
      using g unfolding fd_rule_simps fd_guard_def by auto
    have my: "maximal_at a (y \<downharpoonright> a)" using ma unfolding eq .
    have "m' \<downharpoonright> a = y \<downharpoonright> a" by (rule maximal_at_proj_above[OF my m'(2)])
    then have "m \<downharpoonright> a = m' \<downharpoonright> a" using eq by simp
    then have "m \<downharpoonright> b = m' \<downharpoonright> b" by (rule fdD[OF f m(1) m'(1) ma])
    moreover have "y \<downharpoonright> b \<sqsubseteq> m' \<downharpoonright> b" using m'(2) by (rule monofun_cfun_arg)
    ultimately have "y \<downharpoonright> b \<sqsubseteq> m \<downharpoonright> b" by simp
    also have "m \<downharpoonright> b \<sqsubseteq> m" by (rule proj_below)
    finally show "contribution (fd_rule a b)\<cdot>m\<cdot>y \<sqsubseteq> down\<cdot>m" by simp
  qed
qed

corollary fd_maximal_members:
  "\<forall>c\<in>C. open_guard (guard c) \<Longrightarrow> chase_closed_pd C X \<Longrightarrow> fd_rule a b \<in> C \<Longrightarrow>
    fd a b (lower_maximal X)"
  using chase_closed_pd_iff_rule_holds rule_holds_fd by blast

section \<open>The schema locale\<close>

definition upholds :: "'r presence_rule set \<Rightarrow> 'r chase_rule \<Rightarrow> 'r presence_rule \<Rightarrow> bool" where
  "upholds R c r \<longleftrightarrow> (\<forall>x y z. row_obeys R x \<longrightarrow> row_obeys R y \<longrightarrow> guard c x y \<longrightarrow>
    down\<cdot>x \<squnion> contribution c\<cdot>x\<cdot>y = down\<cdot>z \<longrightarrow> obeys r z)"

definition repairs :: "('r semi_factor \<times> 'r semi_factor) set \<Rightarrow> 'r presence_rule \<Rightarrow> bool" where
  "repairs D r \<longleftrightarrow>
    (\<forall>(a, b)\<in>D. a \<sqsubseteq> trigger r \<and> (\<forall>x. antecedent r x \<longrightarrow> maximal_at a (x \<downharpoonright> a))) \<and>
    (\<forall>x y. consequent r y \<longrightarrow> (\<forall>(a, b)\<in>D. y \<downharpoonright> a \<sqsubseteq> x \<downharpoonright> a \<and> y \<downharpoonright> b \<sqsubseteq> x \<downharpoonright> b) \<longrightarrow>
      consequent r x)"

record 'r schema_rules =
  presence :: "'r presence_rule set"
  chase :: "'r chase_rule set"

hide_const (open) schema_rules.truncate

locale schema =
  fixes rules :: "'r schema_rules"
  assumes antecedent_decisive: "r \<in> presence rules \<Longrightarrow> decisive (trigger r) (antecedent r)"
    and consequent_up_closed: "r \<in> presence rules \<Longrightarrow> up_closed (consequent r)"
    and guard_open: "\<forall>c\<in>chase rules. open_guard (guard c)"
    and rule_maintained: "r \<in> presence rules \<Longrightarrow>
      (\<forall>c\<in>chase rules. upholds (presence rules) c r) \<or>
      (\<exists>D. (\<forall>(a, b)\<in>D. fd_rule a b \<in> chase rules) \<and> repairs D r)"
begin

abbreviation presence_rules :: "'r presence_rule set" where "presence_rules \<equiv> presence rules"
abbreviation chase_rules :: "'r chase_rule set" where "chase_rules \<equiv> chase rules"

abbreviation conforming_row :: "'r \<Rightarrow> bool" where
  "conforming_row \<equiv> row_obeys presence_rules"

definition conforms :: "'r lower_pd \<Rightarrow> bool" where
  "conforms X \<longleftrightarrow> obeys_presence_pd presence_rules X \<and> chase_closed_pd chase_rules X"

lemma conforming_row_bot: "conforming_row \<bottom>"
  unfolding row_obeys_def obeys_def by (blast dest: decisive_bot[OF antecedent_decisive])

lemma adm_conforming_row: "adm conforming_row"
  unfolding row_obeys_def obeys_def imp_conv_disj
  by (intro adm_ball adm_disj adm_not_decisive[OF antecedent_decisive]
      adm_up_closed[OF consequent_up_closed])

text \<open>Lawful rows are closed under compatible joins: a triggered antecedent of the join is
  decided by the joinand whose trigger part is present, and that joinand's consequent goes up.\<close>

lemma conforming_row_join:
  assumes x: "conforming_row x" and y: "conforming_row y" and j: "x \<Up> y"
  shows "conforming_row (x \<squnion> y)"
  unfolding row_obeys_def obeys_def
proof (intro ballI impI)
  fix r assume r: "r \<in> presence_rules" and P: "antecedent r (x \<squnion> y)"
  note D = antecedent_decisive[OF r] and C = consequent_up_closed[OF r]
  have "(x \<squnion> y) \<downharpoonright> trigger r \<noteq> \<bottom>" by (rule decisive_present[OF D P])
  then have "x \<downharpoonright> trigger r \<noteq> \<bottom> \<or> y \<downharpoonright> trigger r \<noteq> \<bottom>" by (auto simp add: proj_join[OF j])
  then show "consequent r (x \<squnion> y)"
  proof
    assume "x \<downharpoonright> trigger r \<noteq> \<bottom>"
    then have "antecedent r x" using P decisive_above[OF D _ joinableD(1)[OF j]] by blast
    then have "consequent r x" using x r by (simp add: row_obeys_def obeys_def)
    then show ?thesis by (rule up_closedD[OF C _ joinableD(1)[OF j]])
  next
    assume "y \<downharpoonright> trigger r \<noteq> \<bottom>"
    then have "antecedent r y" using P decisive_above[OF D _ joinableD(2)[OF j]] by blast
    then have "consequent r y" using y r by (simp add: row_obeys_def obeys_def)
    then show ?thesis by (rule up_closedD[OF C _ joinableD(2)[OF j]])
  qed
qed

lemma adm_conforms: "adm conforms"
  unfolding conforms_def by (intro adm_conj adm_obeys_presence_pd adm_chase_closed_pd)

theorem conforms_chase_fixed: "conforms X \<Longrightarrow> pd_chase chase_rules\<cdot>(lower_map\<cdot>down\<cdot>X) = lower_map\<cdot>down\<cdot>X"
  unfolding conforms_def using pd_chase_fixed[OF guard_open] by blast

corollary conforms_fd:
  "conforms X \<Longrightarrow> fd_rule a b \<in> chase_rules \<Longrightarrow> fd a b (lower_maximal X)"
  unfolding conforms_def using fd_maximal_members[OF guard_open] by blast

lemma conforms_iff_rule_holds:
  "conforms X \<longleftrightarrow> obeys_presence_pd presence_rules X \<and> (\<forall>c\<in>chase_rules. rule_holds c X)"
  unfolding conforms_def by (simp add: chase_closed_pd_iff_rule_holds[OF guard_open])

end

end
