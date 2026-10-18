theory Chase
  imports LOD
begin

default_sort "{bifinite, distributive_cpo}"

section \<open>The chase for one functional dependency\<close>

text \<open>A first step towards the schema layer.  Rows live in a bounded complete domain; the two
  sides of a strong functional dependency \<open>a \<rightarrow> b\<close> are semi-factors of the row domain.  A set of
  rows satisfies the dependency when rows whose \<open>a\<close>-parts are equal and maximal have equal
  \<open>b\<close>-parts.

  The chase is defined without derivations.  A tuple over a set of rows \<open>X\<close> is a function on
  rows (only its values on \<open>X\<close> matter); it is \<^emph>\<open>closed\<close> when it lies above the identity on \<open>X\<close>
  and its image satisfies the dependency.  \<open>X\<close> is consistent when some closed tuple exists, and
  then the chase is the least closed tuple: closed tuples are closed under nonempty pointwise
  meets.  The central result is monotonicity in the Hoare (lower) order: below a consistent set,
  every set is consistent, and the chase of a row stays below the chase of every row above it.
  Only the Hoare order is ever used: the chase depends on the maximal rows alone.\<close>

subsection \<open>Stable deflations preserve nonempty meets\<close>

lemma (in stable_defl) glb_image:
  assumes ne: "S \<noteq> {}"
  shows "d\<cdot>(glb S) = glb ((\<lambda>x. d\<cdot>x) ` S)"
proof (rule below_antisym)
  have ne': "(\<lambda>x. d\<cdot>x) ` S \<noteq> {}" using ne by simp
  show "d\<cdot>(glb S) \<sqsubseteq> glb ((\<lambda>x. d\<cdot>x) ` S)"
    using ne' by (rule glb_greatest) (auto intro: monofun_cfun_arg glb_below)
  obtain s where s: "s \<in> S" using ne by blast
  have "glb ((\<lambda>x. d\<cdot>x) ` S) \<sqsubseteq> d\<cdot>s" using s by (simp add: glb_below)
  then have fixed: "d\<cdot>(glb ((\<lambda>x. d\<cdot>x) ` S)) = glb ((\<lambda>x. d\<cdot>x) ` S)" by (rule lower_fixed)
  have "glb ((\<lambda>x. d\<cdot>x) ` S) \<sqsubseteq> glb S"
  proof (rule glb_greatest[OF ne], intro ballI)
    fix t assume "t \<in> S"
    then have "glb ((\<lambda>x. d\<cdot>x) ` S) \<sqsubseteq> d\<cdot>t" by (simp add: glb_below)
    then show "glb ((\<lambda>x. d\<cdot>x) ` S) \<sqsubseteq> t" using below by (rule below_trans)
  qed
  then have "d\<cdot>(glb ((\<lambda>x. d\<cdot>x) ` S)) \<sqsubseteq> d\<cdot>(glb S)" by (rule monofun_cfun_arg)
  then show "glb ((\<lambda>x. d\<cdot>x) ` S) \<sqsubseteq> d\<cdot>(glb S)" by (simp only: fixed)
qed

lemma glb_semi_factor_proj: "S \<noteq> {} \<Longrightarrow> glb S \<downharpoonright> a = glb ((\<lambda>x. x \<downharpoonright> a) ` S)"
  by (rule stable_defl.glb_image[OF semi_factor_defl.axioms(1)[OF semi_factor_defl_semi_factor_p]])

lemma glb_singleton: "glb {x} = x"
  by (rule glb_eqI) (simp add: is_glb_def)

text \<open>A maximal \<open>a\<close>-part does not move under refinement.\<close>

lemma maximal_at_proj_above:
  assumes m: "maximal_at a (x \<downharpoonright> a)" and le: "x \<sqsubseteq> y"
  shows "y \<downharpoonright> a = x \<downharpoonright> a"
proof (rule maximal_at_eq[OF m])
  show "proj a\<cdot>(y \<downharpoonright> a) = y \<downharpoonright> a" by simp
  show "x \<downharpoonright> a \<sqsubseteq> y \<downharpoonright> a" using le by (rule monofun_cfun_arg)
qed

subsection \<open>Dependencies, closed tuples and the chase\<close>

definition fd :: "'r semi_factor \<Rightarrow> 'r semi_factor \<Rightarrow> 'r set \<Rightarrow> bool" where
  "fd a b R \<longleftrightarrow>
    (\<forall>x\<in>R. \<forall>y\<in>R. maximal_at a (x \<downharpoonright> a) \<longrightarrow> x \<downharpoonright> a = y \<downharpoonright> a \<longrightarrow> x \<downharpoonright> b = y \<downharpoonright> b)"

lemma fdD:
  "fd a b R \<Longrightarrow> x \<in> R \<Longrightarrow> y \<in> R \<Longrightarrow> maximal_at a (x \<downharpoonright> a) \<Longrightarrow> x \<downharpoonright> a = y \<downharpoonright> a \<Longrightarrow>
    x \<downharpoonright> b = y \<downharpoonright> b"
  unfolding fd_def by blast

definition fd_closed :: "'r semi_factor \<Rightarrow> 'r semi_factor \<Rightarrow> 'r set \<Rightarrow> ('r \<Rightarrow> 'r) \<Rightarrow> bool" where
  "fd_closed a b X t \<longleftrightarrow> (\<forall>x\<in>X. x \<sqsubseteq> t x) \<and> fd a b (t ` X)"

definition fd_consistent :: "'r semi_factor \<Rightarrow> 'r semi_factor \<Rightarrow> 'r set \<Rightarrow> bool" where
  "fd_consistent a b X \<longleftrightarrow> (\<exists>t. fd_closed a b X t)"

definition chase :: "'r semi_factor \<Rightarrow> 'r semi_factor \<Rightarrow> 'r set \<Rightarrow> 'r \<Rightarrow> 'r" where
  "chase a b X = (\<lambda>x. glb ((\<lambda>t. t x) ` {t. fd_closed a b X t}))"

text \<open>The hardest step: closed tuples are closed under nonempty pointwise meets.  A maximal
  \<open>a\<close>-part of the meet is the \<open>a\<close>-part of every member, so the members' dependency applies,
  and the \<open>b\<close>-parts pass through the meet because the semi-factor preserves meets.\<close>

lemma fd_closed_glb:
  assumes ne: "T \<noteq> {}" and cl: "\<And>t. t \<in> T \<Longrightarrow> fd_closed a b X t"
  shows "fd_closed a b X (\<lambda>x. glb ((\<lambda>t. t x) ` T))" (is "fd_closed a b X ?m")
  unfolding fd_closed_def
proof (intro conjI ballI)
  fix x assume x: "x \<in> X"
  have "\<forall>u\<in>(\<lambda>t. t x) ` T. x \<sqsubseteq> u" using cl x by (auto simp add: fd_closed_def)
  then show "x \<sqsubseteq> ?m x" using ne by (simp add: glb_greatest)
next
  have ne': "(\<lambda>t. t x) ` T \<noteq> {}" for x using ne by simp
  have m_below: "?m x \<sqsubseteq> t x" if "t \<in> T" for t x using that by (simp add: glb_below)
  have m_b: "?m x \<downharpoonright> b = glb ((\<lambda>t. t x \<downharpoonright> b) ` T)" for x
    by (simp add: glb_semi_factor_proj[OF ne'] image_image)
  show "fd a b (?m ` X)"
    unfolding fd_def
  proof (intro ballI impI, elim imageE)
    fix x x' u u' assume u: "u = ?m x" and x: "x \<in> X" and u': "u' = ?m x'" and x': "x' \<in> X"
    assume mx: "maximal_at a (u \<downharpoonright> a)" and eq: "u \<downharpoonright> a = u' \<downharpoonright> a"
    have b_eq: "t x \<downharpoonright> b = t x' \<downharpoonright> b" if t: "t \<in> T" for t
    proof -
      have tx: "t x \<downharpoonright> a = u \<downharpoonright> a" unfolding u by (rule maximal_at_proj_above[OF mx[unfolded u] m_below[OF t]])
      have mx': "maximal_at a (u' \<downharpoonright> a)" using mx eq by simp
      have tx': "t x' \<downharpoonright> a = u' \<downharpoonright> a"
        unfolding u' by (rule maximal_at_proj_above[OF mx'[unfolded u'] m_below[OF t]])
      have "fd a b (t ` X)" using cl[OF t] by (simp add: fd_closed_def)
      then show ?thesis
        by (rule fdD) (use x x' tx tx' mx eq in simp_all)
    qed
    have "glb ((\<lambda>t. t x \<downharpoonright> b) ` T) = glb ((\<lambda>t. t x' \<downharpoonright> b) ` T)"
      by (rule arg_cong[where f = glb], rule image_cong[OF refl b_eq])
    then show "u \<downharpoonright> b = u' \<downharpoonright> b" by (simp add: u u' m_b)
  qed
qed

lemma chase_closed: "fd_consistent a b X \<Longrightarrow> fd_closed a b X (chase a b X)"
  unfolding chase_def fd_consistent_def by (rule fd_closed_glb) auto

lemma chase_least: "fd_closed a b X t \<Longrightarrow> chase a b X x \<sqsubseteq> t x"
  by (simp add: chase_def glb_below)

lemma chase_above: "fd_consistent a b X \<Longrightarrow> x \<in> X \<Longrightarrow> x \<sqsubseteq> chase a b X x"
  using chase_closed[of a b X] unfolding fd_closed_def by blast

lemma chase_fd: "fd_consistent a b X \<Longrightarrow> fd a b (chase a b X ` X)"
  using chase_closed[of a b X] unfolding fd_closed_def by blast

subsection \<open>Monotonicity in the Hoare order\<close>

definition lower_below :: "'r set \<Rightarrow> 'r set \<Rightarrow> bool" where
  "lower_below X Y \<longleftrightarrow> (\<forall>x\<in>X. \<exists>y\<in>Y. x \<sqsubseteq> y)"

text \<open>Below a consistent \<open>Y\<close>, the meet of the chased rows of \<open>Y\<close> above a row \<open>x\<close> (nonempty by
  the Hoare order) is a closed tuple over \<open>X\<close>: a maximal \<open>a\<close>-part of the meet is that of every
  chased row above, and the chased rows of \<open>Y\<close> agree on their \<open>b\<close>-parts.\<close>

theorem chase_mono:
  assumes le: "lower_below X Y" and cY: "fd_consistent a b Y"
  shows "fd_consistent a b X"
    and "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> chase a b X x \<sqsubseteq> chase a b Y y"
proof -
  define c where "c = chase a b Y"
  define U where "U x = {y \<in> Y. x \<sqsubseteq> y}" for x
  define t where "t x = glb (c ` U x)" for x
  have U_ne: "U x \<noteq> {}" if "x \<in> X" for x using le that by (auto simp add: lower_below_def U_def)
  have cU_ne: "c ` U x \<noteq> {}" if "x \<in> X" for x using U_ne[OF that] by simp
  have c_fd: "fd a b (c ` Y)" unfolding c_def by (rule chase_fd[OF cY])
  have t_below: "t x \<sqsubseteq> c y" if "y \<in> U x" for x y using that by (simp add: t_def glb_below)
  have closed: "fd_closed a b X t"
    unfolding fd_closed_def
  proof (intro conjI ballI)
    fix x assume x: "x \<in> X"
    have "\<forall>u\<in>c ` U x. x \<sqsubseteq> u"
      using chase_above[OF cY] by (auto simp add: U_def c_def intro: below_trans)
    then show "x \<sqsubseteq> t x" unfolding t_def using cU_ne[OF x] by (simp add: glb_greatest)
  next
    show "fd a b (t ` X)"
      unfolding fd_def
    proof (intro ballI impI, elim imageE)
      fix x x' u u' assume u: "u = t x" and x: "x \<in> X" and u': "u' = t x'" and x': "x' \<in> X"
      assume mx: "maximal_at a (u \<downharpoonright> a)" and eq: "u \<downharpoonright> a = u' \<downharpoonright> a"
      have mx': "maximal_at a (u' \<downharpoonright> a)" using mx eq by simp
      have ca: "c y \<downharpoonright> a = u \<downharpoonright> a" if "y \<in> U x" for y
        unfolding u by (rule maximal_at_proj_above[OF mx[unfolded u] t_below[OF that]])
      have ca': "c y' \<downharpoonright> a = u' \<downharpoonright> a" if "y' \<in> U x'" for y'
        unfolding u' by (rule maximal_at_proj_above[OF mx'[unfolded u'] t_below[OF that]])
      have cb: "c y \<downharpoonright> b = c y' \<downharpoonright> b" if y: "y \<in> U x" and y': "y' \<in> U x'" for y y'
      proof (rule fdD[OF c_fd])
        show "c y \<in> c ` Y" "c y' \<in> c ` Y" using y y' by (simp_all add: U_def)
        show "maximal_at a (c y \<downharpoonright> a)" using mx by (simp add: ca[OF y])
        show "c y \<downharpoonright> a = c y' \<downharpoonright> a" using eq by (simp add: ca[OF y] ca'[OF y'])
      qed
      obtain y0 where y0: "y0 \<in> U x" using U_ne[OF x] by blast
      obtain y0' where y0': "y0' \<in> U x'" using U_ne[OF x'] by blast
      have img: "(\<lambda>y. c y \<downharpoonright> b) ` U x = {c y0 \<downharpoonright> b}"
        using y0 cb[OF _ y0'] cb[OF y0 y0'] by auto
      have img': "(\<lambda>y. c y \<downharpoonright> b) ` U x' = {c y0 \<downharpoonright> b}"
      proof (rule set_eqI, rule iffI)
        fix v assume "v \<in> (\<lambda>y. c y \<downharpoonright> b) ` U x'"
        then obtain y' where "y' \<in> U x'" and "v = c y' \<downharpoonright> b" by blast
        then show "v \<in> {c y0 \<downharpoonright> b}" using cb[OF y0] by simp
      next
        fix v assume "v \<in> {c y0 \<downharpoonright> b}"
        then have "v = c y0' \<downharpoonright> b" using cb[OF y0 y0'] by simp
        then show "v \<in> (\<lambda>y. c y \<downharpoonright> b) ` U x'" by (rule rev_image_eqI[OF y0'])
      qed
      have "u \<downharpoonright> b = glb ((\<lambda>y. c y \<downharpoonright> b) ` U x)"
        unfolding u t_def by (simp add: glb_semi_factor_proj[OF cU_ne[OF x]] image_image)
      also have "\<dots> = glb ((\<lambda>y. c y \<downharpoonright> b) ` U x')" by (simp only: img img')
      also have "\<dots> = u' \<downharpoonright> b"
        unfolding u' t_def by (simp add: glb_semi_factor_proj[OF cU_ne[OF x']] image_image)
      finally show "u \<downharpoonright> b = u' \<downharpoonright> b" .
    qed
  qed
  then show "fd_consistent a b X" by (auto simp add: fd_consistent_def)
  assume x: "x \<in> X" and y: "y \<in> Y" and le: "x \<sqsubseteq> y"
  have "chase a b X x \<sqsubseteq> t x" using closed by (rule chase_least)
  also have "t x \<sqsubseteq> c y" using y le by (simp add: t_below U_def)
  finally show "chase a b X x \<sqsubseteq> chase a b Y y" by (simp add: c_def)
qed

corollary chase_lower_mono:
  assumes le: "lower_below X Y" and cY: "fd_consistent a b Y"
  shows "lower_below (chase a b X ` X) (chase a b Y ` Y)"
  unfolding lower_below_def
proof (intro ballI, elim imageE)
  fix u x assume u: "u = chase a b X x" and x: "x \<in> X"
  obtain y where y: "y \<in> Y" "x \<sqsubseteq> y" using le x by (auto simp add: lower_below_def)
  show "\<exists>v\<in>chase a b Y ` Y. u \<sqsubseteq> v" using chase_mono(2)[OF le cY x y] u y(1) by blast
qed

text \<open>The Egli-Milner order transfers too: its Smyth half is carried by the same pointwise
  monotonicity.  And a consistent set lies Egli-Milner below its own chase.\<close>

definition em_below :: "'r set \<Rightarrow> 'r set \<Rightarrow> bool" where
  "em_below X Y \<longleftrightarrow> lower_below X Y \<and> (\<forall>y\<in>Y. \<exists>x\<in>X. x \<sqsubseteq> y)"

corollary chase_em_mono:
  assumes em: "em_below X Y" and cY: "fd_consistent a b Y"
  shows "em_below (chase a b X ` X) (chase a b Y ` Y)"
proof -
  have le: "lower_below X Y" using em by (simp add: em_below_def)
  have "\<exists>u\<in>chase a b X ` X. u \<sqsubseteq> v" if v: "v \<in> chase a b Y ` Y" for v
  proof -
    obtain y where y: "y \<in> Y" and vy: "v = chase a b Y y" using v by blast
    obtain x where x: "x \<in> X" "x \<sqsubseteq> y" using em y by (auto simp add: em_below_def)
    show ?thesis using chase_mono(2)[OF le cY x(1) y x(2)] vy x(1) by blast
  qed
  then show ?thesis unfolding em_below_def using chase_lower_mono[OF le cY] by blast
qed

lemma chase_em_above: "fd_consistent a b X \<Longrightarrow> em_below X (chase a b X ` X)"
  unfolding em_below_def lower_below_def by (blast intro: chase_above)

text \<open>Comparable rows stay comparable, and rows below others never add information: on a
  subset that dominates the whole set (in the Hoare sense) the chase is the same.\<close>

corollary chase_mono_point:
  "fd_consistent a b X \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> chase a b X x \<sqsubseteq> chase a b X y"
  by (rule chase_mono(2)) (auto simp add: lower_below_def)

lemma fd_subset: "fd a b R \<Longrightarrow> S \<subseteq> R \<Longrightarrow> fd a b S"
  unfolding fd_def by blast

lemma fd_closed_subset: "fd_closed a b X t \<Longrightarrow> Z \<subseteq> X \<Longrightarrow> fd_closed a b Z t"
  unfolding fd_closed_def by (blast intro: fd_subset)

lemma chase_subset:
  assumes cX: "fd_consistent a b X" and sub: "Z \<subseteq> X"
  shows "fd_consistent a b Z" and "chase a b Z z \<sqsubseteq> chase a b X z"
proof -
  show "fd_consistent a b Z"
    using cX sub by (auto simp add: fd_consistent_def intro: fd_closed_subset)
  have ne: "(\<lambda>t. t z) ` {t. fd_closed a b X t} \<noteq> {}" using cX by (auto simp add: fd_consistent_def)
  have "\<forall>u\<in>(\<lambda>t. t z) ` {t. fd_closed a b X t}. chase a b Z z \<sqsubseteq> u"
    using sub by (auto intro: chase_least fd_closed_subset)
  then show "chase a b Z z \<sqsubseteq> chase a b X z"
    using ne by (simp add: chase_def[of a b X] glb_greatest)
qed

theorem chase_dominated:
  assumes cZ: "fd_consistent a b Z" and sub: "Z \<subseteq> X" and dom: "\<forall>x\<in>X. \<exists>z\<in>Z. x \<sqsubseteq> z"
  shows "fd_consistent a b X" and "z \<in> Z \<Longrightarrow> chase a b X z = chase a b Z z"
proof -
  have le: "lower_below X Z" using dom by (simp add: lower_below_def)
  show cX: "fd_consistent a b X" by (rule chase_mono(1)[OF le cZ])
  assume z: "z \<in> Z"
  show "chase a b X z = chase a b Z z"
  proof (rule below_antisym)
    show "chase a b X z \<sqsubseteq> chase a b Z z" using z sub by (intro chase_mono(2)[OF le cZ]) auto
    show "chase a b Z z \<sqsubseteq> chase a b X z" by (rule chase_subset(2)[OF cX sub])
  qed
qed

corollary fd_inconsistent_up: "lower_below X Y \<Longrightarrow> \<not> fd_consistent a b X \<Longrightarrow> \<not> fd_consistent a b Y"
  using chase_mono(1) by blast

end
