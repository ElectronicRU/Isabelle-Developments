theory Split_Exact
  imports Split_Csem
begin

section \<open>Exactness of the extended semantics\<close>

text \<open>The extended semantics is below the rigid one at the data a split dataset is definite about.
  It equals it where nothing the expression reads is still open: at a key LOD \<open>K\<close> covering what
  the expression reads, the key mix of the dataset is \<^emph>\<open>saturated\<close>, a finite set of key parts
  maximal at \<open>K\<close>, each both definite and possible.  Then every row's part at \<open>K\<close> is one of them,
  and every possible key's part is a row's.  Row guards are left out: they only confirm, so a group
  whose rows all fail one is still possibly present.\<close>

definition mix_saturated :: "'k::{domain, lod_domain} semi_factor \<Rightarrow> 'k mix_pd \<Rightarrow> bool" where
  "mix_saturated K M \<longleftrightarrow> (\<exists>P. M = mix_principal (MSet P) \<and> (\<forall>v\<in>Rep_pde_basis P. maximal_at K (Rep_compact_basis v)))"

context split_dataspace
begin

subsection \<open>Saturated datasets\<close>

text \<open>At a saturated basis element, the rows' parts are maximal, and the possible keys' parts are
  the rows' parts.\<close>

lemma saturated_row_part:
  assumes s: "mix_saturated K (KM K t)" and x: "x \<in> srows t"
  shows "maximal_at K (rproj K (Rep_compact_basis x))"
proof -
  obtain P where P: "KM K t = mix_principal (MSet P)" and mP: "\<forall>v\<in>Rep_pde_basis P. maximal_at K (Rep_compact_basis v)"
    using s unfolding mix_saturated_def by blast
  obtain u where u: "u \<in> skeys t" and ux: "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
    using split_basis_consistentD [OF x] by blast
  have "mix_possible (proj K\<cdot>(Rep_compact_basis u)) (KM K t)" unfolding KM_possible using u by blast
  then obtain v where v: "v \<in> Rep_pde_basis P" and vu: "Rep_compact_basis v \<sqsubseteq> proj K\<cdot>(Rep_compact_basis u)"
    unfolding P mix_possible_principal by auto
  have mv: "maximal_at K (Rep_compact_basis v)" using mP v by blast
  have vx: "Rep_compact_basis v \<sqsubseteq> rproj K (Rep_compact_basis x)"
    by (rule below_trans [OF vu monofun_cfun_arg [OF ux]])
  have "rproj K (Rep_compact_basis x) = Rep_compact_basis v" by (rule maximal_at_eq [OF mv _ vx]) simp
  then show ?thesis using mv by simp
qed

lemma saturated_key_part:
  assumes s: "mix_saturated K (KM K t)" and u: "u \<in> skeys t"
  shows "\<exists>x\<in>srows t. proj K\<cdot>(Rep_compact_basis u) = rproj K (Rep_compact_basis x)"
proof -
  obtain P where P: "KM K t = mix_principal (MSet P)" and mP: "\<forall>v\<in>Rep_pde_basis P. maximal_at K (Rep_compact_basis v)"
    using s unfolding mix_saturated_def by blast
  have "mix_possible (proj K\<cdot>(Rep_compact_basis u)) (KM K t)" unfolding KM_possible using u by blast
  then obtain v where v: "v \<in> Rep_pde_basis P" and vu: "Rep_compact_basis v \<sqsubseteq> proj K\<cdot>(Rep_compact_basis u)"
    unfolding P mix_possible_principal by auto
  have mv: "maximal_at K (Rep_compact_basis v)" using mP v by blast
  have uv: "proj K\<cdot>(Rep_compact_basis u) = Rep_compact_basis v" by (rule maximal_at_eq [OF mv _ vu]) simp
  have "mix_definite (Rep_compact_basis v) (KM K t)" unfolding P mix_definite_principal using v by auto
  then obtain x where x: "x \<in> srows t" and vx: "Rep_compact_basis v \<sqsubseteq> rproj K (Rep_compact_basis x)"
    unfolding KM_definite [OF Rep_compact_basis'] by blast
  have xv: "rproj K (Rep_compact_basis x) = Rep_compact_basis v" by (rule maximal_at_eq [OF mv _ vx]) simp
  show ?thesis by (rule bexI [OF _ x]) (simp only: uv xv)
qed

text \<open>The presence test at a part of a coarser LOD, with a key guard reading the keys' parts at
  \<open>K\<close> and no row guard, is the rigid one at the data of a saturated basis element.\<close>

lemma select_test_exact:
  assumes s: "mix_saturated K (KM K t)" and d: "split_rows\<cdot>(split_principal t) = up\<cdot>data"
    and LK: "L \<sqsubseteq> K" and \<kappa>: "proj L\<cdot>\<kappa> = \<kappa>" and hK: "\<And>u. h\<cdot>(proj K\<cdot>u) = h\<cdot>u"
  shows "select_test L \<kappa> (\<Lambda> _. TT) h (split_principal t) = (\<exists>\<^sub>K m\<in>{m \<in> lower_maximal data. rproj L m = \<kappa>}. h\<cdot>(row_key\<cdot>m))"
proof -
  let ?D = "split_principal t" and ?R = "{m \<in> lower_maximal data. rproj L m = \<kappa>}"
  have pk: "proj L\<cdot>(proj K\<cdot>u) = proj L\<cdot>u" for u by (rule proj_le [OF LK])
  have rowL: "maximal_at L (rproj L (Rep_compact_basis x))" if "x \<in> srows t" for x
    using maximal_at_proj [OF LK saturated_row_part [OF s that]] pk by simp
  have pt: "m \<in> lower_maximal data \<Longrightarrow> \<exists>x\<in>srows t. m = Rep_compact_basis x" for m
    by (rule split_maximal_row_generator [OF d])
  have hrow: "h\<cdot>(row_key\<cdot>m) = h\<cdot>(row_key\<cdot>(Rep_compact_basis x))"
    if x: "x \<in> srows t" and m: "Rep_compact_basis x \<sqsubseteq> m" for x m
  proof -
    have xm: "rproj K (Rep_compact_basis x) \<sqsubseteq> rproj K m" by (intro monofun_cfun_arg m)
    have "rproj K m = rproj K (Rep_compact_basis x)" by (rule maximal_at_eq [OF saturated_row_part [OF s x] _ xm]) simp
    then show ?thesis using hK [of "row_key\<cdot>m"] hK [of "row_key\<cdot>(Rep_compact_basis x)"] by simp
  qed
  have defpt: "split_definite (Rep_compact_basis x) ?D" if "x \<in> srows t" for x by (rule generator_definite [OF that])
  have TTiff: "(maximal_at L \<kappa> \<and> (\<exists>y. split_definite y ?D \<and> rproj L y = \<kappa> \<and> (\<Lambda> _. TT)\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT))
      \<longleftrightarrow> (\<exists>m\<in>?R. h\<cdot>(row_key\<cdot>m) = TT)"
  proof
    assume "maximal_at L \<kappa> \<and> (\<exists>y. split_definite y ?D \<and> rproj L y = \<kappa> \<and> (\<Lambda> _. TT)\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)"
    then obtain y where mx: "maximal_at L \<kappa>" and y: "split_definite y ?D" "rproj L y = \<kappa>" and hy: "h\<cdot>(row_key\<cdot>y) = TT" by auto
    obtain m where m: "m \<in> lower_maximal data" "y \<sqsubseteq> m" "rproj L m = rproj L y"
      using definite_maximal_point [OF below_refl d y(1)] mx y(2) by auto
    have "TT \<sqsubseteq> h\<cdot>(row_key\<cdot>m)" unfolding hy [symmetric] by (intro monofun_cfun_arg m(2))
    then show "\<exists>m\<in>?R. h\<cdot>(row_key\<cdot>m) = TT" using m y(2) by auto
  next
    assume "\<exists>m\<in>?R. h\<cdot>(row_key\<cdot>m) = TT"
    then obtain m where m: "m \<in> lower_maximal data" "rproj L m = \<kappa>" and hm: "h\<cdot>(row_key\<cdot>m) = TT" by blast
    obtain x where x: "x \<in> srows t" and mx: "m = Rep_compact_basis x" using pt [OF m(1)] by blast
    show "maximal_at L \<kappa> \<and> (\<exists>y. split_definite y ?D \<and> rproj L y = \<kappa> \<and> (\<Lambda> _. TT)\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)"
      using rowL [OF x] defpt [OF x] m(2) hm unfolding mx by auto
  qed
  have FFiff: "split_refuted L \<kappa> h ?D \<longleftrightarrow> (\<forall>m\<in>?R. h\<cdot>(row_key\<cdot>m) = FF)"
  proof -
    have r: "split_refuted L \<kappa> h ?D \<longleftrightarrow> (\<forall>u\<in>skeys t. proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa> \<longrightarrow> h\<cdot>(Rep_compact_basis u) = FF)"
      unfolding split_refuted_keyguard split_select_principal split_keyguard_principal split_keys_principal_Top by auto
    show ?thesis unfolding r
    proof (intro iffI ballI impI)
      fix m assume all: "\<forall>u\<in>skeys t. proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa> \<longrightarrow> h\<cdot>(Rep_compact_basis u) = FF" and "m \<in> ?R"
      then have m: "m \<in> lower_maximal data" "rproj L m = \<kappa>" by simp_all
      obtain x where x: "x \<in> srows t" and mx: "m = Rep_compact_basis x" using pt [OF m(1)] by blast
      obtain u where u: "u \<in> skeys t" and ux: "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
        using split_basis_consistentD [OF x] by blast
      have "proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>" using monofun_cfun_arg [OF ux, of "proj L"] m(2) mx by simp
      then have "h\<cdot>(Rep_compact_basis u) = FF" using all u by blast
      moreover have "h\<cdot>(Rep_compact_basis u) \<sqsubseteq> h\<cdot>(row_key\<cdot>m)" unfolding mx by (rule monofun_cfun_arg [OF ux])
      ultimately show "h\<cdot>(row_key\<cdot>m) = FF" by simp
    next
      fix u assume all: "\<forall>m\<in>?R. h\<cdot>(row_key\<cdot>m) = FF" and u: "u \<in> skeys t" and uk: "proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>"
      obtain x where x: "x \<in> srows t" and ux: "proj K\<cdot>(Rep_compact_basis u) = rproj K (Rep_compact_basis x)"
        using saturated_key_part [OF s u] by blast
      have le: "rproj L (Rep_compact_basis x) \<sqsubseteq> \<kappa>"
        using uk ux pk [of "Rep_compact_basis u"] pk [of "row_key\<cdot>(Rep_compact_basis x)"] by metis
      have xL: "rproj L (Rep_compact_basis x) = \<kappa>" using maximal_at_eq [OF rowL [OF x] \<kappa> le] by simp
      have rL: "maximal_at L (rproj L (Rep_compact_basis x))" by (rule rowL [OF x])
      obtain m where m: "m \<in> lower_maximal data" "Rep_compact_basis x \<sqsubseteq> m" "rproj L m = rproj L (Rep_compact_basis x)"
        by (rule definite_maximal_point [OF below_refl d defpt [OF x] rL])
      have "h\<cdot>(row_key\<cdot>m) = FF" using all m xL by auto
      then have "h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = FF" using hrow [OF x m(2)] by simp
      then show "h\<cdot>(Rep_compact_basis u) = FF" using hK [of "Rep_compact_basis u"] hK [of "row_key\<cdot>(Rep_compact_basis x)"] ux by simp
    qed
  qed
  show ?thesis
  proof (cases "\<exists>m\<in>?R. h\<cdot>(row_key\<cdot>m) = TT")
    case True
    then show ?thesis unfolding select_test_def TTiff kleene_bex_def by auto
  next
    case nT: False
    then show ?thesis unfolding select_test_def TTiff FFiff kleene_bex_def by auto
  qed
qed


subsection \<open>Exact expressions\<close>

text \<open>A key guard \<^emph>\<open>reads\<close> an LOD when it depends on keys only through their parts there.  An
  expression reads within \<open>K\<close> at a frame when its entries' selected parts and keys lie below
  \<open>K\<close>, and its guards' key guards read \<open>K\<close>.\<close>

definition kreads :: "'k semi_factor \<Rightarrow> ('k \<rightarrow> tr) \<Rightarrow> bool" where
  "kreads K h \<longleftrightarrow> (\<forall>u. h\<cdot>(proj K\<cdot>u) = h\<cdot>u)"

abbreviation gkguard :: "('k, 'r guard \<times> 'k guard) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<rightarrow> tr" where
  "gkguard e F \<equiv> gand (sopen (coarsen (eupper e) (slice F))) (ekguard e)"

definition reads_within :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> bool" where
  "reads_within X F K \<longleftrightarrow> (\<forall>S\<in>set (esels X). sel_at S (flod F) \<sqsubseteq> K) \<and>
     (\<forall>e\<in>set (eguards X). ekeys e \<sqsubseteq> K \<and> kreads K (gkguard e F)) \<and> (\<forall>e\<in>set (evalues X). ekeys e \<sqsubseteq> K)"

text \<open>An extended expression is \<^emph>\<open>exact\<close> when, at a saturated compact dataset under a frame
  without an ambient filter, reading within the saturating LOD, it is the rigid semantics of the
  data the dataset is definite about.\<close>

definition ext_exact :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> bool" where
  "ext_exact X \<longleftrightarrow> (\<forall>t data F k K. mix_saturated K (KM K t) \<longrightarrow> split_rows\<cdot>(split_principal t) = up\<cdot>data \<longrightarrow>
     conforms data \<longrightarrow> fconf (evalues X) data F \<longrightarrow> amb F = gtrue \<longrightarrow> reads_within X F K \<longrightarrow> proj (kd X F)\<cdot>k = k \<longrightarrow>
     sem_ext X (split_principal t) F k = esem X data F k)"

lemma ext_exactI:
  "(\<And>t data F k K. mix_saturated K (KM K t) \<Longrightarrow> split_rows\<cdot>(split_principal t) = up\<cdot>data \<Longrightarrow>
     conforms data \<Longrightarrow> fconf (evalues X) data F \<Longrightarrow> amb F = gtrue \<Longrightarrow> reads_within X F K \<Longrightarrow> proj (kd X F)\<cdot>k = k \<Longrightarrow>
     sem_ext X (split_principal t) F k = esem X data F k) \<Longrightarrow> ext_exact X"
  unfolding ext_exact_def by blast

lemma ext_exactD:
  "ext_exact X \<Longrightarrow> mix_saturated K (KM K t) \<Longrightarrow> split_rows\<cdot>(split_principal t) = up\<cdot>data \<Longrightarrow>
     conforms data \<Longrightarrow> fconf (evalues X) data F \<Longrightarrow> amb F = gtrue \<Longrightarrow> reads_within X F K \<Longrightarrow> proj (kd X F)\<cdot>k = k \<Longrightarrow>
     sem_ext X (split_principal t) F k = esem X data F k"
  unfolding ext_exact_def by blast

text \<open>The presence of a group at a part read within \<open>K\<close> is exact.\<close>

lemma populated_ext_exact:
  assumes s: "mix_saturated K (KM K t)" and d: "split_rows\<cdot>(split_principal t) = up\<cdot>data"
    and LK: "a \<squnion> (\<rho> \<sqinter> flod F) \<sqsubseteq> K" and hK: "kreads K (sopen (coarsen \<rho> (slice F)))" and amb: "amb F = gtrue"
  shows "populated_ext (split_principal t) a \<rho> F k = populated data a \<rho> F k"
proof -
  let ?L = "a \<squnion> (\<rho> \<sqinter> flod F)"
  have "select_test ?L (proj ?L\<cdot>k) (\<Lambda> _. TT) (sopen (coarsen \<rho> (slice F))) (split_principal t) =
      (\<exists>\<^sub>K m\<in>{m \<in> lower_maximal data. rproj ?L m = proj ?L\<cdot>k}. sopen (coarsen \<rho> (slice F))\<cdot>(row_key\<cdot>m))"
    by (rule select_test_exact [OF s d LK proj_idem]) (use hK in \<open>simp add: kreads_def\<close>)
  then show ?thesis unfolding populated_ext_def populated_def fiber_def fguard_split amb gtrue_def by simp
qed

theorem ext_exact_key_at: "ext_exact (key_at_ext c)"
proof (rule ext_exactI, simp only: key_at_ext_simps key_at_simps)
  fix t data F k K
  assume s: "mix_saturated K (KM K t)" and d: "split_rows\<cdot>(split_principal t) = up\<cdot>data"
    and r: "reads_within (key_at_ext c) F K"
  have cK: "c \<sqsubseteq> K" using r by (simp add: reads_within_def join_meet_self)
  have fib: "fiber data c c F k = {m \<in> lower_maximal data. rproj c m = proj c\<cdot>k}" by (simp add: fiber_def join_meet_self)
  have "select_test c (proj c\<cdot>k) (\<Lambda> _. TT) (\<Lambda> _. TT) (split_principal t) = (\<exists>\<^sub>K m\<in>fiber data c c F k. (\<Lambda> _. TT)\<cdot>(row_key\<cdot>m))"
    unfolding fib by (rule select_test_exact [OF s d cK proj_idem]) simp
  then show "key_at_sem c (split_principal t) k = (if fiber data c c F k = {} then Absent else Present\<cdot>(proj c\<cdot>k))"
    by (simp add: kleene_bex_const_TT)
qed

theorem ext_exact_column: "ext_exact (column_ext c a v)"
proof (rule ext_exactI, simp only: column_ext_simps)
  fix t data F k K
  assume s: "mix_saturated K (KM K t)" and d: "split_rows\<cdot>(split_principal t) = up\<cdot>data"
    and conf: "fconf (evalues (column c a v)) data F" and r: "reads_within (column_ext c a v) F K"
  let ?D = "split_principal t" and ?e = "mk_value (sel a a) c a"
  have aK: "a \<sqsubseteq> K" using r by (simp add: reads_within_def join_meet_self)
  have cf: "entry_conf ?e data F" using conf by (simp add: fconf_def)
  have fib: "fiber data a a F k = {m \<in> lower_maximal data. rproj a m = proj a\<cdot>k}" by (simp add: fiber_def join_meet_self)
  have t0: "select_test a (proj a\<cdot>k) (\<Lambda> _. TT) (\<Lambda> _. TT) ?D = (\<exists>\<^sub>K m\<in>fiber data a a F k. (\<Lambda> _. TT)\<cdot>(row_key\<cdot>m))"
    unfolding fib by (rule select_test_exact [OF s d aK proj_idem]) simp
  then have t: "select_test a (proj a\<cdot>k) (\<Lambda> _. TT) (\<Lambda> _. TT) ?D = (\<exists>\<^sub>K m\<in>fiber data a a F k. TT)" by simp
  show "column_sem c a v ?D k = esem (column c a v) data F k"
  proof (cases "fiber data a a F k = {}")
    case True
    then show ?thesis using t by (simp add: kleene_bex_const_TT)
  next
    case False
    then obtain m where m: "m \<in> fiber data a a F k" by blast
    have mm: "m \<in> lower_maximal data" and mk: "rproj a m = proj a\<cdot>k" using m fib by simp_all
    obtain x where x: "x \<in> srows t" and xm: "m = Rep_compact_basis x" using split_maximal_row_generator [OF d mm] by blast
    have mx: "maximal_at a (proj a\<cdot>k)"
      using maximal_at_proj [OF aK saturated_row_part [OF s x]] proj_le [OF aK] mk xm by simp
    have "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k = (\<lambda>_. v\<cdot>(m \<downharpoonright> c)) ` fiber data a a F k"
      by (rule image_cong [OF refl]) (simp add: column_fiber_section [OF cf m])
    then have V: "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k = {v\<cdot>(m \<downharpoonright> c)}" using m by (auto simp: image_constant_conv)
    have ub: "col_sections c a ?D k <| m \<downharpoonright> c"
    proof (rule is_ubI)
      fix z assume "z \<in> col_sections c a ?D k"
      then obtain y where y: "split_definite y ?D" "rproj a y = proj a\<cdot>k" "z = y \<downharpoonright> c" by (auto simp: col_sections_def)
      have "maximal_at a (rproj a y)" using mx y(2) by simp
      then obtain m' where m': "m' \<in> lower_maximal data" "y \<sqsubseteq> m'" "rproj a m' = rproj a y"
        using definite_maximal_point [OF below_refl d y(1)] by blast
      have m'F: "m' \<in> fiber data a a F k" using fib m'(1,3) y(2) by simp
      have "y \<downharpoonright> c \<sqsubseteq> m' \<downharpoonright> c" by (intro monofun_cfun_arg m'(2))
      then show "z \<sqsubseteq> m \<downharpoonright> c" using y(3) column_fiber_section [OF cf m m'F] by simp
    qed
    have inS: "m \<downharpoonright> c \<in> col_sections c a ?D k"
      unfolding col_sections_def using generator_definite [OF x] xm mk by auto
    have cv: "col_value c a ?D k = m \<downharpoonright> c"
      unfolding col_value_def using mx is_lub_maximal [OF ub inS] by (simp add: lub_eqI)
    show ?thesis using False t V cv by (simp add: kleene_bex_const_TT)
  qed
qed

theorem ext_exact_const: "ext_exact (const_ext v)"
  by (rule ext_exactI) simp

theorem ext_exact_smap: "ext_exact X \<Longrightarrow> ext_exact (smap_ext g X)"
  by (rule ext_exactI) (simp add: ext_exactD reads_within_def)

theorem ext_exact_combine:
  assumes X\<^sub>1: "ext_exact X\<^sub>1" and X\<^sub>2: "ext_exact X\<^sub>2"
  shows "ext_exact (combine_ext f X\<^sub>1 X\<^sub>2)"
proof (rule ext_exactI, simp only: combine_ext_simps combine_simps)
  fix t data F k K
  assume s: "mix_saturated K (KM K t)" and d: "split_rows\<cdot>(split_principal t) = up\<cdot>data" and cd: "conforms data"
    and conf: "fconf (evalues X\<^sub>1 @ evalues X\<^sub>2) data F" and amb: "amb F = gtrue"
    and r: "reads_within (combine_ext f X\<^sub>1 X\<^sub>2) F K"
  have c1: "fconf (evalues X\<^sub>1) data F" and c2: "fconf (evalues X\<^sub>2) data F" using conf by (simp_all add: fconf_def)
  have r1: "reads_within X\<^sub>1 F K" and r2: "reads_within X\<^sub>2 F K" using r by (auto simp: reads_within_def)
  show "lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 (split_principal t) F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 (split_principal t) F (proj (kd X\<^sub>2 F)\<cdot>k)) =
      lift2_option_pd f\<cdot>(esem X\<^sub>1 data F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(esem X\<^sub>2 data F (proj (kd X\<^sub>2 F)\<cdot>k))"
    by (simp only: ext_exactD [OF X\<^sub>1 s d cd c1 amb r1 proj_idem] ext_exactD [OF X\<^sub>2 s d cd c2 amb r2 proj_idem])
qed

theorem ext_exact_present_at:
  assumes X: "ext_exact X"
  shows "ext_exact (present_at_ext a \<rho> X)"
proof (rule ext_exactI, simp only: present_at_ext_simps present_at_simps)
  fix t data F k K
  assume s: "mix_saturated K (KM K t)" and d: "split_rows\<cdot>(split_principal t) = up\<cdot>data" and cd: "conforms data"
    and conf: "fconf (evalues X) data F" and amb: "amb F = gtrue" and r: "reads_within (present_at_ext a \<rho> X) F K"
  let ?e = "mk_guard (sel (emind X \<squnion> a) \<rho>) gtrue gtrue \<bottom> :: ('k, 'r guard \<times> 'k guard) entry"
  have LK: "(emind X \<squnion> a) \<squnion> (\<rho> \<sqinter> flod F) \<sqsubseteq> K" and hK: "kreads K (sopen (coarsen \<rho> (slice F)))"
    using r unfolding reads_within_def by (auto simp: gand_gtrue)
  have rX: "reads_within X F K" using r by (simp add: reads_within_def)
  show "populated_ext (split_principal t) (emind X \<squnion> a) \<rho> F k \<odot> sem_ext X (split_principal t) F (proj (kd X F)\<cdot>k) =
      populated data (emind X \<squnion> a) \<rho> F k \<odot> esem X data F (proj (kd X F)\<cdot>k)"
    by (simp only: populated_ext_exact [OF s d LK hK amb] ext_exactD [OF X s d cd conf amb rX proj_idem])
qed


text \<open>Including dimensions and filtering for keys move what the entries read along with the
  frame.\<close>

lemma gkguard_include: "gkguard (include_entry M e) F = gkguard e (finclude M F)"
  by simp

lemma gkguard_ffor: "gkguard e (ffor \<tau> G F) = gkguard (for_entry \<tau> G e) F"
  by (simp add: coarsen_conj coarsen_coarsen sopen_gand gand_assoc)

theorem ext_exact_include_dims:
  assumes ES: "semilawful X" and X: "ext_exact X"
  shows "ext_exact (include_dims_ext M X)"
proof (rule ext_exactI, simp only: include_dims_ext_simps include_dims_simps(3,4))
  fix t data F k K
  assume s: "mix_saturated K (KM K t)" and d: "split_rows\<cdot>(split_principal t) = up\<cdot>data" and cd: "conforms data"
    and conf: "fconf (map (include_entry M) (evalues X)) data F" and amb: "amb F = gtrue"
    and r: "reads_within (include_dims_ext M X) F K" and k: "proj (kd (include_dims M X) F)\<cdot>k = k"
  have d': "fconf (evalues X) data (finclude M F)" using conf by (simp only: fconf_include)
  have k': "proj (kd X (finclude M F))\<cdot>k = k" by (rule proj_fix_mono [OF include_dims_kd_below [OF ES] k])
  have amb': "amb (finclude M F) = gtrue" using amb by simp
  have r': "reads_within X (finclude M F) K"
    unfolding reads_within_def
  proof (intro conjI ballI)
    fix S assume S: "S \<in> set (esels X)"
    have ts: "include_sel M S \<in> set (esels (include_dims_ext M X))" using S by (auto simp: comp_def)
    have "sel_at (include_sel M S) (flod F) \<sqsubseteq> K" using r ts unfolding reads_within_def by blast
    then show "sel_at S (flod (finclude M F)) \<sqsubseteq> K" by (simp only: include_lod)
  next
    fix e assume e: "e \<in> set (eguards X)"
    have fe: "include_entry M e \<in> set (eguards (include_dims_ext M X))" using e by simp
    have "ekeys (include_entry M e) \<sqsubseteq> K" using r fe unfolding reads_within_def by blast
    then show "ekeys e \<sqsubseteq> K" by simp
  next
    fix e assume e: "e \<in> set (eguards X)"
    have fe: "include_entry M e \<in> set (eguards (include_dims_ext M X))" using e by simp
    have "kreads K (gkguard (include_entry M e) F)" using r fe unfolding reads_within_def by blast
    then show "kreads K (gkguard e (finclude M F))" by (simp only: gkguard_include)
  next
    fix e assume e: "e \<in> set (evalues X)"
    have fe: "include_entry M e \<in> set (evalues (include_dims_ext M X))" using e by simp
    have "ekeys (include_entry M e) \<sqsubseteq> K" using r fe unfolding reads_within_def by blast
    then show "ekeys e \<sqsubseteq> K" by simp
  qed
  show "sem_ext X (split_principal t) (finclude M F) k = esem X data (finclude M F) k"
    by (rule ext_exactD [OF X s d cd d' amb' r' k'])
qed

theorem ext_exact_filtfor:
  assumes ES: "semilawful X" and X: "ext_exact X"
  shows "ext_exact (filtfor_ext \<tau> G X)"
proof (rule ext_exactI, simp only: filtfor_ext_simps filtfor_simps)
  fix t data F k K
  assume s: "mix_saturated K (KM K t)" and d: "split_rows\<cdot>(split_principal t) = up\<cdot>data" and cd: "conforms data"
    and conf: "fconf (map (for_value \<tau>) (evalues X)) data F" and amb: "amb F = gtrue"
    and r: "reads_within (filtfor_ext \<tau> G X) F K"
  let ?k = "proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k"
  have d': "fconf (evalues X) data (ffor \<tau> G F)" using conf by (simp only: fconf_filtfor [of _ _ _ _ G])
  have amb': "amb (ffor \<tau> G F) = gtrue" using amb by simp
  have lm: "lower_part S \<sqsubseteq> emind X" if "S \<in> set (esels X)" for S by (rule lower_below_mind [OF ES that])
  have sel: "sel_at S (flod (ffor \<tau> G F)) = sel_at (trunc_sel \<tau> S) (flod F)" if "S \<in> set (esels X)" for S
    by (simp only: ffor_key [OF lm [OF that]] trunc_sel_simps)
  have r': "reads_within X (ffor \<tau> G F) K"
    unfolding reads_within_def
  proof (intro conjI ballI)
    fix S assume S: "S \<in> set (esels X)"
    have ts: "trunc_sel \<tau> S \<in> set (esels (filtfor_ext \<tau> G X))" using S by (auto simp: comp_def)
    have "sel_at (trunc_sel \<tau> S) (flod F) \<sqsubseteq> K" using r ts unfolding reads_within_def by blast
    then show "sel_at S (flod (ffor \<tau> G F)) \<sqsubseteq> K" by (simp only: sel [OF S])
  next
    fix e assume e: "e \<in> set (eguards X)"
    have fe: "for_entry \<tau> G e \<in> set (eguards (filtfor_ext \<tau> G X))" using e by simp
    have "ekeys (for_entry \<tau> G e) \<sqsubseteq> K" using r fe unfolding reads_within_def by blast
    then show "ekeys e \<sqsubseteq> K" by simp
  next
    fix e assume e: "e \<in> set (eguards X)"
    have fe: "for_entry \<tau> G e \<in> set (eguards (filtfor_ext \<tau> G X))" using e by simp
    have "kreads K (gkguard (for_entry \<tau> G e) F)" using r fe unfolding reads_within_def by blast
    then show "kreads K (gkguard e (ffor \<tau> G F))" by (simp only: gkguard_ffor)
  next
    fix e assume e: "e \<in> set (evalues X)"
    have fe: "for_value \<tau> e \<in> set (evalues (filtfor_ext \<tau> G X))" using e by simp
    have "ekeys (for_value \<tau> e) \<sqsubseteq> K" using r fe unfolding reads_within_def by blast
    then show "ekeys e \<sqsubseteq> K" by simp
  qed
  show "sem_ext X (split_principal t) (ffor \<tau> G F) ?k = esem X data (ffor \<tau> G F) ?k"
    by (rule ext_exactD [OF X s d cd d' amb' r' proj_idem])
qed

end

end
