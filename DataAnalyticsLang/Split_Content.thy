theory Split_Content
  imports SplitPD "HOLCF-extra.Kleene_Logic"
begin

default_sort bifinite

section \<open>Mapping and selecting from split datasets\<close>

text \<open>Two operations towards contents over split datasets.  Mapping sends the rows and the possible
  keys through continuous functions that preserve compactness, provided the key of a mapped row
  lies above the mapped key.  Selecting at a key part keeps the definite rows that lie at that part
  (only where it is maximal: a row at a partial part may still leave it) and the possible keys that
  may still end up there.\<close>

subsection \<open>Mapping\<close>

definition cb_map :: "('a \<rightarrow> 'b) \<Rightarrow> 'a compact_basis \<Rightarrow> 'b compact_basis" where
  "cb_map f x = Abs_compact_basis (f\<cdot>(Rep_compact_basis x))"

lemma Rep_cb_map:
  "(\<And>x. compact x \<Longrightarrow> compact (f\<cdot>x)) \<Longrightarrow> Rep_compact_basis (cb_map f x) = f\<cdot>(Rep_compact_basis x)"
  unfolding cb_map_def by simp

text \<open>A mapping of split datasets: a row map and a key map, both preserving compactness, such that
  the key of a mapped row lies above the mapped key of the row.\<close>

definition split_map_ok :: "('r \<rightarrow> 'r2) \<Rightarrow> ('k \<rightarrow> 'k2) \<Rightarrow> bool" where
  "split_map_ok f h \<longleftrightarrow> (\<forall>x. compact x \<longrightarrow> compact (f\<cdot>x)) \<and> (\<forall>u. compact u \<longrightarrow> compact (h\<cdot>u)) \<and>
     (\<forall>y. h\<cdot>(row_key\<cdot>y) \<sqsubseteq> row_key\<cdot>(f\<cdot>y))"

lemma split_map_okD:
  assumes "split_map_ok f h"
  shows "compact x \<Longrightarrow> compact (f\<cdot>x)" and "compact u \<Longrightarrow> compact (h\<cdot>u)"
    and "h\<cdot>(row_key\<cdot>y) \<sqsubseteq> row_key\<cdot>(f\<cdot>y)"
  using assms unfolding split_map_ok_def by blast+

lemma smap_consistent:
  assumes ok: "split_map_ok f h"
  shows "split_consistent (cb_map f ` srows t) (cb_map h ` skeys t)"
  unfolding split_consistent_def
proof
  fix x' assume "x' \<in> cb_map f ` srows t"
  then obtain x where x: "x \<in> srows t" and x': "x' = cb_map f x" by blast
  obtain u where u: "u \<in> skeys t" and ux: "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
    using split_basis_consistentD [OF x] by blast
  have "h\<cdot>(Rep_compact_basis u) \<sqsubseteq> h\<cdot>(row_key\<cdot>(Rep_compact_basis x))"
    using ux by (rule monofun_cfun_arg)
  also have "\<dots> \<sqsubseteq> row_key\<cdot>(f\<cdot>(Rep_compact_basis x))"
    by (rule split_map_okD(3) [OF ok])
  finally show "\<exists>w\<in>cb_map h ` skeys t. Rep_compact_basis w \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x')"
    using u unfolding x' by (auto simp: Rep_cb_map split_map_okD [OF ok])
qed

definition SMap :: "('r \<rightarrow> 'r2) \<Rightarrow> ('k \<rightarrow> 'k2) \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> ('r2, 'k2) split_basis" where
  "SMap f h t = SplitB (cb_map f ` srows t) (cb_map h ` skeys t)"

lemma srows_SMap [simp]: "split_map_ok f h \<Longrightarrow> srows (SMap f h t) = cb_map f ` srows t"
  and skeys_SMap [simp]: "split_map_ok f h \<Longrightarrow> skeys (SMap f h t) = cb_map h ` skeys t"
  unfolding SMap_def by (simp_all add: smap_consistent)

lemma cb_map_mono:
  "(\<And>x. compact x \<Longrightarrow> compact (f\<cdot>x)) \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> cb_map f x \<sqsubseteq> cb_map f y"
  unfolding compact_le_def by (simp add: Rep_cb_map monofun_cfun_arg)

lemma SMap_split_mono:
  assumes ok: "split_map_ok f h" and st: "split_le s t"
  shows "split_le (SMap f h s) (SMap f h t)"
  using st unfolding split_le_def hoare_le_def smyth_le_def
  by (auto simp: ok) (meson cb_map_mono split_map_okD [OF ok])+

definition split_map :: "('r \<rightarrow> 'r2) \<Rightarrow> ('k \<rightarrow> 'k2) \<Rightarrow> ('r, 'k) split_pd \<rightarrow> ('r2, 'k2) split_pd" where
  "split_map f h = split_pd.extension (\<lambda>t. split_principal (SMap f h t))"

lemma split_map_principal [simp]:
  "split_map_ok f h \<Longrightarrow> split_map f h\<cdot>(split_principal t) = split_principal (SMap f h t)"
  unfolding split_map_def by (simp add: split_pd.extension_principal SMap_split_mono)


subsection \<open>Selecting at a key part\<close>

context split_keyed
begin

text \<open>Selecting at the key part \<open>\<kappa>\<close> at the LOD \<open>s\<close>.  A definite row is kept when it lies at
  \<open>\<kappa>\<close> and \<open>\<kappa>\<close> is maximal at \<open>s\<close>: the test is upward closed, since refining the row keeps it
  at a maximal part.  A possible key is kept when its part lies below \<open>\<kappa>\<close>, that is, when it may
  still end up at \<open>\<kappa>\<close>: the test is downward closed.  A kept row's possible key is kept.\<close>

definition SSelect :: "'k semi_factor \<Rightarrow> 'k \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SSelect s \<kappa> t = SplitB {x \<in> srows t. maximal_at s \<kappa> \<and> rproj s (Rep_compact_basis x) = \<kappa>}
     {u \<in> skeys t. proj s\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>}"

lemma select_consistent:
  "split_consistent {x \<in> srows t. maximal_at s \<kappa> \<and> rproj s (Rep_compact_basis x) = \<kappa>}
     {u \<in> skeys t. proj s\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>}"
  unfolding split_consistent_def
proof (intro ballI)
  fix x assume "x \<in> {x \<in> srows t. maximal_at s \<kappa> \<and> rproj s (Rep_compact_basis x) = \<kappa>}"
  then have x: "x \<in> srows t" and k: "rproj s (Rep_compact_basis x) = \<kappa>" by simp_all
  obtain u where u: "u \<in> skeys t" and ux: "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
    using split_basis_consistentD [OF x] by blast
  have "proj s\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>"
    using monofun_cfun_arg [OF ux, of "proj s"] k by simp
  then show "\<exists>u\<in>{u \<in> skeys t. proj s\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>}. Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
    using u ux by blast
qed

lemma srows_SSelect [simp]:
  "srows (SSelect s \<kappa> t) = {x \<in> srows t. maximal_at s \<kappa> \<and> rproj s (Rep_compact_basis x) = \<kappa>}"
  and skeys_SSelect [simp]: "skeys (SSelect s \<kappa> t) = {u \<in> skeys t. proj s\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>}"
  unfolding SSelect_def by (simp_all add: select_consistent)

text \<open>A row at a maximal part stays there when refined.\<close>

lemma maximal_at_row_up:
  assumes m: "maximal_at s \<kappa>" and k: "rproj s x = \<kappa>" and xy: "x \<sqsubseteq> y"
  shows "rproj s y = \<kappa>"
proof -
  have "\<kappa> \<sqsubseteq> rproj s y" using k monofun_cfun_arg [OF monofun_cfun_arg [OF xy, of row_key], of "proj s"] by simp
  moreover have "proj s\<cdot>(rproj s y) = rproj s y" by simp
  ultimately show ?thesis using m unfolding maximal_at_def by blast
qed

lemma SSelect_split_mono:
  assumes le: "split_le t t'"
  shows "split_le (SSelect s \<kappa> t) (SSelect s \<kappa> t')"
  unfolding split_le_def hoare_le_def smyth_le_def
proof (intro conjI ballI)
  fix x assume "x \<in> srows (SSelect s \<kappa> t)"
  then have x: "x \<in> srows t" and m: "maximal_at s \<kappa>" and k: "rproj s (Rep_compact_basis x) = \<kappa>" by simp_all
  obtain y where y: "y \<in> srows t'" and xy: "x \<sqsubseteq> y" using le x unfolding split_le_def hoare_le_def by blast
  have "rproj s (Rep_compact_basis y) = \<kappa>"
    by (rule maximal_at_row_up [OF m k xy [unfolded compact_le_def]])
  then show "\<exists>y\<in>srows (SSelect s \<kappa> t'). x \<sqsubseteq> y" using y xy m by auto
next
  fix v assume "v \<in> skeys (SSelect s \<kappa> t')"
  then have v: "v \<in> skeys t'" and vk: "proj s\<cdot>(Rep_compact_basis v) \<sqsubseteq> \<kappa>" by simp_all
  obtain u where u: "u \<in> skeys t" and uv: "u \<sqsubseteq> v" using le v unfolding split_le_def smyth_le_def by blast
  have "proj s\<cdot>(Rep_compact_basis u) \<sqsubseteq> proj s\<cdot>(Rep_compact_basis v)"
    by (rule monofun_cfun_arg [OF uv [unfolded compact_le_def]])
  then show "\<exists>u\<in>skeys (SSelect s \<kappa> t). u \<sqsubseteq> v" using u uv vk by (auto intro: below_trans)
qed

definition split_select :: "'k semi_factor \<Rightarrow> 'k \<Rightarrow> ('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" where
  "split_select s \<kappa> = split_pd.extension (\<lambda>t. split_principal (SSelect s \<kappa> t))"

lemma split_select_principal [simp]:
  "split_select s \<kappa>\<cdot>(split_principal t) = split_principal (SSelect s \<kappa> t)"
  unfolding split_select_def by (simp add: split_pd.extension_principal SSelect_split_mono)

text \<open>Selection keeps a maybe-unit whose key may end up at the part, and distributes over unions.\<close>

lemma SSelect_SKey: "proj s\<cdot>(Rep_compact_basis k) \<sqsubseteq> \<kappa> \<Longrightarrow> SSelect s \<kappa> (SKey k) = SKey k"
  by (rule split_basis_eqI) auto

lemma split_select_maybe_unit_imp:
  "proj s\<cdot>k \<sqsubseteq> \<kappa> \<longrightarrow> split_select s \<kappa>\<cdot>(split_maybe_unit\<cdot>k :: ('r, 'k) split_pd) = split_maybe_unit\<cdot>k"
proof (induct k rule: compact_basis.principal_induct)
  show "adm (\<lambda>k. proj s\<cdot>k \<sqsubseteq> \<kappa> \<longrightarrow> split_select s \<kappa>\<cdot>(split_maybe_unit\<cdot>k :: ('r, 'k) split_pd) = split_maybe_unit\<cdot>k)"
  proof (rule admI, rule impI)
    fix Y :: "nat \<Rightarrow> 'k"
    assume Y: "chain Y" and h: "\<forall>i. proj s\<cdot>(Y i) \<sqsubseteq> \<kappa> \<longrightarrow> split_select s \<kappa>\<cdot>(split_maybe_unit\<cdot>(Y i) :: ('r, 'k) split_pd) = split_maybe_unit\<cdot>(Y i)"
      and l: "proj s\<cdot>(\<Squnion>i. Y i) \<sqsubseteq> \<kappa>"
    have "proj s\<cdot>(Y i) \<sqsubseteq> \<kappa>" for i by (rule below_trans [OF monofun_cfun_arg [OF is_ub_thelub [OF Y]] l])
    then have e: "split_select s \<kappa>\<cdot>(split_maybe_unit\<cdot>(Y i) :: ('r, 'k) split_pd) = split_maybe_unit\<cdot>(Y i)" for i
      using h by blast
    show "split_select s \<kappa>\<cdot>(split_maybe_unit\<cdot>(\<Squnion>i. Y i) :: ('r, 'k) split_pd) = split_maybe_unit\<cdot>(\<Squnion>i. Y i)"
      by (simp add: contlub_cfun_arg [OF Y] contlub_cfun_arg [OF ch2ch_Rep_cfunR [OF Y]] e)
  qed
next
  fix k :: "'k compact_basis"
  show "proj s\<cdot>(Rep_compact_basis k) \<sqsubseteq> \<kappa> \<longrightarrow>
      split_select s \<kappa>\<cdot>(split_maybe_unit\<cdot>(Rep_compact_basis k) :: ('r, 'k) split_pd) = split_maybe_unit\<cdot>(Rep_compact_basis k)"
    by (simp add: SSelect_SKey)
qed

lemma split_select_maybe_unit:
  "proj s\<cdot>k \<sqsubseteq> \<kappa> \<Longrightarrow> split_select s \<kappa>\<cdot>(split_maybe_unit\<cdot>k :: ('r, 'k) split_pd) = split_maybe_unit\<cdot>k"
  using split_select_maybe_unit_imp by blast

lemma split_select_plus: "split_select s \<kappa>\<cdot>(xs \<union>\<^sub>s ys) = split_select s \<kappa>\<cdot>xs \<union>\<^sub>s split_select s \<kappa>\<cdot>ys"
  apply (induct xs rule: split_pd.principal_induct, simp)
  apply (induct ys rule: split_pd.principal_induct, simp)
  apply (simp, rule split_principal_eqI, auto)
  done

lemma split_select_idem: "split_select s \<kappa>\<cdot>(split_select s \<kappa>\<cdot>D) = split_select s \<kappa>\<cdot>D"
  by (induct D rule: split_pd.principal_induct, simp, simp, rule split_principal_eqI, auto)

text \<open>A possible key that may end up at the part bounds the selected possible keys.\<close>

lemma split_select_keys_possible:
  assumes p: "split_possible k D" and k: "proj s\<cdot>k \<sqsubseteq> \<kappa>"
  shows "split_keys\<cdot>(split_select s \<kappa>\<cdot>D) \<sqsubseteq> down\<cdot>{k}\<sharp>"
proof -
  have u: "D \<union>\<^sub>s split_maybe_unit\<cdot>k = D" using p unfolding split_possible_def split_incl_def .
  have "split_select s \<kappa>\<cdot>D = split_select s \<kappa>\<cdot>(D \<union>\<^sub>s split_maybe_unit\<cdot>k)" by (simp only: u)
  also have "\<dots> = split_select s \<kappa>\<cdot>D \<union>\<^sub>s split_maybe_unit\<cdot>k"
    by (simp only: split_select_plus split_select_maybe_unit [OF k])
  finally have e: "split_select s \<kappa>\<cdot>D = split_select s \<kappa>\<cdot>D \<union>\<^sub>s split_maybe_unit\<cdot>k" .
  have "split_keys\<cdot>(split_select s \<kappa>\<cdot>D) \<sqsubseteq> split_keys\<cdot>(split_maybe_unit\<cdot>k :: ('r, 'k) split_pd)"
    by (subst e) (rule split_keys_plus_below)
  then show ?thesis by simp
qed

subsection \<open>Filtering by guards\<close>

text \<open>A row guard filters the definite rows to those it holds on: refining a row keeps it true, and
  the possible keys stay, since rows yet to come may pass.  A key guard filters the definite rows to
  those whose key it holds on, and the possible keys to those it is not false on: refining a key
  keeps it false.  A kept row's possible key is kept, since it lies below the row's key.\<close>

definition SRowGuard :: "('r \<rightarrow> tr) \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SRowGuard g t = SplitB {x \<in> srows t. g\<cdot>(Rep_compact_basis x) = TT} (skeys t)"

lemma srows_SRowGuard [simp]: "srows (SRowGuard g t) = {x \<in> srows t. g\<cdot>(Rep_compact_basis x) = TT}"
  and skeys_SRowGuard [simp]: "skeys (SRowGuard g t) = skeys t"
  unfolding SRowGuard_def using split_basis_consistent [of t] by (simp_all add: split_consistent_def)

lemma TT_up: "g\<cdot>x = TT \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> g\<cdot>y = TT"
proof -
  assume "g\<cdot>x = TT" "x \<sqsubseteq> y"
  then have "TT \<sqsubseteq> g\<cdot>y" by (metis monofun_cfun_arg)
  then show ?thesis by simp
qed

lemma SRowGuard_split_mono:
  assumes le: "split_le t t'"
  shows "split_le (SRowGuard g t) (SRowGuard g t')"
  unfolding split_le_def hoare_le_def smyth_le_def
proof (intro conjI ballI)
  fix x assume "x \<in> srows (SRowGuard g t)"
  then have x: "x \<in> srows t" and gx: "g\<cdot>(Rep_compact_basis x) = TT" by simp_all
  obtain y where y: "y \<in> srows t'" and xy: "x \<sqsubseteq> y" using le x unfolding split_le_def hoare_le_def by blast
  have "g\<cdot>(Rep_compact_basis y) = TT" by (rule TT_up [OF gx xy [unfolded compact_le_def]])
  then show "\<exists>y\<in>srows (SRowGuard g t'). x \<sqsubseteq> y" using y xy by auto
next
  fix v assume "v \<in> skeys (SRowGuard g t')"
  then show "\<exists>u\<in>skeys (SRowGuard g t). u \<sqsubseteq> v" using le unfolding split_le_def smyth_le_def by simp
qed

definition split_rowguard :: "('r \<rightarrow> tr) \<Rightarrow> ('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" where
  "split_rowguard g = split_pd.extension (\<lambda>t. split_principal (SRowGuard g t))"

lemma split_rowguard_principal [simp]: "split_rowguard g\<cdot>(split_principal t) = split_principal (SRowGuard g t)"
  unfolding split_rowguard_def by (simp add: split_pd.extension_principal SRowGuard_split_mono)

definition SKeyGuard :: "('k \<rightarrow> tr) \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SKeyGuard h t = SplitB {x \<in> srows t. h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = TT} {u \<in> skeys t. h\<cdot>(Rep_compact_basis u) \<noteq> FF}"

lemma keyguard_consistent:
  "split_consistent {x \<in> srows t. h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = TT} {u \<in> skeys t. h\<cdot>(Rep_compact_basis u) \<noteq> FF}"
  unfolding split_consistent_def
proof (intro ballI)
  fix x assume "x \<in> {x \<in> srows t. h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = TT}"
  then have x: "x \<in> srows t" and hx: "h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = TT" by simp_all
  obtain u where u: "u \<in> skeys t" and ux: "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
    using split_basis_consistentD [OF x] by blast
  have "h\<cdot>(Rep_compact_basis u) \<sqsubseteq> TT" using monofun_cfun_arg [OF ux, of h] hx by simp
  then have "h\<cdot>(Rep_compact_basis u) \<noteq> FF" by auto
  then show "\<exists>u\<in>{u \<in> skeys t. h\<cdot>(Rep_compact_basis u) \<noteq> FF}. Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
    using u ux by blast
qed

lemma srows_SKeyGuard [simp]: "srows (SKeyGuard h t) = {x \<in> srows t. h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = TT}"
  and skeys_SKeyGuard [simp]: "skeys (SKeyGuard h t) = {u \<in> skeys t. h\<cdot>(Rep_compact_basis u) \<noteq> FF}"
  unfolding SKeyGuard_def by (simp_all add: keyguard_consistent)

lemma FF_down: "h\<cdot>y \<noteq> FF \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> h\<cdot>x \<noteq> FF"
proof -
  assume "h\<cdot>y \<noteq> FF" "x \<sqsubseteq> y"
  have "h\<cdot>x \<sqsubseteq> h\<cdot>y" by (rule monofun_cfun_arg [OF \<open>x \<sqsubseteq> y\<close>])
  then show ?thesis using \<open>h\<cdot>y \<noteq> FF\<close> by (cases "h\<cdot>x" rule: trE) auto
qed

lemma SKeyGuard_split_mono:
  assumes le: "split_le t t'"
  shows "split_le (SKeyGuard h t) (SKeyGuard h t')"
  unfolding split_le_def hoare_le_def smyth_le_def
proof (intro conjI ballI)
  fix x assume "x \<in> srows (SKeyGuard h t)"
  then have x: "x \<in> srows t" and hx: "h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = TT" by simp_all
  obtain y where y: "y \<in> srows t'" and xy: "x \<sqsubseteq> y" using le x unfolding split_le_def hoare_le_def by blast
  have "h\<cdot>(row_key\<cdot>(Rep_compact_basis y)) = TT"
    by (rule TT_up [OF hx]) (intro monofun_cfun_arg xy [unfolded compact_le_def])
  then show "\<exists>y\<in>srows (SKeyGuard h t'). x \<sqsubseteq> y" using y xy by auto
next
  fix v assume "v \<in> skeys (SKeyGuard h t')"
  then have v: "v \<in> skeys t'" and hv: "h\<cdot>(Rep_compact_basis v) \<noteq> FF" by simp_all
  obtain u where u: "u \<in> skeys t" and uv: "u \<sqsubseteq> v" using le v unfolding split_le_def smyth_le_def by blast
  have "h\<cdot>(Rep_compact_basis u) \<noteq> FF" by (rule FF_down [OF hv uv [unfolded compact_le_def]])
  then show "\<exists>u\<in>skeys (SKeyGuard h t). u \<sqsubseteq> v" using u uv by auto
qed

definition split_keyguard :: "('k \<rightarrow> tr) \<Rightarrow> ('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" where
  "split_keyguard h = split_pd.extension (\<lambda>t. split_principal (SKeyGuard h t))"

lemma split_keyguard_principal [simp]: "split_keyguard h\<cdot>(split_principal t) = split_principal (SKeyGuard h t)"
  unfolding split_keyguard_def by (simp add: split_pd.extension_principal SKeyGuard_split_mono)

lemma split_keys_rowguard [simp]: "split_keys\<cdot>(split_rowguard g\<cdot>C) = split_keys\<cdot>C"
  by (induct C rule: split_pd.principal_induct) (simp_all add: skeys_upper_def)

lemma split_rows_principal_bot: "split_rows\<cdot>(split_principal t) = \<bottom> \<longleftrightarrow> srows t = {}"
  by (simp add: srows_lower_def)

subsection \<open>Selection as a key guard\<close>

text \<open>Selecting exactly the part \<open>\<kappa>\<close> at the LOD \<open>s\<close> is the key guard that best approximates the
  test whether a key's part is \<open>\<kappa>\<close>: true on the interior of the keys with that part, false on the
  interior of the others, undecided in between.  The keys with part \<open>\<kappa>\<close> form an open set only
  when \<open>\<kappa>\<close> is compact and maximal at \<open>s\<close> (otherwise a key there may move up, or is not finitely
  witnessed), and the interior of the others is the keys whose part is not below \<open>\<kappa>\<close> (a part
  below \<open>\<kappa>\<close> may still rise to it).  A slicer cannot ask for a part exactly, so it never meets the
  maximality condition.\<close>

definition part_test :: "'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> tr" where
  "part_test s \<kappa> k = (if compact \<kappa> \<and> maximal_at s \<kappa> \<and> proj s\<cdot>k = \<kappa> then TT else if proj s\<cdot>k \<sqsubseteq> \<kappa> then \<bottom> else FF)"

lemma part_test_mono:
  assumes le: "k \<sqsubseteq> k'"
  shows "part_test s \<kappa> k \<sqsubseteq> part_test s \<kappa> k'"
proof -
  have pk: "proj s\<cdot>k \<sqsubseteq> proj s\<cdot>k'" by (rule monofun_cfun_arg [OF le])
  show ?thesis
  proof (cases "compact \<kappa> \<and> maximal_at s \<kappa> \<and> proj s\<cdot>k = \<kappa>")
    case True
    then have "proj s\<cdot>k' = \<kappa>" using maximal_at_eq [of s \<kappa> "proj s\<cdot>k'"] pk by auto
    then show ?thesis using True unfolding part_test_def by simp
  next
    case nT: False
    show ?thesis
    proof (cases "proj s\<cdot>k \<sqsubseteq> \<kappa>")
      case True
      then have "part_test s \<kappa> k = \<bottom>" using nT unfolding part_test_def by simp
      then show ?thesis by simp
    next
      case False
      then have "\<not> proj s\<cdot>k' \<sqsubseteq> \<kappa>" using pk below_trans by blast
      then show ?thesis using nT False unfolding part_test_def by auto
    qed
  qed
qed

lemma cont_part_test: "cont (part_test s \<kappa>)"
proof (rule contI2 [OF monofunI [OF part_test_mono]])
  fix Y :: "nat \<Rightarrow> 'k" assume Y: "chain Y" and ch: "chain (\<lambda>i. part_test s \<kappa> (Y i))"
  have pY: "chain (\<lambda>i. proj s\<cdot>(Y i))" by (rule ch2ch_Rep_cfunR [OF Y])
  have pl: "proj s\<cdot>(\<Squnion>i. Y i) = (\<Squnion>i. proj s\<cdot>(Y i))" by (rule contlub_cfun_arg [OF Y])
  have stage: "part_test s \<kappa> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. part_test s \<kappa> (Y i))"
    if "part_test s \<kappa> (\<Squnion>i. Y i) = part_test s \<kappa> (Y i)" for i
    unfolding that by (rule is_ub_thelub [OF ch])
  show "part_test s \<kappa> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. part_test s \<kappa> (Y i))"
  proof (cases "compact \<kappa> \<and> maximal_at s \<kappa> \<and> proj s\<cdot>(\<Squnion>i. Y i) = \<kappa>")
    case True
    then have c: "compact \<kappa>" and mx: "maximal_at s \<kappa>" and e: "proj s\<cdot>(\<Squnion>i. Y i) = \<kappa>" by simp_all
    have "\<kappa> \<sqsubseteq> (\<Squnion>i. proj s\<cdot>(Y i))" using e pl by simp
    then obtain i where "\<kappa> \<sqsubseteq> proj s\<cdot>(Y i)" using compact_below_lub_iff [OF c pY] by blast
    then have "proj s\<cdot>(Y i) = \<kappa>" using maximal_at_eq [OF mx proj_idem] by blast
    then show ?thesis by (intro stage [of i]) (simp add: part_test_def c mx e)
  next
    case nT: False
    show ?thesis
    proof (cases "proj s\<cdot>(\<Squnion>i. Y i) \<sqsubseteq> \<kappa>")
      case True
      then have "part_test s \<kappa> (\<Squnion>i. Y i) = \<bottom>" using nT unfolding part_test_def by simp
      then show ?thesis by simp
    next
      case nB: False
      have "\<exists>i. \<not> proj s\<cdot>(Y i) \<sqsubseteq> \<kappa>"
      proof (rule ccontr)
        assume "\<not> (\<exists>i. \<not> proj s\<cdot>(Y i) \<sqsubseteq> \<kappa>)"
        then have "(\<Squnion>i. proj s\<cdot>(Y i)) \<sqsubseteq> \<kappa>" by (intro lub_below pY) simp
        then show False using nB pl by simp
      qed
      then obtain i where i: "\<not> proj s\<cdot>(Y i) \<sqsubseteq> \<kappa>" by blast
      have "part_test s \<kappa> (Y i) = FF" using i unfolding part_test_def by auto
      moreover have "part_test s \<kappa> (\<Squnion>i. Y i) = FF" using nT nB unfolding part_test_def by auto
      ultimately show ?thesis by (intro stage [of i]) simp
    qed
  qed
qed

definition at_part :: "'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'k \<rightarrow> tr" where
  "at_part s \<kappa> = (\<Lambda> k. part_test s \<kappa> k)"

lemma at_part_apply: "at_part s \<kappa>\<cdot>k = part_test s \<kappa> k"
  unfolding at_part_def by (simp add: cont_part_test)

lemma at_part_TT_iff: "at_part s \<kappa>\<cdot>k = TT \<longleftrightarrow> compact \<kappa> \<and> maximal_at s \<kappa> \<and> proj s\<cdot>k = \<kappa>"
  and at_part_FF_iff: "at_part s \<kappa>\<cdot>k = FF \<longleftrightarrow> \<not> proj s\<cdot>k \<sqsubseteq> \<kappa>"
  unfolding at_part_apply part_test_def by auto

text \<open>At a compact part, selection is the key guard of the part test.\<close>

lemma SSelect_keyguard: "compact \<kappa> \<Longrightarrow> SSelect s \<kappa> t = SKeyGuard (at_part s \<kappa>) t"
  by (rule split_basis_eqI) (auto simp: at_part_TT_iff at_part_FF_iff)

lemma split_select_keyguard: "compact \<kappa> \<Longrightarrow> split_select s \<kappa> = split_keyguard (at_part s \<kappa>)"
  by (rule cfun_eqI, induct_tac x rule: split_pd.principal_induct) (simp_all add: SSelect_keyguard)

text \<open>Key guards compose by conjunction.\<close>

lemma SKeyGuard_pand: "SKeyGuard h\<^sub>1 (SKeyGuard h\<^sub>2 t) = SKeyGuard (\<Lambda> k. pand\<cdot>(h\<^sub>1\<cdot>k)\<cdot>(h\<^sub>2\<cdot>k)) t"
  by (rule split_basis_eqI) (auto simp: pand_TT_iff pand_FF_iff)

lemma split_keyguard_pand:
  "split_keyguard h\<^sub>1\<cdot>(split_keyguard h\<^sub>2\<cdot>D) = split_keyguard (\<Lambda> k. pand\<cdot>(h\<^sub>1\<cdot>k)\<cdot>(h\<^sub>2\<cdot>k))\<cdot>D"
proof (induct D rule: split_pd.principal_induct)
  case (2 t)
  show ?case unfolding split_keyguard_principal by (rule arg_cong [where f = split_principal], rule SKeyGuard_pand)
qed simp

subsection \<open>Refutation by a key test\<close>

text \<open>A key test refutes the part when it is false on every selected possible key: the selected
  keys, mapped through the test, are no keys at all or only false.  The test is monotone in the
  dataset, and decided at a finite stage.\<close>

lemma compact_down: "compact x \<Longrightarrow> compact (down\<cdot>x)"
  unfolding compact_def
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a top"
  assume c: "adm (\<lambda>y. \<not> x \<sqsubseteq> y)" and Y: "chain Y" and n: "\<forall>i. \<not> down\<cdot>x \<sqsubseteq> Y i"
  from Y show "\<not> down\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)"
  proof (cases rule: top_chain_cases)
    case (down X)
    have "\<not> x \<sqsubseteq> X i" for i using n down(2) by (simp add: down_beta below_Of)
    then have "\<not> x \<sqsubseteq> (\<Squnion>i. X i)" using compact_below_lub_iff [OF c [folded compact_def] down(1)] by blast
    then show ?thesis using down(3) by (simp add: down_beta below_Of)
  next
    case Top
    then obtain i where "Y i = Top" by blast
    then show ?thesis using n below_Top by metis
  qed
qed

definition split_refuted :: "'k semi_factor \<Rightarrow> 'k \<Rightarrow> ('k \<rightarrow> tr) \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> bool" where
  "split_refuted s \<kappa> h D \<longleftrightarrow> down\<cdot>{FF}\<sharp> \<sqsubseteq> cmap_top\<cdot>(upper_map\<cdot>h)\<cdot>(split_keys\<cdot>(split_select s \<kappa>\<cdot>D))"

lemma split_refuted_mono: "split_refuted s \<kappa> h D \<Longrightarrow> D \<sqsubseteq> D' \<Longrightarrow> split_refuted s \<kappa> h D'"
  unfolding split_refuted_def by (erule below_trans) (intro monofun_cfun_arg)

lemma split_refuted_lub:
  assumes Y: "chain Y" and r: "split_refuted s \<kappa> h (\<Squnion>i. Y i)"
  obtains i where "split_refuted s \<kappa> h (Y i)"
proof -
  let ?F = "\<lambda>D. cmap_top\<cdot>(upper_map\<cdot>h)\<cdot>(split_keys\<cdot>(split_select s \<kappa>\<cdot>D))"
  have ch: "chain (\<lambda>i. ?F (Y i))" by (intro ch2ch_Rep_cfunR Y)
  have "?F (\<Squnion>i. Y i) = (\<Squnion>i. ?F (Y i))"
    by (simp only: contlub_cfun_arg [OF Y] contlub_cfun_arg [OF ch2ch_Rep_cfunR [OF Y]]
        contlub_cfun_arg [OF ch2ch_Rep_cfunR [OF ch2ch_Rep_cfunR [OF Y]]])
  then have "down\<cdot>{FF}\<sharp> \<sqsubseteq> (\<Squnion>i. ?F (Y i))" using r unfolding split_refuted_def by simp
  then obtain i where "down\<cdot>{FF}\<sharp> \<sqsubseteq> ?F (Y i)"
    using compact_below_lub_iff [OF compact_down [OF compact_upper_unit [OF compact_FF]] ch] by blast
  then show ?thesis using that unfolding split_refuted_def by blast
qed

text \<open>Refutation is the key guard leaving no possible keys: the possible keys mapped through the
  key test are all false exactly when the key guard drops all of them.  On a finite set of keys this
  is a computation; in general both sides are decided at a finite stage.\<close>

lemma upper_map_principal_FF:
  "{FF}\<sharp> \<sqsubseteq> upper_map\<cdot>h\<cdot>(upper_principal P) \<longleftrightarrow> (\<forall>u\<in>Rep_pd_basis P. h\<cdot>(Rep_compact_basis u) = FF)"
proof (induct P rule: pd_basis_induct)
  case (PDUnit a)
  show ?case by (simp add: upper_unit_Rep_compact_basis [symmetric] Rep_PDUnit del: upper_unit_Rep_compact_basis)
next
  case (PDPlus t u)
  show ?case
    by (simp add: upper_plus_principal [symmetric] Rep_PDPlus PDPlus.hyps del: upper_plus_principal) blast
qed

lemma keys_refuted_principal:
  "down\<cdot>{FF}\<sharp> \<sqsubseteq> cmap_top\<cdot>(upper_map\<cdot>h)\<cdot>(split_keys\<cdot>(split_principal t :: ('r, 'k) split_pd)) \<longleftrightarrow>
     split_keys\<cdot>(split_keyguard h\<cdot>(split_principal t :: ('r, 'k) split_pd)) = Top"
proof (cases "skeys t = {}")
  case True
  then show ?thesis by (simp add: skeys_upper_def)
next
  case False
  have K: "Rep_pd_basis (Abs_pd_basis (skeys t)) = skeys t"
    by (rule Abs_pd_basis_inverse) (simp add: pd_basis_def False)
  have "down\<cdot>{FF}\<sharp> \<sqsubseteq> cmap_top\<cdot>(upper_map\<cdot>h)\<cdot>(split_keys\<cdot>(split_principal t :: ('r, 'k) split_pd)) \<longleftrightarrow>
      (\<forall>u\<in>skeys t. h\<cdot>(Rep_compact_basis u) = FF)"
  proof -
    have e: "split_keys\<cdot>(split_principal t :: ('r, 'k) split_pd) = down\<cdot>(upper_principal (Abs_pd_basis (skeys t)))"
      by (simp add: skeys_upper_def False)
    show ?thesis unfolding e cmap_top_down unfolding down_beta below_Of upper_map_principal_FF K ..
  qed
  moreover have "split_keys\<cdot>(split_keyguard h\<cdot>(split_principal t :: ('r, 'k) split_pd)) = Top \<longleftrightarrow>
      (\<forall>u\<in>skeys t. h\<cdot>(Rep_compact_basis u) = FF)"
    by (auto simp: skeys_upper_def down_beta)
  ultimately show ?thesis by simp
qed

lemma keys_refuted_iff:
  "down\<cdot>{FF}\<sharp> \<sqsubseteq> cmap_top\<cdot>(upper_map\<cdot>h)\<cdot>(split_keys\<cdot>E) \<longleftrightarrow> split_keys\<cdot>(split_keyguard h\<cdot>E) = Top"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and EZ: "E = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  let ?F = "\<lambda>E. cmap_top\<cdot>(upper_map\<cdot>h)\<cdot>(split_keys\<cdot>E)" and ?G = "\<lambda>E. split_keys\<cdot>(split_keyguard h\<cdot>E)"
  have chF: "chain (\<lambda>i. ?F (split_principal (Z i)))" and chG: "chain (\<lambda>i. ?G (split_principal (Z i)))"
    by (intro ch2ch_Rep_cfunR ch)+
  have F: "?F E = (\<Squnion>i. ?F (split_principal (Z i)))"
    unfolding EZ by (simp only: contlub_cfun_arg [OF ch] contlub_cfun_arg [OF ch2ch_Rep_cfunR [OF ch]])
  have G: "?G E = (\<Squnion>i. ?G (split_principal (Z i)))"
    unfolding EZ by (simp only: contlub_cfun_arg [OF ch] contlub_cfun_arg [OF ch2ch_Rep_cfunR [OF ch]])
  have "down\<cdot>{FF}\<sharp> \<sqsubseteq> ?F E \<longleftrightarrow> (\<exists>i. down\<cdot>{FF}\<sharp> \<sqsubseteq> ?F (split_principal (Z i)))"
    unfolding F by (rule compact_below_lub_iff [OF compact_down [OF compact_upper_unit [OF compact_FF]] chF])
  also have "\<dots> \<longleftrightarrow> (\<exists>i. Top \<sqsubseteq> ?G (split_principal (Z i)))" by (simp only: Top_below keys_refuted_principal)
  also have "\<dots> \<longleftrightarrow> Top \<sqsubseteq> ?G E"
    unfolding G by (rule compact_below_lub_iff [OF compact_Top chG, symmetric])
  finally show ?thesis by simp
qed

lemma split_refuted_keyguard:
  "split_refuted s \<kappa> h D \<longleftrightarrow> split_keys\<cdot>(split_keyguard h\<cdot>(split_select s \<kappa>\<cdot>D)) = Top"
  unfolding split_refuted_def by (rule keys_refuted_iff)

text \<open>A refuted part has no possible key there on which the test is not false.\<close>

lemma split_refuted_possible:
  assumes r: "split_refuted s \<kappa> h D" and p: "split_possible k D" and k: "proj s\<cdot>k \<sqsubseteq> \<kappa>"
  shows "h\<cdot>k = FF"
proof -
  have b: "cmap_top\<cdot>(upper_map\<cdot>h)\<cdot>(split_keys\<cdot>(split_select s \<kappa>\<cdot>D)) \<sqsubseteq> down\<cdot>{h\<cdot>k}\<sharp>"
    using monofun_cfun_arg [OF split_select_keys_possible [OF p k], of "cmap_top\<cdot>(upper_map\<cdot>h)"] by simp
  have "down\<cdot>{FF}\<sharp> \<sqsubseteq> down\<cdot>{h\<cdot>k}\<sharp>" by (rule below_trans [OF r [unfolded split_refuted_def] b])
  then have "FF \<sqsubseteq> h\<cdot>k" by (simp add: down_beta below_Of)
  then show ?thesis by simp
qed

end

end
