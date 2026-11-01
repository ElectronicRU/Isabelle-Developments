theory Split_Content
  imports SplitPD
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

end

end
