theory Split_Semantics
  imports Expr_Combinators SplitPD
begin

default_sort type

section \<open>Semantics over split datasets\<close>

text \<open>The rigid semantics reads a dataset's definite rows, as a lower powerdomain.  The
  \<^emph>\<open>extended\<close> semantics reads a split dataset, definite rows and possible keys, and is defined
  combinator by combinator.  Its law is soundness against the rigid one: below every compact
  dataset above it that has rows, what it says is what the rigid semantics says on that dataset's
  rows.  It need not be exact there.\<close>

subsection \<open>Rows of compact split datasets\<close>

lemma lower_mem_Abs_pd_basis:
  assumes "finite S" "S \<noteq> {}"
  shows "x \<in>\<flat> lower_principal (Abs_pd_basis S) \<longleftrightarrow> (\<exists>s\<in>S. x \<sqsubseteq> Rep_compact_basis s)"
  using assms
proof (induct S rule: finite_ne_induct)
  case (singleton a)
  show ?case
    unfolding Abs_pd_basis_singleton lower_unit_Rep_compact_basis [symmetric] lower_mem_principal by simp
next
  case (insert a S)
  have eq: "Abs_pd_basis (insert a S) = PDPlus (PDUnit a) (Abs_pd_basis S)"
    unfolding PDPlus_def Rep_PDUnit using insert by (simp add: Abs_pd_basis_inverse pd_basis_def)
  show ?case
    unfolding eq lower_plus_principal [symmetric] lower_unit_Rep_compact_basis [symmetric] lower_mem_union lower_mem_principal
    using insert by simp
qed

lemma split_rows_mem_principal:
  "srows t \<noteq> {} \<Longrightarrow> x \<in>\<flat> split_rows\<cdot>(split_principal t) \<longleftrightarrow> (\<exists>s\<in>srows t. x \<sqsubseteq> Rep_compact_basis s)"
  by (simp add: srows_lower_def lower_mem_Abs_pd_basis)

lemma split_definite_rows_mem: "split_definite x xs \<Longrightarrow> x \<in>\<flat> split_rows\<cdot>xs"
  unfolding split_definite_def lower_mem_equiv
  by (drule monofun_cfun_arg [of _ _ split_rows]) simp

lemma split_definite_bottom_principal:
  "split_definite \<bottom> (split_principal t :: ('r::bifinite, 'k::bifinite) split_pd) \<longleftrightarrow> srows t \<noteq> {}"
  using split_definite_principal [of compact_bot t] by (auto simp: compact_bot_minimal)

text \<open>The maximal rows of a compact dataset with rows are among its generators.\<close>

lemma split_maximal_row_generator:
  assumes m: "x \<in> lower_maximal (split_rows\<cdot>(split_principal t))" and ne: "srows t \<noteq> {}"
  shows "\<exists>s\<in>srows t. x = Rep_compact_basis s"
proof -
  have "x \<in>\<flat> split_rows\<cdot>(split_principal t)" using m by (simp add: lower_maximal_def)
  then obtain s where s: "s \<in> srows t" "x \<sqsubseteq> Rep_compact_basis s" using split_rows_mem_principal [OF ne] by blast
  have "Rep_compact_basis s \<in>\<flat> split_rows\<cdot>(split_principal t)" using split_rows_mem_principal [OF ne] s(1) by blast
  then have "Rep_compact_basis s = x" using m s(2) by (simp add: lower_maximal_def)
  then show ?thesis using s(1) by blast
qed

text \<open>A compact key possible in a compact dataset is possible below it.\<close>

lemma split_possible_below_principal:
  assumes k: "split_possible (Rep_compact_basis k) (split_principal t :: ('r::bifinite, 'k::bifinite) split_pd)"
    and D: "D \<sqsubseteq> split_principal t"
  shows "split_possible (Rep_compact_basis k) D"
proof -
  obtain u where u: "u \<in> skeys t" "u \<sqsubseteq> k" using k by (auto simp: split_possible_principal)
  have "D \<sqsubseteq> split_principal t \<longrightarrow> split_possible (Rep_compact_basis k) D"
  proof (induct D rule: split_pd.principal_induct)
    case 1
    show ?case unfolding split_possible_def split_incl_def by (intro adm_imp adm_not_below adm_eq) simp_all
  next
    case (2 s)
    show ?case
    proof
      assume "split_principal s \<sqsubseteq> split_principal t"
      then have "smyth_le (skeys s) (skeys t)" by (simp add: split_le_def)
      then obtain w where "w \<in> skeys s" "w \<sqsubseteq> u" using u(1) by (auto simp: smyth_le_def)
      then show "split_possible (Rep_compact_basis k) (split_principal s)"
        using u(2) by (auto simp: split_possible_principal intro: below_trans)
    qed
  qed
  then show ?thesis using D by blast
qed


subsection \<open>Expressions with an extended semantics\<close>

text \<open>An extended expression is an expression with a semantics over split datasets as well.\<close>

record ('k::"domain", 'f::type, 'r::"{bifinite, distributive_cpo}", 'v::bifinite) expr_ext = "('k, 'f, 'r, 'v) expr" +
  sem_ext :: "('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd"

hide_const (open) expr_ext.truncate

text \<open>An expression extended by a semantics over split datasets.\<close>

definition with_ext :: "('k::domain, 'f, 'r::{bifinite, distributive_cpo}, 'v::bifinite) expr \<Rightarrow>
    (('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "with_ext E s = expr.extend E (expr_ext.fields s)"

lemma with_ext_simps [simp]:
  "emind (with_ext E s) = emind E" "eguards (with_ext E s) = eguards E" "evalues (with_ext E s) = evalues E"
  
  "esem (with_ext E s) = esem E" "csem (with_ext E s) = csem E" "sem_ext (with_ext E s) = s"
  by (simp_all add: with_ext_def expr.defs expr_ext.defs)


text \<open>The row key of split datasets is the keying's.\<close>

locale split_dataspace = dataspace slicing rules keying + split_keyed keying
  for slicing :: "('f, 'k::{domain, lod_domain}) slicer_ops"
    and rules :: "'r::{domain, lod_domain} schema_rules" and keying :: "('r, 'k) keying"
begin

text \<open>\<^emph>\<open>Soundness\<close>: below a compact dataset with rows, conforming relative to the rigid
  expression's value entries, the extended semantics is below the rigid semantics of that
  dataset's rows, at every key of the key LOD.  Compact datasets with rows are where the rigid
  semantics is meant: it reads no possible keys, and it cannot see the empty dataset, whose
  rows are \<open>\<bottom>\<close>.  An \<^emph>\<open>extended-lawful\<close> expression is moreover semilawful.\<close>

definition ext_sound :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> bool" where
  "ext_sound X \<longleftrightarrow> (\<forall>D D' F k. D \<sqsubseteq> D' \<longrightarrow> compact D' \<longrightarrow> split_definite (\<bottom>::'r) D' \<longrightarrow>
     fconf (evalues X) (split_rows\<cdot>D') F \<longrightarrow> proj (kd X F)\<cdot>k = k \<longrightarrow>
     sem_ext X D F k \<sqsubseteq> esem X (split_rows\<cdot>D') F k)"

lemma ext_soundI:
  "(\<And>D D' F k. D \<sqsubseteq> D' \<Longrightarrow> compact D' \<Longrightarrow> split_definite (\<bottom>::'r) D' \<Longrightarrow>
     fconf (evalues X) (split_rows\<cdot>D') F \<Longrightarrow> proj (kd X F)\<cdot>k = k \<Longrightarrow>
     sem_ext X D F k \<sqsubseteq> esem X (split_rows\<cdot>D') F k) \<Longrightarrow> ext_sound X"
  unfolding ext_sound_def by blast

lemma ext_soundD:
  "ext_sound X \<Longrightarrow> D \<sqsubseteq> D' \<Longrightarrow> compact D' \<Longrightarrow> split_definite (\<bottom>::'r) D' \<Longrightarrow>
     fconf (evalues X) (split_rows\<cdot>D') F \<Longrightarrow> proj (kd X F)\<cdot>k = k \<Longrightarrow>
     sem_ext X D F k \<sqsubseteq> esem X (split_rows\<cdot>D') F k"
  unfolding ext_sound_def by blast

lemma semilawful_with_ext [simp]: "semilawful (with_ext E s) \<longleftrightarrow> semilawful E"
  by (simp add: semilawful_def cstrict_def)

definition ext_lawful :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> bool" where
  "ext_lawful X \<longleftrightarrow> semilawful X \<and> ext_sound X"


subsection \<open>Keys\<close>

text \<open>The key at an LOD \<open>c\<close> is present where some definite row has it, provided it is maximal
  at \<open>c\<close> (a row at a partial key may still move up), and absent where no possible key projects
  below it.  Otherwise it is undecided.\<close>

definition key_at_ext :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'k) expr_ext" where
  "key_at_ext c = with_ext (key_at c) (\<lambda>D F k. if maximal_at c (proj c\<cdot>k) \<and> (\<exists>y. split_definite y D \<and> rproj c y = proj c\<cdot>k)
       then Present\<cdot>(proj c\<cdot>k)
       else if \<exists>u::'k. split_possible u D \<and> proj c\<cdot>u \<sqsubseteq> proj c\<cdot>k then \<bottom> else Absent)"

lemma key_at_ext_simps [simp]:
  "semilawful (key_at_ext c) \<longleftrightarrow> semilawful (key_at c)"
  "emind (key_at_ext c) = emind (key_at c)" "eguards (key_at_ext c) = eguards (key_at c)" "evalues (key_at_ext c) = evalues (key_at c)"
  "esem (key_at_ext c) = esem (key_at c)" "csem (key_at_ext c) = csem (key_at c)"
  "sem_ext (key_at_ext c) D F k = (if maximal_at c (proj c\<cdot>k) \<and> (\<exists>y. split_definite y D \<and> rproj c y = proj c\<cdot>k)
     then Present\<cdot>(proj c\<cdot>k)
     else if \<exists>u::'k. split_possible u D \<and> proj c\<cdot>u \<sqsubseteq> proj c\<cdot>k then \<bottom> else Absent)"
  by (simp_all add: key_at_ext_def)

theorem ext_sound_key_at: "ext_sound (key_at_ext c)"
proof (rule ext_soundI, simp only: key_at_ext_simps)
  fix D D' :: "('r, 'k) split_pd" and F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_definite (\<bottom>::'r) D'"
  let ?data = "split_rows\<cdot>D'"
  have fib: "fiber ?data c c F k = {m \<in> lower_maximal ?data. rproj c m = proj c\<cdot>k}"
    by (simp add: fiber_def join_meet_self)
  obtain t where t: "D' = split_principal t" using split_pd.compact_imp_principal [OF cD] by blast
  have ne: "srows t \<noteq> {}" using nD unfolding t split_definite_bottom_principal .
  show "(if maximal_at c (proj c\<cdot>k) \<and> (\<exists>y. split_definite y D \<and> rproj c y = proj c\<cdot>k) then Present\<cdot>(proj c\<cdot>k)
      else if \<exists>u::'k. split_possible u D \<and> proj c\<cdot>u \<sqsubseteq> proj c\<cdot>k then \<bottom> else Absent)
    \<sqsubseteq> esem (key_at c) ?data F k"
  proof (cases "maximal_at c (proj c\<cdot>k) \<and> (\<exists>y. split_definite y D \<and> rproj c y = proj c\<cdot>k)")
    case True
    then obtain y where mx: "maximal_at c (proj c\<cdot>k)" and y: "split_definite y D" "rproj c y = proj c\<cdot>k" by blast
    have "y \<in>\<flat> ?data" by (rule split_definite_rows_mem [OF split_definite_mono [OF y(1) DD]])
    then obtain m where m: "m \<in> lower_maximal ?data" "y \<sqsubseteq> m" by (rule lower_mem_maximal_above)
    have "proj c\<cdot>k \<sqsubseteq> rproj c m" unfolding y(2) [symmetric] by (intro monofun_cfun_arg m(2))
    then have "rproj c m = proj c\<cdot>k" by (rule maximal_at_eq [OF mx proj_idem])
    then have "fiber ?data c c F k \<noteq> {}" using m(1) fib by blast
    then show ?thesis using True by simp
  next
    case nP: False
    show ?thesis
    proof (cases "\<exists>u. split_possible u D \<and> proj c\<cdot>u \<sqsubseteq> proj c\<cdot>k")
      case True
      show ?thesis by (simp only: if_not_P [OF nP] if_P [OF True] minimal)
    next
      case nA: False
      have "fiber ?data c c F k = {}"
      proof (rule ccontr)
        assume "fiber ?data c c F k \<noteq> {}"
        then obtain m where m: "m \<in> lower_maximal ?data" "rproj c m = proj c\<cdot>k" using fib by blast
        obtain s where s: "s \<in> srows t" "m = Rep_compact_basis s"
          using split_maximal_row_generator [OF m(1) [unfolded t] ne] by blast
        obtain u where u: "u \<in> skeys t" "Rep_compact_basis u \<sqsubseteq> rkey\<cdot>m"
          using split_basis_consistentD [OF s(1)] unfolding split_key_rkey s(2) by blast
        have "split_possible (Rep_compact_basis u) (split_principal t :: ('r, 'k) split_pd)"
          using u(1) by (auto simp: split_possible_principal)
        then have "split_possible (Rep_compact_basis u) D"
          by (rule split_possible_below_principal) (simp only: DD [unfolded t])
        moreover have "proj c\<cdot>(Rep_compact_basis u) \<sqsubseteq> proj c\<cdot>k"
          unfolding m(2) [symmetric] by (rule monofun_cfun_arg [OF u(2)])
        ultimately show False using nA by blast
      qed
      then show ?thesis by (simp only: if_not_P [OF nP] if_not_P [OF nA] key_at_simps) simp
    qed
  qed
qed

theorem ext_lawful_key_at: "ext_lawful (key_at_ext c)"
  unfolding ext_lawful_def by (simp add: semilawful_key_at ext_sound_key_at)


subsection \<open>Constants and maps\<close>

definition const_ext :: "'v::bifinite \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "const_ext v = with_ext (const_expr v) (\<lambda>D F k. Present\<cdot>v)"

lemma const_ext_simps [simp]:
  "semilawful (const_ext v) \<longleftrightarrow> semilawful (const_expr v)"
  "emind (const_ext v) = emind (const_expr v)" "eguards (const_ext v) = eguards (const_expr v)" "evalues (const_ext v) = evalues (const_expr v)"
  "esem (const_ext v) = esem (const_expr v)" "csem (const_ext v) = csem (const_expr v)"
  "sem_ext (const_ext v) D F k = Present\<cdot>v"
  by (simp_all add: const_ext_def)

theorem ext_lawful_const: "ext_lawful (const_ext v)"
  unfolding ext_lawful_def by (auto simp: semilawful_const_expr intro: ext_soundI)

definition smap_ext :: "('v::bifinite \<rightarrow> 'w::bifinite) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext \<Rightarrow> ('k, 'f, 'r, 'w) expr_ext" where
  "smap_ext g X = with_ext (smap g X) (\<lambda>D F k. map_option_pd g\<cdot>(sem_ext X D F k))"

lemma smap_ext_simps [simp]:
  "semilawful (smap_ext g X) \<longleftrightarrow> semilawful (smap g X)"
  "emind (smap_ext g X) = emind (smap g X)" "eguards (smap_ext g X) = eguards (smap g X)" "evalues (smap_ext g X) = evalues (smap g X)"
  "esem (smap_ext g X) = esem (smap g X)" "csem (smap_ext g X) = csem (smap g X)"
  "sem_ext (smap_ext g X) D F k = map_option_pd g\<cdot>(sem_ext X D F k)"
  by (simp_all add: smap_ext_def)

theorem ext_sound_smap: "ext_sound X \<Longrightarrow> ext_sound (smap_ext g X)"
  by (rule ext_soundI) (simp add: monofun_cfun_arg ext_soundD)

theorem ext_lawful_smap: "ext_lawful X \<Longrightarrow> ext_lawful (smap_ext g X)"
  unfolding ext_lawful_def by (simp add: semilawful_smap ext_sound_smap)

abbreviation value_at_ext :: "'k semi_factor \<Rightarrow> ('k \<rightarrow> 'v::bifinite) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "value_at_ext c g \<equiv> smap_ext g (key_at_ext c)"


subsection \<open>Frame transformers\<close>

definition restrict_ext :: "'r guard \<Rightarrow> ('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "restrict_ext \<gamma> X = with_ext (restrict \<gamma> X) (\<lambda>D F. sem_ext X D (frestrict \<gamma> F))"

lemma restrict_ext_simps [simp]:
  "semilawful (restrict_ext \<gamma> X) \<longleftrightarrow> semilawful (restrict \<gamma> X)"
  "emind (restrict_ext \<gamma> X) = emind (restrict \<gamma> X)" "eguards (restrict_ext \<gamma> X) = eguards (restrict \<gamma> X)" "evalues (restrict_ext \<gamma> X) = evalues (restrict \<gamma> X)"
  "esem (restrict_ext \<gamma> X) = esem (restrict \<gamma> X)" "csem (restrict_ext \<gamma> X) = csem (restrict \<gamma> X)"
  "sem_ext (restrict_ext \<gamma> X) D F = sem_ext X D (frestrict \<gamma> F)"
  by (simp_all add: restrict_ext_def)

theorem ext_sound_restrict: "ext_sound X \<Longrightarrow> ext_sound (restrict_ext \<gamma> X)"
  by (rule ext_soundI) (simp add: ext_soundD fconf_frestrict)

theorem ext_lawful_restrict: "ext_lawful X \<Longrightarrow> ext_lawful (restrict_ext \<gamma> X)"
  unfolding ext_lawful_def by (simp add: semilawful_restrict ext_sound_restrict)

definition filtfor_ext :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "filtfor_ext \<tau> G X = with_ext (filtfor \<tau> G X) (\<lambda>D F k. sem_ext X D (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k))"

lemma filtfor_ext_simps [simp]:
  "semilawful (filtfor_ext \<tau> G X) \<longleftrightarrow> semilawful (filtfor \<tau> G X)"
  "emind (filtfor_ext \<tau> G X) = emind (filtfor \<tau> G X)" "eguards (filtfor_ext \<tau> G X) = eguards (filtfor \<tau> G X)" "evalues (filtfor_ext \<tau> G X) = evalues (filtfor \<tau> G X)"
  "esem (filtfor_ext \<tau> G X) = esem (filtfor \<tau> G X)" "csem (filtfor_ext \<tau> G X) = csem (filtfor \<tau> G X)"
  "sem_ext (filtfor_ext \<tau> G X) D F k = sem_ext X D (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k)"
  by (simp_all add: filtfor_ext_def)

theorem ext_sound_filtfor: "ext_sound X \<Longrightarrow> ext_sound (filtfor_ext \<tau> G X)"
proof (rule ext_soundI, simp only: filtfor_ext_simps filtfor_simps)
  fix D D' :: "('r, 'k) split_pd" and F k
  assume X: "ext_sound X" and DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_definite (\<bottom>::'r) D'"
    and d: "fconf (map (for_value \<tau>) (evalues X)) (split_rows\<cdot>D') F"
  have d': "fconf (evalues X) (split_rows\<cdot>D') (ffor \<tau> G F)" using d by (simp only: fconf_filtfor [of _ _ _ _ G])
  show "sem_ext X D (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k)
      \<sqsubseteq> esem X (split_rows\<cdot>D') (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k)"
    by (rule ext_soundD [OF X DD cD nD d' proj_idem])
qed

theorem ext_lawful_filtfor: "ext_lawful X \<Longrightarrow> ext_lawful (filtfor_ext \<tau> G X)"
  unfolding ext_lawful_def by (simp add: semilawful_filtfor ext_sound_filtfor)

text \<open>Including dimensions raises the frame LOD; the key LOD of a semilawful inner expression in
  the raised frame covers the outer one.\<close>

lemma include_dims_kd_below:
  assumes ES: "semilawful E"
  shows "kd (include_dims M E) F \<sqsubseteq> kd E (finclude M F)"
proof -
  let ?n = "fold (\<squnion>) (map (\<lambda>S. lower_part (include_sel M S)) (esels E)) \<bottom>"
  have le: "?n \<sqsubseteq> emind E \<squnion> M"
  proof (rule fold_join_least)
    fix x assume "x \<in> set (map (\<lambda>S. lower_part (include_sel M S)) (esels E))"
    then obtain S where S: "S \<in> set (esels E)" and x: "x = lower_part (include_sel M S)" by auto
    show "x \<sqsubseteq> emind E \<squnion> M" unfolding x include_sel_simps
      by (rule lattice_join_mono [OF lower_below_mind [OF ES S] truncate_below])
  qed simp
  have "?n \<squnion> flod F \<sqsubseteq> (emind E \<squnion> M) \<squnion> flod F" by (rule lattice_join_mono [OF le below_refl])
  also have "\<dots> = emind E \<squnion> flod (finclude M F)" unfolding flod_finclude by (simp only: lattice_join_ac)
  finally show ?thesis by simp
qed

definition include_dims_ext :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "include_dims_ext M X = with_ext (include_dims M X) (\<lambda>D F. sem_ext X D (finclude M F))"

lemma include_dims_ext_simps [simp]:
  "semilawful (include_dims_ext M X) \<longleftrightarrow> semilawful (include_dims M X)"
  "emind (include_dims_ext M X) = emind (include_dims M X)" "eguards (include_dims_ext M X) = eguards (include_dims M X)" "evalues (include_dims_ext M X) = evalues (include_dims M X)"
  "esem (include_dims_ext M X) = esem (include_dims M X)" "csem (include_dims_ext M X) = csem (include_dims M X)"
  "sem_ext (include_dims_ext M X) D F = sem_ext X D (finclude M F)"
  by (simp_all add: include_dims_ext_def)

theorem ext_sound_include_dims:
  assumes ES: "semilawful X" and X: "ext_sound X"
  shows "ext_sound (include_dims_ext M X)"
proof (rule ext_soundI, simp only: include_dims_ext_simps include_dims_simps(3,4))
  fix D D' :: "('r, 'k) split_pd" and F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_definite (\<bottom>::'r) D'"
    and d: "fconf (map (include_entry M) (evalues X)) (split_rows\<cdot>D') F"
    and k: "proj (kd (include_dims M X) F)\<cdot>k = k"
  have d': "fconf (evalues X) (split_rows\<cdot>D') (finclude M F)" using d by (simp only: fconf_include)
  have k': "proj (kd X (finclude M F))\<cdot>k = k" by (rule proj_fix_mono [OF include_dims_kd_below [OF ES] k])
  show "sem_ext X D (finclude M F) k \<sqsubseteq> esem X (split_rows\<cdot>D') (finclude M F) k"
    by (rule ext_soundD [OF X DD cD nD d' k'])
qed

theorem ext_lawful_include_dims: "ext_lawful X \<Longrightarrow> ext_lawful (include_dims_ext M X)"
  unfolding ext_lawful_def by (simp add: semilawful_include_dims ext_sound_include_dims)


subsection \<open>Combining\<close>

definition combine_ext :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<Rightarrow> ('k, 'f, 'r, 'a::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'b::bifinite) expr_ext \<Rightarrow>
    ('k, 'f, 'r, 'c::bifinite) expr_ext" where
  "combine_ext f X\<^sub>1 X\<^sub>2 = with_ext (combine f X\<^sub>1 X\<^sub>2) (\<lambda>D F k. lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 D F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 D F (proj (kd X\<^sub>2 F)\<cdot>k)))"

lemma combine_ext_simps [simp]:
  "semilawful (combine_ext f X\<^sub>1 X\<^sub>2) \<longleftrightarrow> semilawful (combine f X\<^sub>1 X\<^sub>2)"
  "emind (combine_ext f X\<^sub>1 X\<^sub>2) = emind (combine f X\<^sub>1 X\<^sub>2)" "eguards (combine_ext f X\<^sub>1 X\<^sub>2) = eguards (combine f X\<^sub>1 X\<^sub>2)" "evalues (combine_ext f X\<^sub>1 X\<^sub>2) = evalues (combine f X\<^sub>1 X\<^sub>2)"
  "esem (combine_ext f X\<^sub>1 X\<^sub>2) = esem (combine f X\<^sub>1 X\<^sub>2)" "csem (combine_ext f X\<^sub>1 X\<^sub>2) = csem (combine f X\<^sub>1 X\<^sub>2)"
  "sem_ext (combine_ext f X\<^sub>1 X\<^sub>2) D F k =
     lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 D F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 D F (proj (kd X\<^sub>2 F)\<cdot>k))"
  by (simp_all add: combine_ext_def)

theorem ext_sound_combine:
  assumes X\<^sub>1: "ext_sound X\<^sub>1" and X\<^sub>2: "ext_sound X\<^sub>2"
  shows "ext_sound (combine_ext f X\<^sub>1 X\<^sub>2)"
proof (rule ext_soundI, simp only: combine_ext_simps combine_simps)
  fix D D' :: "('r, 'k) split_pd" and F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_definite (\<bottom>::'r) D'"
    and d: "fconf (evalues X\<^sub>1 @ evalues X\<^sub>2) (split_rows\<cdot>D') F"
  have d1: "fconf (evalues X\<^sub>1) (split_rows\<cdot>D') F" and d2: "fconf (evalues X\<^sub>2) (split_rows\<cdot>D') F"
    using d by (simp_all add: fconf_def)
  show "lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 D F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 D F (proj (kd X\<^sub>2 F)\<cdot>k))
      \<sqsubseteq> lift2_option_pd f\<cdot>(esem X\<^sub>1 (split_rows\<cdot>D') F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>
          (esem X\<^sub>2 (split_rows\<cdot>D') F (proj (kd X\<^sub>2 F)\<cdot>k))"
    by (rule monofun_cfun [OF monofun_cfun_arg ext_soundD [OF X\<^sub>2 DD cD nD d2 proj_idem]],
        rule ext_soundD [OF X\<^sub>1 DD cD nD d1 proj_idem])
qed

theorem ext_lawful_combine: "ext_lawful X\<^sub>1 \<Longrightarrow> ext_lawful X\<^sub>2 \<Longrightarrow> ext_lawful (combine_ext f X\<^sub>1 X\<^sub>2)"
  unfolding ext_lawful_def by (simp add: semilawful_combine ext_sound_combine)

end

end
