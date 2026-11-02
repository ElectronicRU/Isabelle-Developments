theory Key_Mix
  imports Split_Semantics "HOLCF-extra.MixPD"
begin

default_sort type

section \<open>Key mixes\<close>

text \<open>A guard entry reads a split dataset only for the presence of keys at a key LOD: present
  where a definite row has the key, refuted where no possible key may end up there.  The keys of
  the definite rows and the possible keys form a \<^emph>\<open>key mix\<close>, an element of the mixed powerdomain
  of keys; projected to the LOD, it holds exactly what the presence test reads.  Its possible part
  over-approximates both possible and definite presence in every completion, its definite part
  under-approximates definite presence.\<close>

subsection \<open>The halves of a mix\<close>

text \<open>A mix has a definite half in the lower powerdomain, lifted for the empty part, and a
  possible half in the upper powerdomain, with a top for the empty part.  An element is
  \<^emph>\<open>definite\<close> in a mix when it is below a definite element, and \<^emph>\<open>possible\<close> when some possible
  element is below it.\<close>

lemma pd_basis_Abs_inverse: "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> Rep_pd_basis (Abs_pd_basis S) = S"
  by (rule Abs_pd_basis_inverse) (simp add: pd_basis_def)

definition mdef_lower :: "'a::bifinite mix_basis \<Rightarrow> 'a lower_pd u" where
  "mdef_lower t = (if Rep_pde_basis (mdef t) = {} then \<bottom> else up\<cdot>(lower_principal (Abs_pd_basis (Rep_pde_basis (mdef t)))))"

lemma mdef_lower_mono: "mix_le s t \<Longrightarrow> mdef_lower s \<sqsubseteq> mdef_lower t"
proof -
  assume st: "mix_le s t"
  show ?thesis
  proof (cases "Rep_pde_basis (mdef s) = {}")
    case False
    then have t: "Rep_pde_basis (mdef t) \<noteq> {}" using st by (auto simp: mix_le_def lower_le0_def)
    have "Abs_pd_basis (Rep_pde_basis (mdef s)) \<le>\<flat> Abs_pd_basis (Rep_pde_basis (mdef t))"
      using st False t by (simp add: lower_le_def mix_le_def lower_le0_def pd_basis_Abs_inverse)
    then show ?thesis using False t unfolding mdef_lower_def by (simp add: lower_pd.principal_mono)
  qed (simp add: mdef_lower_def)
qed

definition mix_rows :: "'a::bifinite mix_pd \<rightarrow> 'a lower_pd u" where
  "mix_rows = mix_pd.extension mdef_lower"

lemma mix_rows_principal [simp]: "mix_rows\<cdot>(mix_principal t) = mdef_lower t"
  unfolding mix_rows_def by (simp add: mix_pd.extension_principal mdef_lower_mono)

definition mposs_upper :: "'a::bifinite mix_basis \<Rightarrow> 'a upper_pd top" where
  "mposs_upper t = (if Rep_pde_basis (mposs t) = {} then Top else down\<cdot>(upper_principal (Abs_pd_basis (Rep_pde_basis (mposs t)))))"

lemma mposs_upper_mono: "mix_le s t \<Longrightarrow> mposs_upper s \<sqsubseteq> mposs_upper t"
proof -
  assume st: "mix_le s t"
  show ?thesis
  proof (cases "Rep_pde_basis (mposs t) = {}")
    case False
    then have s: "Rep_pde_basis (mposs s) \<noteq> {}" using st by (auto simp: mix_le_def upper_le0_def)
    have "Abs_pd_basis (Rep_pde_basis (mposs s)) \<le>\<sharp> Abs_pd_basis (Rep_pde_basis (mposs t))"
      using st False s by (simp add: upper_le_def mix_le_def upper_le0_def pd_basis_Abs_inverse)
    then show ?thesis using False s unfolding mposs_upper_def by (simp add: upper_pd.principal_mono)
  qed (simp add: mposs_upper_def)
qed

definition mix_keys :: "'a::bifinite mix_pd \<rightarrow> 'a upper_pd top" where
  "mix_keys = mix_pd.extension mposs_upper"

lemma mix_keys_principal [simp]: "mix_keys\<cdot>(mix_principal t) = mposs_upper t"
  unfolding mix_keys_def by (simp add: mix_pd.extension_principal mposs_upper_mono)

definition mix_definite :: "'a::bifinite \<Rightarrow> 'a mix_pd \<Rightarrow> bool" where
  "mix_definite x M \<longleftrightarrow> up\<cdot>{x}\<flat> \<sqsubseteq> mix_rows\<cdot>M"

definition mix_possible :: "'a::bifinite \<Rightarrow> 'a mix_pd \<Rightarrow> bool" where
  "mix_possible x M \<longleftrightarrow> mix_keys\<cdot>M \<sqsubseteq> down\<cdot>{x}\<sharp>"

lemma lower_unit_below_principal:
  "{x}\<flat> \<sqsubseteq> lower_principal P \<longleftrightarrow> (\<exists>u\<in>Rep_pd_basis P. x \<sqsubseteq> Rep_compact_basis u)"
proof (induct P rule: pd_basis_induct)
  case (PDUnit a)
  show ?case by (simp add: lower_unit_Rep_compact_basis [symmetric] Rep_PDUnit del: lower_unit_Rep_compact_basis)
next
  case (PDPlus t u)
  show ?case
    by (simp add: lower_plus_principal [symmetric] Rep_PDPlus PDPlus.hyps del: lower_plus_principal) blast
qed

lemma upper_principal_below_unit:
  "upper_principal P \<sqsubseteq> {x}\<sharp> \<longleftrightarrow> (\<exists>u\<in>Rep_pd_basis P. Rep_compact_basis u \<sqsubseteq> x)"
proof (induct P rule: pd_basis_induct)
  case (PDUnit a)
  show ?case by (simp add: upper_unit_Rep_compact_basis [symmetric] Rep_PDUnit del: upper_unit_Rep_compact_basis)
next
  case (PDPlus t u)
  show ?case
    by (simp add: upper_plus_principal [symmetric] Rep_PDPlus PDPlus.hyps del: upper_plus_principal) blast
qed

lemma mix_definite_principal:
  "mix_definite x (mix_principal t) \<longleftrightarrow> (\<exists>u\<in>Rep_pde_basis (mdef t). x \<sqsubseteq> Rep_compact_basis u)"
  unfolding mix_definite_def mix_rows_principal mdef_lower_def
  by (simp add: lower_unit_below_principal pd_basis_Abs_inverse)

lemma mix_possible_principal:
  "mix_possible x (mix_principal t) \<longleftrightarrow> (\<exists>u\<in>Rep_pde_basis (mposs t). Rep_compact_basis u \<sqsubseteq> x)"
  unfolding mix_possible_def mix_keys_principal mposs_upper_def
  by (simp add: upper_principal_below_unit pd_basis_Abs_inverse down_beta below_Of)

lemma mix_definite_bot [simp]: "\<not> mix_definite x \<bottom>"
  unfolding inst_mix_pd_pcpo mix_definite_principal by simp

lemma mix_possible_bot [simp]: "mix_possible x \<bottom>"
  unfolding inst_mix_pd_pcpo mix_possible_principal by simp

lemma mix_definite_mono: "mix_definite x M \<Longrightarrow> M \<sqsubseteq> M' \<Longrightarrow> mix_definite x M'"
  unfolding mix_definite_def by (erule below_trans) (rule monofun_cfun_arg)

lemma mix_definite_below: "mix_definite x M \<Longrightarrow> x' \<sqsubseteq> x \<Longrightarrow> mix_definite x' M"
  unfolding mix_definite_def by (erule below_trans [rotated]) (intro monofun_cfun_arg)

lemma mix_possible_below: "mix_possible x M' \<Longrightarrow> M \<sqsubseteq> M' \<Longrightarrow> mix_possible x M"
  unfolding mix_possible_def by (erule below_trans [rotated]) (rule monofun_cfun_arg)

lemma mix_definite_lub: "chain Y \<Longrightarrow> compact x \<Longrightarrow> mix_definite x (\<Squnion>i. Y i) \<longleftrightarrow> (\<exists>i. mix_definite x (Y i))"
  unfolding mix_definite_def contlub_cfun_arg
  by (rule compact_below_lub_iff [OF compact_up [OF compact_lower_unit] ch2ch_Rep_cfunR])

lemma mix_possible_lub: "chain Y \<Longrightarrow> mix_possible x (\<Squnion>i. Y i) \<longleftrightarrow> (\<forall>i. mix_possible x (Y i))"
  unfolding mix_possible_def contlub_cfun_arg
  by (simp add: lub_below_iff ch2ch_Rep_cfunR)

lemma cb_below_iff: "(a :: 'a::pcpo compact_basis) \<sqsubseteq> b \<longleftrightarrow> Rep_compact_basis a \<sqsubseteq> Rep_compact_basis b"
  unfolding compact_le_def ..

text \<open>A property eventually true of each of finitely many things is eventually true of all; a
  compact element below another is eventually below its approximations.\<close>

lemma finite_eventually:
  fixes P :: "'a \<Rightarrow> nat \<Rightarrow> bool"
  assumes "finite S" and "\<And>x. x \<in> S \<Longrightarrow> \<exists>n. \<forall>m\<ge>n. P x m"
  shows "\<exists>N. \<forall>x\<in>S. \<forall>m\<ge>N. P x m"
  using assms
proof (induct S rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x S)
  obtain n where n: "\<forall>m\<ge>n. P x m" using insert.prems by blast
  obtain N where N: "\<forall>y\<in>S. \<forall>m\<ge>N. P y m" using insert.hyps(3) insert.prems by blast
  show ?case
  proof (rule exI [of _ "max n N"], intro ballI allI impI)
    fix y m assume y: "y \<in> insert x S" and m: "max n N \<le> m"
    then have nm: "n \<le> m" and Nm: "N \<le> m" by simp_all
    show "P y m"
    proof (cases "y = x")
      case True
      then show ?thesis using n nm by simp
    next
      case False
      then show ?thesis using N Nm y by simp
    qed
  qed
qed

lemma approx_chain_mono: "approx_chain a \<Longrightarrow> n \<le> m \<Longrightarrow> a n\<cdot>z \<sqsubseteq> a m\<cdot>z"
  by (rule monofun_cfun_fun [OF chain_mono [OF approx_chain.chain_approx]])

lemma approx_chain_lub:
  assumes A: "approx_chain a"
  shows "(\<Squnion>n. a n\<cdot>z) = z"
  using contlub_cfun_fun [OF approx_chain.chain_approx [OF A], of z] approx_chain.lub_approx [OF A] by simp

lemma approx_chain_eventually_above:
  assumes A: "approx_chain a" and c: "compact b" and bz: "b \<sqsubseteq> z"
  shows "\<exists>n. \<forall>m\<ge>n. b \<sqsubseteq> a m\<cdot>z"
proof -
  have ch: "chain (\<lambda>n. a n\<cdot>z)" by (rule ch2ch_Rep_cfunL [OF approx_chain.chain_approx [OF A]])
  obtain n where "b \<sqsubseteq> a n\<cdot>z" using bz compact_below_lub_iff [OF c ch] by (auto simp: approx_chain_lub [OF A])
  then show ?thesis by (blast intro: below_trans approx_chain_mono [OF A])
qed

lemma approx_chain_eventually_eq:
  assumes A: "approx_chain a" and c: "compact z"
  shows "\<exists>n. \<forall>m\<ge>n. a m\<cdot>z = z"
proof -
  obtain n where "z \<sqsubseteq> a m\<cdot>z" if "m \<ge> n" for m using approx_chain_eventually_above [OF A c below_refl] by blast
  then show ?thesis by (blast intro: below_antisym approx_chain.approx_below [OF A])
qed

lemmas split_approx_mono = approx_chain_mono [OF approx_chain_split_approx]
  and split_approx_lub = approx_chain_lub [OF approx_chain_split_approx]
  and approx_eventually_above = approx_chain_eventually_above [OF approx_chain_split_approx]
  and approx_eventually_eq = approx_chain_eventually_eq [OF approx_chain_split_approx]


context split_dataspace
begin

lemma split_rowguard_TT [simp]: "split_rowguard (\<Lambda> _. TT)\<cdot>C = C"
  by (induct C rule: split_pd.principal_induct) (simp, simp, rule split_principal_eqI, simp_all)

lemma split_keyguard_TT [simp]: "split_keyguard (\<Lambda> _. TT)\<cdot>C = C"
  by (induct C rule: split_pd.principal_induct) (simp, simp, rule split_principal_eqI, simp_all)

lemma split_keys_principal_Top: "split_keys\<cdot>(split_principal t) = Top \<longleftrightarrow> skeys t = {}"
  by (simp add: skeys_upper_def down_beta)

lemma upper_map_principal_below_unit:
  "upper_map\<cdot>h\<cdot>(upper_principal P) \<sqsubseteq> {x}\<sharp> \<longleftrightarrow> (\<exists>u\<in>Rep_pd_basis P. h\<cdot>(Rep_compact_basis u) \<sqsubseteq> x)"
proof (induct P rule: pd_basis_induct)
  case (PDUnit a)
  show ?case by (simp add: upper_unit_Rep_compact_basis [symmetric] Rep_PDUnit del: upper_unit_Rep_compact_basis)
next
  case (PDPlus t u)
  show ?case
    by (simp add: upper_plus_principal [symmetric] Rep_PDPlus PDPlus.hyps del: upper_plus_principal) blast
qed

lemma possible_at_principal:
  "split_possible_at K \<kappa> (split_principal t) \<longleftrightarrow> (\<exists>u\<in>skeys t. proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>)"
proof (cases "skeys t = {}")
  case True
  then show ?thesis by (simp add: split_possible_at_def skeys_upper_def down_beta)
next
  case False
  have Kt: "Rep_pd_basis (Abs_pd_basis (skeys t)) = skeys t" by (rule Abs_pd_basis_inverse) (simp add: pd_basis_def False)
  have e: "split_keys\<cdot>(split_principal t) = down\<cdot>(upper_principal (Abs_pd_basis (skeys t)))" by (simp add: skeys_upper_def False)
  show ?thesis unfolding split_possible_at_def e cmap_top_down unfolding down_beta below_Of upper_map_principal_below_unit Kt ..
qed


subsection \<open>The key mix of a split dataset\<close>

text \<open>The key mix of a basis element at a key LOD has as definite part the parts of the rows'
  keys, as possible part the parts of the possible keys.  The parts of the rows' keys need not be
  compact; the key mix is the limit of the basis elements with compact approximations of them,
  those consistent with the possible keys.\<close>

definition kmkey :: "'k semi_factor \<Rightarrow> 'k compact_basis \<Rightarrow> 'k compact_basis" where
  "kmkey K u = Abs_compact_basis (proj K\<cdot>(Rep_compact_basis u))"

text \<open>The stages are formed along an approximation chain of the keys; the limit does not
  depend on the chain.\<close>

definition kmapp_with :: "(nat \<Rightarrow> 'k \<rightarrow> 'k) \<Rightarrow> 'k semi_factor \<Rightarrow> nat \<Rightarrow> 'r compact_basis \<Rightarrow> 'k compact_basis" where
  "kmapp_with a K n x = Abs_compact_basis (a n\<cdot>(rproj K (Rep_compact_basis x)))"

lemma Rep_kmkey [simp]: "Rep_compact_basis (kmkey K u) = proj K\<cdot>(Rep_compact_basis u)"
  unfolding kmkey_def by (simp add: compact_proj_compact)

lemma Rep_kmapp_with: "approx_chain a \<Longrightarrow> Rep_compact_basis (kmapp_with a K n x) = a n\<cdot>(rproj K (Rep_compact_basis x))"
  unfolding kmapp_with_def by (simp add: approx_chain.compact_approx)

definition kconf_with :: "(nat \<Rightarrow> 'k \<rightarrow> 'k) \<Rightarrow> 'k semi_factor \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> nat \<Rightarrow> bool" where
  "kconf_with a K t n \<longleftrightarrow> (\<forall>x\<in>srows t. \<exists>u\<in>skeys t. proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> a n\<cdot>(rproj K (Rep_compact_basis x)))"

lemma kconf_with_mono: "approx_chain a \<Longrightarrow> kconf_with a K t n \<Longrightarrow> n \<le> m \<Longrightarrow> kconf_with a K t m"
  unfolding kconf_with_def by (meson below_trans approx_chain_mono)

lemma kconf_with_eventually:
  assumes A: "approx_chain a"
  shows "\<exists>N. \<forall>m\<ge>N. kconf_with a K t m"
proof -
  have "\<exists>N. \<forall>x\<in>srows t. \<forall>m\<ge>N. \<exists>u\<in>skeys t. proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> a m\<cdot>(rproj K (Rep_compact_basis x))"
  proof (rule finite_eventually [OF finite_srows])
    fix x assume x: "x \<in> srows t"
    obtain u where u: "u \<in> skeys t" and ux: "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
      using split_basis_consistentD [OF x] by blast
    have "proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> rproj K (Rep_compact_basis x)" by (rule monofun_cfun_arg [OF ux])
    then obtain n where "\<forall>m\<ge>n. proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> a m\<cdot>(rproj K (Rep_compact_basis x))"
      using approx_chain_eventually_above [OF A compact_proj_compact [OF Rep_compact_basis']] by blast
    then show "\<exists>n. \<forall>m\<ge>n. \<exists>u\<in>skeys t. proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> a m\<cdot>(rproj K (Rep_compact_basis x))"
      using u by blast
  qed
  then show ?thesis unfolding kconf_with_def by blast
qed

lemma skm_with_consistent:
  assumes A: "approx_chain a" and kc: "kconf_with a K t n"
  shows "upper_le0 (Abs_pde_basis (kmkey K ` skeys t)) (Abs_pde_basis (kmapp_with a K n ` srows t))"
  unfolding upper_le0_def Abs_pde_basis_inverse' [OF finite_imageI [OF finite_srows]] Abs_pde_basis_inverse' [OF finite_imageI [OF finite_skeys]]
proof (intro ballI)
  fix z assume "z \<in> kmapp_with a K n ` srows t"
  then obtain x where x: "x \<in> srows t" and z: "z = kmapp_with a K n x" by blast
  obtain u where u: "u \<in> skeys t" and ux: "proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> a n\<cdot>(rproj K (Rep_compact_basis x))"
    using kc x unfolding kconf_with_def by blast
  have "kmkey K u \<sqsubseteq> z" unfolding z cb_below_iff Rep_kmkey Rep_kmapp_with [OF A] by (rule ux)
  then show "\<exists>w\<in>kmkey K ` skeys t. w \<sqsubseteq> z" using u by blast
qed

definition SKM_with :: "(nat \<Rightarrow> 'k \<rightarrow> 'k) \<Rightarrow> 'k semi_factor \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> nat \<Rightarrow> 'k mix_basis" where
  "SKM_with a K t n = MixB (Abs_pde_basis (kmapp_with a K n ` srows t)) (Abs_pde_basis (kmkey K ` skeys t))"

lemma mdef_SKM_with: "approx_chain a \<Longrightarrow> kconf_with a K t n \<Longrightarrow> Rep_pde_basis (mdef (SKM_with a K t n)) = kmapp_with a K n ` srows t"
  and mposs_SKM_with: "approx_chain a \<Longrightarrow> kconf_with a K t n \<Longrightarrow> Rep_pde_basis (mposs (SKM_with a K t n)) = kmkey K ` skeys t"
  unfolding SKM_with_def by (simp_all add: skm_with_consistent)

definition kstage_with :: "(nat \<Rightarrow> 'k \<rightarrow> 'k) \<Rightarrow> 'k semi_factor \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> nat \<Rightarrow> 'k mix_pd" where
  "kstage_with a K t n = (if kconf_with a K t n then mix_principal (SKM_with a K t n) else \<bottom>)"

text \<open>A stage below a later stage of another chain, for a dataset above.\<close>

lemma kstage_with_le:
  assumes A: "approx_chain a" and B: "approx_chain b" and st: "split_le s t" and c: "kconf_with b K t m"
    and ab: "\<And>x y. x \<in> srows s \<Longrightarrow> y \<in> srows t \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> a n\<cdot>(rproj K (Rep_compact_basis x)) \<sqsubseteq> b m\<cdot>(rproj K (Rep_compact_basis y))"
  shows "kstage_with a K s n \<sqsubseteq> kstage_with b K t m"
proof (cases "kconf_with a K s n")
  case True
  have "mix_le (SKM_with a K s n) (SKM_with b K t m)"
    unfolding mix_le_def lower_le0_def upper_le0_def mdef_SKM_with [OF A True] mposs_SKM_with [OF A True]
      mdef_SKM_with [OF B c] mposs_SKM_with [OF B c]
  proof (intro conjI ballI)
    fix z assume "z \<in> kmapp_with a K n ` srows s"
    then obtain x where x: "x \<in> srows s" and z: "z = kmapp_with a K n x" by blast
    obtain y where y: "y \<in> srows t" and xy: "x \<sqsubseteq> y" using st x unfolding split_le_def hoare_le_def by blast
    have "kmapp_with a K n x \<sqsubseteq> kmapp_with b K m y"
      unfolding cb_below_iff Rep_kmapp_with [OF A] Rep_kmapp_with [OF B] by (rule ab [OF x y xy])
    then show "\<exists>w\<in>kmapp_with b K m ` srows t. z \<sqsubseteq> w" using y unfolding z by blast
  next
    fix w assume "w \<in> kmkey K ` skeys t"
    then obtain v where v: "v \<in> skeys t" and w: "w = kmkey K v" by blast
    obtain u where u: "u \<in> skeys s" and uv: "u \<sqsubseteq> v" using st v unfolding split_le_def smyth_le_def by blast
    have "kmkey K u \<sqsubseteq> kmkey K v" unfolding cb_below_iff Rep_kmkey by (intro monofun_cfun_arg uv [unfolded cb_below_iff])
    then show "\<exists>z\<in>kmkey K ` skeys s. z \<sqsubseteq> w" using u unfolding w by blast
  qed
  then show ?thesis using True c unfolding kstage_with_def by (simp add: mix_pd.principal_mono)
qed (simp add: kstage_with_def)

lemma kstage_with_mono:
  assumes A: "approx_chain a" and st: "split_le s t" and nm: "n \<le> m" and c: "kconf_with a K t m"
  shows "kstage_with a K s n \<sqsubseteq> kstage_with a K t m"
  by (rule kstage_with_le [OF A A st c], rule below_trans [OF approx_chain_mono [OF A nm]])
    (intro monofun_cfun_arg, simp only: cb_below_iff)

lemma chain_kstage_with:
  assumes A: "approx_chain a"
  shows "chain (kstage_with a K t)"
proof (rule chainI)
  fix n
  show "kstage_with a K t n \<sqsubseteq> kstage_with a K t (Suc n)"
  proof (cases "kconf_with a K t (Suc n)")
    case True
    then show ?thesis by (rule kstage_with_mono [OF A split_le_refl le_SucI [OF order_refl]])
  next
    case False
    then have "\<not> kconf_with a K t n" using kconf_with_mono [OF A, of K t n "Suc n"] by auto
    then show ?thesis by (simp add: kstage_with_def)
  qed
qed

definition KM_with :: "(nat \<Rightarrow> 'k \<rightarrow> 'k) \<Rightarrow> 'k semi_factor \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> 'k mix_pd" where
  "KM_with a K t = (\<Squnion>n. kstage_with a K t n)"

lemma KM_with_le:
  assumes A: "approx_chain a" and B: "approx_chain b"
  shows "KM_with a K t \<sqsubseteq> KM_with b K t"
  unfolding KM_with_def
proof (rule lub_below [OF chain_kstage_with [OF A]])
  fix n
  have "\<exists>N. \<forall>x\<in>srows t. \<forall>m\<ge>N. a n\<cdot>(rproj K (Rep_compact_basis x)) \<sqsubseteq> b m\<cdot>(rproj K (Rep_compact_basis x))"
  proof (rule finite_eventually [OF finite_srows])
    fix x
    show "\<exists>N. \<forall>m\<ge>N. a n\<cdot>(rproj K (Rep_compact_basis x)) \<sqsubseteq> b m\<cdot>(rproj K (Rep_compact_basis x))"
      by (rule approx_chain_eventually_above [OF B approx_chain.compact_approx [OF A] approx_chain.approx_below [OF A]])
  qed
  then obtain N1 where N1: "\<forall>x\<in>srows t. \<forall>m\<ge>N1. a n\<cdot>(rproj K (Rep_compact_basis x)) \<sqsubseteq> b m\<cdot>(rproj K (Rep_compact_basis x))" ..
  obtain N2 where N2: "\<forall>m\<ge>N2. kconf_with b K t m" using kconf_with_eventually [OF B] by blast
  let ?m = "max N1 N2"
  have "kstage_with a K t n \<sqsubseteq> kstage_with b K t ?m"
  proof (rule kstage_with_le [OF A B split_le_refl])
    show "kconf_with b K t ?m" using N2 by simp
    fix x y assume x: "x \<in> srows t" and "y \<in> srows t" and xy: "x \<sqsubseteq> y"
    have "a n\<cdot>(rproj K (Rep_compact_basis x)) \<sqsubseteq> b ?m\<cdot>(rproj K (Rep_compact_basis x))" using N1 x by simp
    also have "\<dots> \<sqsubseteq> b ?m\<cdot>(rproj K (Rep_compact_basis y))" by (intro monofun_cfun_arg) (simp only: xy [unfolded cb_below_iff])
    finally show "a n\<cdot>(rproj K (Rep_compact_basis x)) \<sqsubseteq> b ?m\<cdot>(rproj K (Rep_compact_basis y))" .
  qed
  then show "kstage_with a K t n \<sqsubseteq> (\<Squnion>m. kstage_with b K t m)"
    by (rule below_trans [OF _ is_ub_thelub [OF chain_kstage_with [OF B]]])
qed

theorem KM_with_indep: "approx_chain a \<Longrightarrow> approx_chain b \<Longrightarrow> KM_with a K t = KM_with b K t"
  by (rule below_antisym) (simp_all add: KM_with_le)

text \<open>The key mix of a basis element is its limit along the chosen approximation chain.\<close>

abbreviation kmapp :: "'k semi_factor \<Rightarrow> nat \<Rightarrow> 'r compact_basis \<Rightarrow> 'k compact_basis" where
  "kmapp \<equiv> kmapp_with split_approx"

abbreviation kconf :: "'k semi_factor \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> nat \<Rightarrow> bool" where
  "kconf \<equiv> kconf_with split_approx"

abbreviation SKM :: "'k semi_factor \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> nat \<Rightarrow> 'k mix_basis" where
  "SKM \<equiv> SKM_with split_approx"

abbreviation kstage :: "'k semi_factor \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> nat \<Rightarrow> 'k mix_pd" where
  "kstage \<equiv> kstage_with split_approx"

abbreviation KM :: "'k semi_factor \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> 'k mix_pd" where
  "KM \<equiv> KM_with split_approx"

lemmas Rep_kmapp [simp] = Rep_kmapp_with [OF approx_chain_split_approx]
  and kconf_mono = kconf_with_mono [OF approx_chain_split_approx]
  and kconf_eventually = kconf_with_eventually [OF approx_chain_split_approx]
  and mdef_SKM = mdef_SKM_with [OF approx_chain_split_approx]
  and mposs_SKM = mposs_SKM_with [OF approx_chain_split_approx]
  and kstage_mono = kstage_with_mono [OF approx_chain_split_approx]
  and chain_kstage = chain_kstage_with [OF approx_chain_split_approx]

lemma KM_mono: "split_le s t \<Longrightarrow> KM K s \<sqsubseteq> KM K t"
  unfolding KM_with_def
proof (rule lub_below [OF chain_kstage])
  fix n assume st: "split_le s t"
  obtain N where N: "\<forall>m\<ge>N. kconf K t m" using kconf_eventually by blast
  have "kstage K s n \<sqsubseteq> kstage K t (max n N)" by (rule kstage_mono [OF st]) (simp_all add: N)
  then show "kstage K s n \<sqsubseteq> (\<Squnion>m. kstage K t m)" by (rule below_trans [OF _ is_ub_thelub [OF chain_kstage]])
qed

definition split_keymix :: "'k semi_factor \<Rightarrow> ('r, 'k) split_pd \<rightarrow> 'k mix_pd" where
  "split_keymix K = split_pd.extension (KM K)"

lemma split_keymix_principal [simp]: "split_keymix K\<cdot>(split_principal t) = KM K t"
  unfolding split_keymix_def by (simp add: split_pd.extension_principal KM_mono)

lemma split_keymix_chain:
  assumes Z: "\<forall>i. split_le (Z i) (Z (Suc i))"
  shows "chain (\<lambda>i. KM K (Z i))" and "split_keymix K\<cdot>(\<Squnion>i. split_principal (Z i)) = (\<Squnion>i. KM K (Z i))"
proof -
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  show "chain (\<lambda>i. KM K (Z i))" by (rule chainI) (rule KM_mono [OF Z [rule_format]])
  show "split_keymix K\<cdot>(\<Squnion>i. split_principal (Z i)) = (\<Squnion>i. KM K (Z i))" unfolding contlub_cfun_arg [OF ch] by simp
qed

text \<open>The key mix of a basis element: a key part is possible in it where a possible key's part is
  below it, and a compact one definite where it is below a row's key part.\<close>

lemma KM_possible: "mix_possible \<kappa> (KM K t) \<longleftrightarrow> (\<exists>u\<in>skeys t. proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>)"
proof -
  obtain N where N: "\<forall>m\<ge>N. kconf K t m" using kconf_eventually by blast
  have st: "mix_possible \<kappa> (kstage K t n) \<longleftrightarrow> (kconf K t n \<longrightarrow> (\<exists>u\<in>skeys t. proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>))" for n
    by (cases "kconf K t n") (simp_all add: kstage_with_def mix_possible_principal mposs_SKM)
  show ?thesis unfolding KM_with_def mix_possible_lub [OF chain_kstage] st using N by blast
qed

lemma KM_definite:
  assumes c: "compact q"
  shows "mix_definite q (KM K t) \<longleftrightarrow> (\<exists>x\<in>srows t. q \<sqsubseteq> rproj K (Rep_compact_basis x))"
proof
  assume "mix_definite q (KM K t)"
  then obtain n where d: "mix_definite q (kstage K t n)" unfolding KM_with_def mix_definite_lub [OF chain_kstage c] by blast
  then have kc: "kconf K t n" by (cases "kconf K t n") (simp_all add: kstage_with_def)
  then obtain x where x: "x \<in> srows t" and qx: "q \<sqsubseteq> split_approx n\<cdot>(rproj K (Rep_compact_basis x))"
    using d unfolding kstage_with_def by (auto simp: mix_definite_principal mdef_SKM)
  then show "\<exists>x\<in>srows t. q \<sqsubseteq> rproj K (Rep_compact_basis x)" by (blast intro: below_trans split_approx.approx_below)
next
  assume "\<exists>x\<in>srows t. q \<sqsubseteq> rproj K (Rep_compact_basis x)"
  then obtain x where x: "x \<in> srows t" and qx: "q \<sqsubseteq> rproj K (Rep_compact_basis x)" by blast
  obtain n where n: "\<forall>m\<ge>n. q \<sqsubseteq> split_approx m\<cdot>(rproj K (Rep_compact_basis x))" using approx_eventually_above [OF c qx] by blast
  obtain N where N: "\<forall>m\<ge>N. kconf K t m" using kconf_eventually by blast
  let ?m = "max n N"
  have km: "kconf K t ?m" using N by simp
  have "q \<sqsubseteq> split_approx ?m\<cdot>(rproj K (Rep_compact_basis x))" using n by simp
  then have "mix_definite q (kstage K t ?m)"
    using km x unfolding kstage_with_def by (auto simp: mix_definite_principal mdef_SKM)
  then show "mix_definite q (KM K t)" unfolding KM_with_def by (rule mix_definite_mono [OF _ is_ub_thelub [OF chain_kstage]])
qed

text \<open>Where the parts of the rows' keys are compact, the key mix of a basis element is compact.\<close>

lemma compact_KM:
  assumes c: "\<forall>x\<in>srows t. compact (rproj K (Rep_compact_basis x))"
  shows "compact (KM K t)"
proof -
  have "\<exists>N. \<forall>x\<in>srows t. \<forall>m\<ge>N. split_approx m\<cdot>(rproj K (Rep_compact_basis x)) = rproj K (Rep_compact_basis x)"
  proof (rule finite_eventually [OF finite_srows])
    fix x assume "x \<in> srows t"
    then show "\<exists>n. \<forall>m\<ge>n. split_approx m\<cdot>(rproj K (Rep_compact_basis x)) = rproj K (Rep_compact_basis x)"
      using c by (blast intro: approx_eventually_eq)
  qed
  then obtain N1 where N1: "\<forall>x\<in>srows t. \<forall>m\<ge>N1. split_approx m\<cdot>(rproj K (Rep_compact_basis x)) = rproj K (Rep_compact_basis x)" ..
  obtain N2 where N2: "\<forall>m\<ge>N2. kconf K t m" using kconf_eventually by blast
  let ?N = "max N1 N2"
  have ka: "kmapp K m x = kmapp K ?N x" if m: "m \<ge> ?N" and x: "x \<in> srows t" for m x
  proof -
    have "split_approx m\<cdot>(rproj K (Rep_compact_basis x)) = split_approx ?N\<cdot>(rproj K (Rep_compact_basis x))"
      using N1 m x by simp
    then show ?thesis unfolding kmapp_with_def by (rule arg_cong)
  qed
  have eq: "kstage K t (m + ?N) = kstage K t ?N" for m
  proof -
    have c1: "kconf K t (m + ?N)" and c2: "kconf K t ?N" using N2 by simp_all
    have im: "kmapp K (m + ?N) ` srows t = kmapp K ?N ` srows t" by (rule image_cong [OF refl ka]) simp_all
    show ?thesis unfolding kstage_with_def if_P [OF c1] if_P [OF c2] SKM_with_def im ..
  qed
  have "KM K t = (\<Squnion>m. kstage K t (m + ?N))" unfolding KM_with_def by (rule lub_range_shift [OF chain_kstage, symmetric])
  also have "\<dots> = kstage K t ?N" by (simp only: eq lub_const)
  finally show ?thesis using N2 by (simp add: kstage_with_def mix_pd.compact_principal)
qed

text \<open>A key part is possible in the key mix where it is possible in the dataset; a compact one is
  definite where it is below the part of a definite row.\<close>

lemma keymix_possible: "mix_possible \<kappa> (split_keymix K\<cdot>C) \<longleftrightarrow> split_possible_at K \<kappa> C"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and CZ: "C = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have "split_possible_at K \<kappa> C \<longleftrightarrow> (\<forall>i. split_possible_at K \<kappa> (split_principal (Z i)))"
    unfolding CZ using split_possible_at_lub [OF ch] split_possible_at_below [OF _ is_ub_thelub [OF ch]] by blast
  then show ?thesis
    unfolding CZ split_keymix_chain(2) [OF Z] mix_possible_lub [OF split_keymix_chain(1) [OF Z]] KM_possible possible_at_principal ..
qed

lemma keymix_definite_imp:
  assumes c: "compact q" and d: "mix_definite q (split_keymix K\<cdot>C)"
  shows "\<exists>y. split_definite y C \<and> q \<sqsubseteq> rproj K y"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and CZ: "C = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  obtain i where "mix_definite q (KM K (Z i))"
    using d unfolding CZ split_keymix_chain(2) [OF Z] mix_definite_lub [OF split_keymix_chain(1) [OF Z] c] by blast
  then obtain x where x: "x \<in> srows (Z i)" and qx: "q \<sqsubseteq> rproj K (Rep_compact_basis x)" unfolding KM_definite [OF c] by blast
  have "split_definite (Rep_compact_basis x) C"
    by (rule split_definite_mono [OF generator_definite [OF x]]) (simp only: CZ is_ub_thelub [OF ch])
  then show ?thesis using qx by blast
qed

lemma keymix_definite:
  assumes y: "split_definite y C" and qy: "q \<sqsubseteq> rproj K y" and c: "compact q"
  shows "mix_definite q (split_keymix K\<cdot>C)"
proof -
  obtain r :: "nat \<Rightarrow> 'r \<rightarrow> 'r" where r: "approx_chain r" using bifinite by blast
  interpret R: approx_chain r by (fact r)
  have chy: "chain (\<lambda>n. r n\<cdot>y)" by (rule ch2ch_Rep_cfunL [OF R.chain_approx])
  have ly: "(\<Squnion>n. r n\<cdot>y) = y" using contlub_cfun_fun [OF R.chain_approx, of y] R.lub_approx by simp
  have ch: "chain (\<lambda>n. rproj K (r n\<cdot>y))" by (intro ch2ch_Rep_cfunR chy)
  have "rproj K y = (\<Squnion>n. rproj K (r n\<cdot>y))"
    by (subst (1) ly [symmetric]) (simp only: contlub_cfun_arg [OF chy] contlub_cfun_arg [OF ch2ch_Rep_cfunR [OF chy]])
  then obtain n where n: "q \<sqsubseteq> rproj K (r n\<cdot>y)" using qy compact_below_lub_iff [OF c ch] by auto
  have cy: "compact (r n\<cdot>y)" by (rule finite_deflation.compact [OF R.finite_deflation_approx])
  let ?a = "Abs_compact_basis (r n\<cdot>y)"
  have ya: "Rep_compact_basis ?a = r n\<cdot>y" by (rule Abs_compact_basis_inverse' [OF cy])
  have dy: "split_definite (r n\<cdot>y) C"
    by (rule split_definite_below [OF y deflation.below [OF finite_deflation_imp_deflation [OF R.finite_deflation_approx]]])
  have "split_keymix K\<cdot>(split_open_unit\<cdot>(r n\<cdot>y)) \<sqsubseteq> split_keymix K\<cdot>C"
    using dy unfolding split_definite_def by (rule monofun_cfun_arg)
  moreover have "mix_definite q (split_keymix K\<cdot>(split_open_unit\<cdot>(r n\<cdot>y)))"
  proof -
    have d: "mix_definite q (KM K (SOpen ?a))" unfolding KM_definite [OF c] using n ya by simp
    have e: "split_open_unit\<cdot>(r n\<cdot>y) = split_principal (SOpen ?a)"
      using split_open_unit_Rep_compact_basis [of ?a] unfolding ya .
    show ?thesis unfolding e split_keymix_principal by (rule d)
  qed
  ultimately show ?thesis by (rule mix_definite_mono [rotated])
qed

text \<open>Where the parts of the rows' keys are compact, the key mix of a compact dataset is compact.\<close>

lemma compact_keymix:
  assumes c: "compact C" and k: "\<And>y. split_definite y C \<Longrightarrow> compact y \<Longrightarrow> compact (rproj K y)"
  shows "compact (split_keymix K\<cdot>C)"
proof -
  obtain t where t: "C = split_principal t" using split_pd.compact_imp_principal [OF c] by blast
  have "compact (rproj K (Rep_compact_basis x))" if "x \<in> srows t" for x
    using k generator_definite [OF that] unfolding t by simp
  then show ?thesis unfolding t split_keymix_principal by (blast intro: compact_KM)
qed

subsection \<open>Selection in a mix\<close>

text \<open>Selecting a key mix at a compact part of a coarser LOD keeps the definite keys exactly at the
  part, if it is maximal, and the possible keys that may end up there; it commutes with forming
  the key mix.\<close>

lemma Rep_pde_basis_filter [simp]:
  "Rep_pde_basis (Abs_pde_basis {x \<in> Rep_pde_basis S. P x}) = {x \<in> Rep_pde_basis S. P x}"
  by (rule Abs_pde_basis_inverse', rule finite_subset [OF _ finite_Rep_pde_basis]) auto

definition MSelect :: "'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'k mix_basis \<Rightarrow> 'k mix_basis" where
  "MSelect L q t = MixB (Abs_pde_basis {x \<in> Rep_pde_basis (mdef t). maximal_at L q \<and> proj L\<cdot>(Rep_compact_basis x) = q})
     (Abs_pde_basis {u \<in> Rep_pde_basis (mposs t). proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> q})"

lemma mselect_consistent:
  "upper_le0 (Abs_pde_basis {u \<in> Rep_pde_basis (mposs t). proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> q})
     (Abs_pde_basis {x \<in> Rep_pde_basis (mdef t). maximal_at L q \<and> proj L\<cdot>(Rep_compact_basis x) = q})"
  unfolding upper_le0_def
proof (unfold Rep_pde_basis_filter, intro ballI)
  fix x assume "x \<in> {x \<in> Rep_pde_basis (mdef t). maximal_at L q \<and> proj L\<cdot>(Rep_compact_basis x) = q}"
  then have x: "x \<in> Rep_pde_basis (mdef t)" and xq: "proj L\<cdot>(Rep_compact_basis x) = q" by simp_all
  obtain u where u: "u \<in> Rep_pde_basis (mposs t)" and ux: "u \<sqsubseteq> x" using mix_basis_consistentD [OF x] by blast
  have "proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> q" unfolding xq [symmetric] by (rule monofun_cfun_arg) (use ux in \<open>simp only: cb_below_iff\<close>)
  then show "\<exists>u\<in>{u \<in> Rep_pde_basis (mposs t). proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> q}. u \<sqsubseteq> x" using u ux by blast
qed

lemma mdef_MSelect [simp]:
  "Rep_pde_basis (mdef (MSelect L q t)) = {x \<in> Rep_pde_basis (mdef t). maximal_at L q \<and> proj L\<cdot>(Rep_compact_basis x) = q}"
  and mposs_MSelect [simp]:
  "Rep_pde_basis (mposs (MSelect L q t)) = {u \<in> Rep_pde_basis (mposs t). proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> q}"
  unfolding MSelect_def by (simp_all add: mselect_consistent)

lemma MSelect_mix_mono:
  assumes st: "mix_le s t"
  shows "mix_le (MSelect L q s) (MSelect L q t)"
  unfolding mix_le_def lower_le0_def upper_le0_def mdef_MSelect mposs_MSelect
proof (intro conjI ballI)
  fix x assume "x \<in> {x \<in> Rep_pde_basis (mdef s). maximal_at L q \<and> proj L\<cdot>(Rep_compact_basis x) = q}"
  then have x: "x \<in> Rep_pde_basis (mdef s)" and m: "maximal_at L q" and xq: "proj L\<cdot>(Rep_compact_basis x) = q" by simp_all
  obtain y where y: "y \<in> Rep_pde_basis (mdef t)" and xy: "x \<sqsubseteq> y" using st x unfolding mix_le_def lower_le0_def by blast
  have "q \<sqsubseteq> proj L\<cdot>(Rep_compact_basis y)" unfolding xq [symmetric] by (rule monofun_cfun_arg) (use xy in \<open>simp only: cb_below_iff\<close>)
  then have "proj L\<cdot>(Rep_compact_basis y) = q" by (rule maximal_at_eq [OF m proj_idem])
  then show "\<exists>y\<in>{x \<in> Rep_pde_basis (mdef t). maximal_at L q \<and> proj L\<cdot>(Rep_compact_basis x) = q}. x \<sqsubseteq> y"
    using y xy m by blast
next
  fix v assume "v \<in> {u \<in> Rep_pde_basis (mposs t). proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> q}"
  then have v: "v \<in> Rep_pde_basis (mposs t)" and vq: "proj L\<cdot>(Rep_compact_basis v) \<sqsubseteq> q" by simp_all
  obtain u where u: "u \<in> Rep_pde_basis (mposs s)" and uv: "u \<sqsubseteq> v" using st v unfolding mix_le_def upper_le0_def by blast
  have "proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> proj L\<cdot>(Rep_compact_basis v)" by (rule monofun_cfun_arg) (use uv in \<open>simp only: cb_below_iff\<close>)
  then show "\<exists>u\<in>{u \<in> Rep_pde_basis (mposs s). proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> q}. u \<sqsubseteq> v"
    using u uv vq by (blast intro: below_trans)
qed

definition mix_select :: "'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'k mix_pd \<rightarrow> 'k mix_pd" where
  "mix_select L q = mix_pd.extension (\<lambda>t. mix_principal (MSelect L q t))"

lemma mix_select_principal [simp]: "mix_select L q\<cdot>(mix_principal t) = mix_principal (MSelect L q t)"
  unfolding mix_select_def by (simp add: mix_pd.extension_principal MSelect_mix_mono)

lemma keymix_select:
  assumes LK: "L \<sqsubseteq> K" and cq: "compact q"
  shows "split_keymix K\<cdot>(split_select L q\<cdot>C) = mix_select L q\<cdot>(split_keymix K\<cdot>C)"
proof (induct C rule: split_pd.principal_induct)
  fix t :: "('r, 'k) split_basis"
  have pk: "proj L\<cdot>(proj K\<cdot>u) = proj L\<cdot>u" for u by (rule proj_le [OF LK])
  have up: "proj L\<cdot>(split_approx m\<cdot>(rproj K y)) = q" if m: "maximal_at L q" and e: "q \<sqsubseteq> proj L\<cdot>(split_approx m\<cdot>(rproj K y))" for m y
  proof -
    have a: "proj L\<cdot>(split_approx m\<cdot>(rproj K y)) \<sqsubseteq> rproj L y"
      using monofun_cfun_arg [OF split_approx.approx_below, of "proj L" m "rproj K y"] unfolding pk .
    have le: "q \<sqsubseteq> rproj L y" by (rule below_trans [OF e a])
    have yq: "rproj L y = q" by (rule maximal_at_eq [OF m _ le]) simp
    have "proj L\<cdot>(split_approx m\<cdot>(rproj K y)) \<sqsubseteq> q" using a unfolding yq .
    then show ?thesis by (rule below_antisym [OF _ e])
  qed
  have "\<exists>N. \<forall>x\<in>srows t. \<forall>m\<ge>N. rproj L (Rep_compact_basis x) = q \<longrightarrow> q \<sqsubseteq> proj L\<cdot>(split_approx m\<cdot>(rproj K (Rep_compact_basis x)))"
  proof (rule finite_eventually [OF finite_srows])
    fix x assume "x \<in> srows t"
    show "\<exists>n. \<forall>m\<ge>n. rproj L (Rep_compact_basis x) = q \<longrightarrow> q \<sqsubseteq> proj L\<cdot>(split_approx m\<cdot>(rproj K (Rep_compact_basis x)))"
    proof (cases "rproj L (Rep_compact_basis x) = q")
      case True
      have "q \<sqsubseteq> rproj K (Rep_compact_basis x)"
        using True pk [of "row_key\<cdot>(Rep_compact_basis x)"] by (metis proj_below)
      then obtain n where n: "\<forall>m\<ge>n. q \<sqsubseteq> split_approx m\<cdot>(rproj K (Rep_compact_basis x))"
        using approx_eventually_above [OF cq] by blast
      have qq: "proj L\<cdot>q = q" using True by (metis proj_idem)
      show ?thesis using n by (metis qq monofun_cfun_arg)
    qed simp
  qed
  then obtain N1 where N1: "\<forall>x\<in>srows t. \<forall>m\<ge>N1. rproj L (Rep_compact_basis x) = q \<longrightarrow> q \<sqsubseteq> proj L\<cdot>(split_approx m\<cdot>(rproj K (Rep_compact_basis x)))" by blast
  obtain N2 where N2: "\<forall>m\<ge>N2. kconf K t m" using kconf_eventually by blast
  let ?N = "max N1 N2" and ?s = "SSelect L q t"
  have cs: "kconf K ?s m" if ctm: "kconf K t m" for m
    unfolding kconf_with_def
  proof (intro ballI)
    fix x assume "x \<in> srows ?s"
    then have x: "x \<in> srows t" and xq: "rproj L (Rep_compact_basis x) = q" by simp_all
    obtain u where u: "u \<in> skeys t" and ux: "proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> split_approx m\<cdot>(rproj K (Rep_compact_basis x))"
      using ctm x unfolding kconf_with_def by blast
    have "proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> q"
    proof -
      have "proj L\<cdot>(proj K\<cdot>(Rep_compact_basis u)) \<sqsubseteq> proj L\<cdot>(rproj K (Rep_compact_basis x))"
        by (intro monofun_cfun_arg below_trans [OF ux split_approx.approx_below])
      then show ?thesis unfolding pk xq .
    qed
    then show "\<exists>u\<in>skeys ?s. proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> split_approx m\<cdot>(rproj K (Rep_compact_basis x))" using u ux by auto
  qed
  have st: "mix_select L q\<cdot>(kstage K t m) = kstage K ?s m" if m: "m \<ge> ?N" for m
  proof -
    have ct: "kconf K t m" using N2 m by simp
    have "MSelect L q (SKM K t m) = SKM K ?s m"
    proof (rule mix_basis_eqI)
      show "mdef (MSelect L q (SKM K t m)) = mdef (SKM K ?s m)"
        unfolding Rep_pde_basis_inject [symmetric] mdef_MSelect mdef_SKM [OF ct] mdef_SKM [OF cs [OF ct]]
      proof (rule set_eqI, rule iffI)
        fix z assume "z \<in> {z \<in> kmapp K m ` srows t. maximal_at L q \<and> proj L\<cdot>(Rep_compact_basis z) = q}"
        then obtain x where x: "x \<in> srows t" and z: "z = kmapp K m x" and mx: "maximal_at L q"
          and zq: "proj L\<cdot>(split_approx m\<cdot>(rproj K (Rep_compact_basis x))) = q" by auto
        have "rproj L (Rep_compact_basis x) = q"
        proof (rule maximal_at_eq [OF mx _])
          show "q \<sqsubseteq> rproj L (Rep_compact_basis x)"
            using zq monofun_cfun_arg [OF split_approx.approx_below, of "proj L" m "rproj K (Rep_compact_basis x)"] pk by simp
        qed simp
        then show "z \<in> kmapp K m ` srows ?s" using x z mx by auto
      next
        fix z assume "z \<in> kmapp K m ` srows ?s"
        then obtain x where x: "x \<in> srows t" and z: "z = kmapp K m x" and mx: "maximal_at L q"
          and xq: "rproj L (Rep_compact_basis x) = q" by auto
        have "proj L\<cdot>(split_approx m\<cdot>(rproj K (Rep_compact_basis x))) = q"
          by (rule up [OF mx]) (use N1 x xq m in auto)
        then show "z \<in> {z \<in> kmapp K m ` srows t. maximal_at L q \<and> proj L\<cdot>(Rep_compact_basis z) = q}" using x z mx by auto
      qed
      show "mposs (MSelect L q (SKM K t m)) = mposs (SKM K ?s m)"
        unfolding Rep_pde_basis_inject [symmetric] mposs_MSelect mposs_SKM [OF ct] mposs_SKM [OF cs [OF ct]]
        by (auto simp: pk)
    qed
    then show ?thesis using ct cs [OF ct] unfolding kstage_with_def by simp
  qed
  have "mix_select L q\<cdot>(KM K t) = (\<Squnion>m. mix_select L q\<cdot>(kstage K t m))"
    unfolding KM_with_def by (rule contlub_cfun_arg [OF chain_kstage])
  also have "\<dots> = (\<Squnion>m. mix_select L q\<cdot>(kstage K t (m + ?N)))"
    by (rule lub_range_shift [OF ch2ch_Rep_cfunR [OF chain_kstage], symmetric])
  also have "\<dots> = (\<Squnion>m. kstage K ?s (m + ?N))" by (simp only: st le_add2)
  also have "\<dots> = KM K ?s" unfolding KM_with_def by (rule lub_range_shift [OF chain_kstage])
  finally show "split_keymix K\<cdot>(split_select L q\<cdot>(split_principal t)) = mix_select L q\<cdot>(split_keymix K\<cdot>(split_principal t))"
    by simp
qed simp

subsection \<open>Presence\<close>

text \<open>The presence of a key part in a mix: true where it is definite and maximal, false where it
  is not possible, undecided otherwise.\<close>

definition mix_present :: "'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'k mix_pd \<Rightarrow> tr" where
  "mix_present K \<kappa> M = (if maximal_at K \<kappa> \<and> mix_definite \<kappa> M then TT else if mix_possible \<kappa> M then \<bottom> else FF)"

lemma refuted_TT_impossible:
  assumes r: "split_refuted K \<kappa> (\<Lambda> _. TT) C"
  shows "\<not> split_possible_at K \<kappa> C"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and CZ: "C = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  obtain i where "split_refuted K \<kappa> (\<Lambda> _. TT) (split_principal (Z i))"
    using r unfolding CZ by (rule split_refuted_lub [OF ch])
  then have "skeys (SSelect K \<kappa> (Z i)) = {}"
    unfolding split_refuted_keyguard split_keyguard_TT split_select_principal split_keys_principal_Top .
  then have "\<not> split_possible_at K \<kappa> (split_principal (Z i))" unfolding possible_at_principal by auto
  then show ?thesis unfolding CZ using split_possible_at_below [OF _ is_ub_thelub [OF ch]] by blast
qed

text \<open>The presence test at a compact key part reads only the key mix.\<close>

theorem select_test_keymix:
  assumes c: "compact \<kappa>"
  shows "select_test K \<kappa> (\<Lambda> _. TT) (\<Lambda> _. TT) C = mix_present K \<kappa> (split_keymix K\<cdot>C)"
proof -
  have d1: "mix_definite \<kappa> (split_keymix K\<cdot>C)" if "split_definite y C" "rproj K y = \<kappa>" for y
    using keymix_definite [OF that(1) _ c] that(2) by simp
  have r: "split_refuted K \<kappa> (\<Lambda> _. TT) C \<longleftrightarrow> \<not> mix_possible \<kappa> (split_keymix K\<cdot>C)"
    unfolding keymix_possible using refuted_TT_impossible impossible_refuted by blast
  show ?thesis
  proof (cases "maximal_at K \<kappa> \<and> mix_definite \<kappa> (split_keymix K\<cdot>C)")
    case True
    then have mx: "maximal_at K \<kappa>" and md: "mix_definite \<kappa> (split_keymix K\<cdot>C)" by simp_all
    obtain y where y: "split_definite y C" "\<kappa> \<sqsubseteq> rproj K y" using keymix_definite_imp [OF c md] by blast
    have ky: "rproj K y = \<kappa>" by (rule maximal_at_eq [OF mx _ y(2)]) simp
    have "select_test K \<kappa> (\<Lambda> _. TT) (\<Lambda> _. TT) C = TT" by (rule select_test_TT [OF mx y(1) ky]) simp_all
    then show ?thesis using True unfolding mix_present_def by simp
  next
    case False
    then have "\<not> (maximal_at K \<kappa> \<and> (\<exists>y. split_definite y C \<and> rproj K y = \<kappa>))" using d1 by blast
    then show ?thesis using False r unfolding select_test_def mix_present_def by auto
  qed
qed

corollary present_select_keymix:
  "compact \<kappa> \<Longrightarrow> split_present (split_select K \<kappa>\<cdot>C) = mix_present K \<kappa> (split_keymix K\<cdot>C)"
  using select_test_keymix [of \<kappa> K C] select_test_guarded [of \<kappa> K "\<Lambda> _. TT" "\<Lambda> _. TT" C] by simp


text \<open>Below a key mix, a maximal key part that is definite is possible.\<close>

lemma keymix_definite_possible:
  assumes c: "compact \<kappa>" and mx: "maximal_at K \<kappa>" and d: "mix_definite \<kappa> (split_keymix K\<cdot>C)"
  shows "mix_possible \<kappa> (split_keymix K\<cdot>C)"
proof -
  obtain y where y: "split_definite y C" "\<kappa> \<sqsubseteq> rproj K y" using keymix_definite_imp [OF c d] by blast
  have ky: "rproj K y = \<kappa>" by (rule maximal_at_eq [OF mx _ y(2)]) simp
  have "split_possible_at K (rproj K y) C" by (rule definite_maximal_possible [OF y(1)]) (simp_all add: ky c mx)
  then show ?thesis unfolding keymix_possible ky .
qed

lemma mix_present_mono_below:
  assumes c: "compact \<kappa>" and le: "M \<sqsubseteq> M'" and M': "M' \<sqsubseteq> split_keymix K\<cdot>C"
  shows "mix_present K \<kappa> M \<sqsubseteq> mix_present K \<kappa> M'"
proof (cases "maximal_at K \<kappa> \<and> mix_definite \<kappa> M")
  case True
  then show ?thesis using mix_definite_mono [OF _ le] unfolding mix_present_def by auto
next
  case nT: False
  show ?thesis
  proof (cases "mix_possible \<kappa> M")
    case True
    then have "mix_present K \<kappa> M = \<bottom>" using nT unfolding mix_present_def by simp
    then show ?thesis by simp
  next
    case nP: False
    have nP': "\<not> mix_possible \<kappa> M'" using nP mix_possible_below [OF _ le] by blast
    have "\<not> (maximal_at K \<kappa> \<and> mix_definite \<kappa> M')"
    proof
      assume "maximal_at K \<kappa> \<and> mix_definite \<kappa> M'"
      then have "mix_possible \<kappa> (split_keymix K\<cdot>C)"
        using keymix_definite_possible [OF c] mix_definite_mono [OF _ M'] by blast
      then show False using nP' mix_possible_below [OF _ M'] by blast
    qed
    then show ?thesis using nT nP nP' unfolding mix_present_def by simp
  qed
qed

text \<open>The compact maximal definite parts of a compact mix are finitely many.\<close>

lemma mix_definite_finite:
  assumes cM: "compact M"
  shows "finite {\<kappa>. compact \<kappa> \<and> maximal_at K \<kappa> \<and> mix_definite \<kappa> M}"
proof -
  obtain t where t: "M = mix_principal t" using mix_pd.compact_imp_principal [OF cM] by blast
  have "{\<kappa>. compact \<kappa> \<and> maximal_at K \<kappa> \<and> mix_definite \<kappa> M} \<subseteq> (\<lambda>x. proj K\<cdot>(Rep_compact_basis x)) ` Rep_pde_basis (mdef t)"
  proof
    fix \<kappa> assume "\<kappa> \<in> {\<kappa>. compact \<kappa> \<and> maximal_at K \<kappa> \<and> mix_definite \<kappa> M}"
    then have c: "compact \<kappa>" and mx: "maximal_at K \<kappa>" and d: "mix_definite \<kappa> M" by simp_all
    obtain x where x: "x \<in> Rep_pde_basis (mdef t)" and ax: "\<kappa> \<sqsubseteq> Rep_compact_basis x"
      using d unfolding t mix_definite_principal by blast
    have "\<kappa> \<sqsubseteq> proj K\<cdot>(Rep_compact_basis x)"
      using monofun_cfun_arg [OF ax, of "proj K"] maximal_at_lives [OF mx] by simp
    then have "proj K\<cdot>(Rep_compact_basis x) = \<kappa>" by (rule maximal_at_eq [OF mx proj_idem])
    then show "\<kappa> \<in> (\<lambda>x. proj K\<cdot>(Rep_compact_basis x)) ` Rep_pde_basis (mdef t)" using x by force
  qed
  then show ?thesis by (rule finite_subset) simp
qed

end

end
