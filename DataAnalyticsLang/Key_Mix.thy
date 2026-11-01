theory Key_Mix
  imports Split_Semantics "HOLCF-extra.MixPD"
begin

default_sort type

section \<open>Key mixes\<close>

text \<open>A guard entry reads a split dataset only for the presence of keys at a key LOD: present
  where a definite row has the key, refuted where no possible key may end up there.  Projecting the
  keys of the definite rows and the possible keys to the LOD gives a \<^emph>\<open>key mix\<close>, an element of the
  mixed powerdomain of keys.  It holds exactly what the presence test reads.  Its possible part
  over-approximates both possible and definite presence in every completion, its definite part
  under-approximates definite presence.\<close>

subsection \<open>Presence in a mix\<close>

text \<open>An element is \<^emph>\<open>definite\<close> in a mix when it is below a definite element, and \<^emph>\<open>possible\<close> when
  some possible element is below it.\<close>

definition MOpen :: "'a::bifinite compact_basis \<Rightarrow> 'a mix_basis" where
  "MOpen a = MixB (PDEUnit a) (PDEUnit compact_bot)"

lemma mdef_MOpen [simp]: "mdef (MOpen a) = PDEUnit a"
  and mposs_MOpen [simp]: "mposs (MOpen a) = PDEUnit compact_bot"
  unfolding MOpen_def by (simp_all add: upper_le0_def)

lemma MOpen_mix_mono: "a \<sqsubseteq> b \<Longrightarrow> mix_le (MOpen a) (MOpen b)"
  unfolding mix_le_def lower_le0_def upper_le0_def by simp

definition mix_open_unit :: "'a::bifinite \<rightarrow> 'a mix_pd" where
  "mix_open_unit = compact_basis.extension (\<lambda>a. mix_principal (MOpen a))"

lemma mix_open_unit_Rep_compact_basis [simp]: "mix_open_unit\<cdot>(Rep_compact_basis a) = mix_principal (MOpen a)"
  unfolding mix_open_unit_def by (simp add: compact_basis.extension_principal MOpen_mix_mono)

definition mix_definite :: "'a::bifinite \<Rightarrow> 'a mix_pd \<Rightarrow> bool" where
  "mix_definite x M \<longleftrightarrow> mix_open_unit\<cdot>x \<sqsubseteq> M"

definition mix_possible :: "'a::bifinite \<Rightarrow> 'a mix_pd \<Rightarrow> bool" where
  "mix_possible x M \<longleftrightarrow> mix_maybe\<cdot>M \<sqsubseteq> mix_maybe\<cdot>(mix_unit\<cdot>x)"

lemma mix_definite_principal:
  "mix_definite (Rep_compact_basis a) (mix_principal t) \<longleftrightarrow> (\<exists>x\<in>Rep_pde_basis (mdef t). a \<sqsubseteq> x)"
  unfolding mix_definite_def mix_open_unit_Rep_compact_basis mix_pd.principal_below_iff mix_le_def lower_le0_def upper_le0_def
  by simp

lemma mix_possible_principal:
  "mix_possible (Rep_compact_basis a) (mix_principal t) \<longleftrightarrow> (\<exists>u\<in>Rep_pde_basis (mposs t). u \<sqsubseteq> a)"
  unfolding mix_possible_def mix_unit_Rep_compact_basis mix_maybe_principal mix_pd.principal_below_iff mix_le_def lower_le0_def upper_le0_def
  by simp

lemma mix_definite_mono: "mix_definite x M \<Longrightarrow> M \<sqsubseteq> M' \<Longrightarrow> mix_definite x M'"
  unfolding mix_definite_def by (rule below_trans)

lemma mix_definite_below: "mix_definite x M \<Longrightarrow> x' \<sqsubseteq> x \<Longrightarrow> mix_definite x' M"
  unfolding mix_definite_def by (erule below_trans [rotated]) (rule monofun_cfun_arg)

lemma mix_possible_below: "mix_possible x M' \<Longrightarrow> M \<sqsubseteq> M' \<Longrightarrow> mix_possible x M"
  unfolding mix_possible_def by (erule below_trans [rotated]) (rule monofun_cfun_arg)

lemma compact_mix_open_unit: "compact x \<Longrightarrow> compact (mix_open_unit\<cdot>x)"
  by (drule Abs_compact_basis_inverse') (metis mix_open_unit_Rep_compact_basis mix_pd.compact_principal)

lemma mix_definite_lub: "chain Y \<Longrightarrow> compact x \<Longrightarrow> mix_definite x (\<Squnion>i. Y i) \<longleftrightarrow> (\<exists>i. mix_definite x (Y i))"
  unfolding mix_definite_def by (rule compact_below_lub_iff [OF compact_mix_open_unit])

lemma mix_possible_lub: "chain Y \<Longrightarrow> mix_possible x (\<Squnion>i. Y i) \<longleftrightarrow> (\<forall>i. mix_possible x (Y i))"
  unfolding mix_possible_def contlub_cfun_arg
  by (simp add: lub_below_iff ch2ch_Rep_cfunR)


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

text \<open>At a key LOD, a row gives the part of its key, and a possible key its part.\<close>

definition kmrow :: "'k semi_factor \<Rightarrow> 'r compact_basis \<Rightarrow> 'k compact_basis" where
  "kmrow K x = Abs_compact_basis (rproj K (Rep_compact_basis x))"

definition kmkey :: "'k semi_factor \<Rightarrow> 'k compact_basis \<Rightarrow> 'k compact_basis" where
  "kmkey K u = Abs_compact_basis (proj K\<cdot>(Rep_compact_basis u))"

lemma Rep_kmrow [simp]: "Rep_compact_basis (kmrow K x) = rproj K (Rep_compact_basis x)"
  unfolding kmrow_def by (simp add: compact_proj_compact row_key_compact)

lemma Rep_kmkey [simp]: "Rep_compact_basis (kmkey K u) = proj K\<cdot>(Rep_compact_basis u)"
  unfolding kmkey_def by (simp add: compact_proj_compact)

lemma keymix_consistent: "upper_le0 (Abs_pde_basis (kmkey K ` skeys t)) (Abs_pde_basis (kmrow K ` srows t))"
  unfolding upper_le0_def
proof (simp, intro ballI)
  fix x assume x: "x \<in> srows t"
  obtain u where u: "u \<in> skeys t" and ux: "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
    using split_basis_consistentD [OF x] by blast
  have "kmkey K u \<sqsubseteq> kmrow K x" unfolding compact_le_def by (simp add: monofun_cfun_arg [OF ux])
  then show "\<exists>v\<in>skeys t. kmkey K v \<sqsubseteq> kmrow K x" using u by blast
qed

definition SKeyMix :: "'k semi_factor \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> 'k mix_basis" where
  "SKeyMix K t = MixB (Abs_pde_basis (kmrow K ` srows t)) (Abs_pde_basis (kmkey K ` skeys t))"

lemma mdef_SKeyMix [simp]: "Rep_pde_basis (mdef (SKeyMix K t)) = kmrow K ` srows t"
  and mposs_SKeyMix [simp]: "Rep_pde_basis (mposs (SKeyMix K t)) = kmkey K ` skeys t"
  unfolding SKeyMix_def by (simp_all add: keymix_consistent)

lemma cb_below_iff: "(a :: 'a::pcpo compact_basis) \<sqsubseteq> b \<longleftrightarrow> Rep_compact_basis a \<sqsubseteq> Rep_compact_basis b"
  unfolding compact_le_def ..

lemma kmrow_mono: "x \<sqsubseteq> y \<Longrightarrow> kmrow K x \<sqsubseteq> kmrow K y"
  and kmkey_mono: "u \<sqsubseteq> w \<Longrightarrow> kmkey K u \<sqsubseteq> kmkey K w"
  unfolding compact_le_def by (simp_all add: monofun_cfun_arg)

lemma SKeyMix_mix_mono:
  assumes "split_le s t"
  shows "mix_le (SKeyMix K s) (SKeyMix K t)"
  unfolding mix_le_def lower_le0_def upper_le0_def mdef_SKeyMix mposs_SKeyMix
  using assms unfolding split_le_def hoare_le_def smyth_le_def by (blast intro: kmrow_mono kmkey_mono)

definition split_keymix :: "'k semi_factor \<Rightarrow> ('r, 'k) split_pd \<rightarrow> 'k mix_pd" where
  "split_keymix K = split_pd.extension (\<lambda>t. mix_principal (SKeyMix K t))"

lemma split_keymix_principal [simp]: "split_keymix K\<cdot>(split_principal t) = mix_principal (SKeyMix K t)"
  unfolding split_keymix_def by (simp add: split_pd.extension_principal SKeyMix_mix_mono)

lemma compact_split_keymix: "compact C \<Longrightarrow> compact (split_keymix K\<cdot>C)"
  by (auto dest!: split_pd.compact_imp_principal simp: mix_pd.compact_principal)

text \<open>A key part is definite in the key mix where it is below the part of a definite row, and
  possible where it is possible in the dataset.\<close>

lemma keymix_definite_imp:
  assumes c: "compact q" and d: "mix_definite q (split_keymix K\<cdot>C)"
  shows "\<exists>y. split_definite y C \<and> q \<sqsubseteq> rproj K y"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and CZ: "C = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have chM: "chain (\<lambda>i. mix_principal (SKeyMix K (Z i)))"
    by (rule mix_pd.ch2ch_principal) (blast intro: Z [rule_format] SKeyMix_mix_mono)
  have "split_keymix K\<cdot>C = (\<Squnion>i. mix_principal (SKeyMix K (Z i)))" unfolding CZ contlub_cfun_arg [OF ch] by simp
  then obtain i where di: "mix_definite q (mix_principal (SKeyMix K (Z i)))"
    using d mix_definite_lub [OF chM c] by auto
  let ?a = "Abs_compact_basis q"
  have qa: "Rep_compact_basis ?a = q" by (rule Abs_compact_basis_inverse' [OF c])
  have "mix_definite (Rep_compact_basis ?a) (mix_principal (SKeyMix K (Z i)))" using di by (simp only: qa)
  then obtain x where x: "x \<in> srows (Z i)" and ax: "?a \<sqsubseteq> kmrow K x"
    unfolding mix_definite_principal mdef_SKeyMix by blast
  have qx: "q \<sqsubseteq> rproj K (Rep_compact_basis x)" using ax unfolding cb_below_iff qa Rep_kmrow .
  have "split_definite (Rep_compact_basis x) C"
    by (rule split_definite_mono [OF generator_definite [OF x]]) (simp only: CZ is_ub_thelub [OF ch])
  then show ?thesis using qx by blast
qed

lemma keymix_definite_open:
  "mix_definite (rproj K (Rep_compact_basis a)) (split_keymix K\<cdot>(split_open_unit\<cdot>(Rep_compact_basis a)))"
proof -
  have "mix_definite (Rep_compact_basis (kmrow K a)) (mix_principal (SKeyMix K (SOpen a)))"
    unfolding mix_definite_principal by simp
  then show ?thesis by simp
qed

lemma keymix_definite:
  assumes y: "split_definite y C" and qy: "q \<sqsubseteq> rproj K y" and c: "compact q"
  shows "mix_definite q (split_keymix K\<cdot>C)"
proof -
  obtain r :: "nat \<Rightarrow> 'r \<rightarrow> 'r" where r: "approx_chain r" using bifinite by blast
  interpret R: approx_chain r by (fact r)
  have ch: "chain (\<lambda>n. rproj K (r n\<cdot>y))" by (intro ch2ch_Rep_cfunR ch2ch_Rep_cfunL R.chain_approx)
  have chy: "chain (\<lambda>n. r n\<cdot>y)" by (rule ch2ch_Rep_cfunL [OF R.chain_approx])
  have ly: "(\<Squnion>n. r n\<cdot>y) = y" using contlub_cfun_fun [OF R.chain_approx, of y] R.lub_approx by simp
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
  moreover have "mix_definite (rproj K (r n\<cdot>y)) (split_keymix K\<cdot>(split_open_unit\<cdot>(r n\<cdot>y)))"
    using keymix_definite_open [of K ?a] unfolding ya .
  ultimately show ?thesis by (blast intro: mix_definite_mono mix_definite_below [OF _ n])
qed

lemma keymix_possible:
  assumes c: "compact \<kappa>"
  shows "mix_possible \<kappa> (split_keymix K\<cdot>C) \<longleftrightarrow> split_possible_at K \<kappa> C"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and CZ: "C = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have chM: "chain (\<lambda>i. mix_principal (SKeyMix K (Z i)))"
    by (rule mix_pd.ch2ch_principal) (blast intro: Z [rule_format] SKeyMix_mix_mono)
  have M: "split_keymix K\<cdot>C = (\<Squnion>i. mix_principal (SKeyMix K (Z i)))" unfolding CZ contlub_cfun_arg [OF ch] by simp
  let ?a = "Abs_compact_basis \<kappa>"
  have ka: "Rep_compact_basis ?a = \<kappa>" by (rule Abs_compact_basis_inverse' [OF c])
  have each: "mix_possible \<kappa> (mix_principal (SKeyMix K (Z i))) \<longleftrightarrow> split_possible_at K \<kappa> (split_principal (Z i))" for i
  proof -
    have "mix_possible \<kappa> (mix_principal (SKeyMix K (Z i))) \<longleftrightarrow> (\<exists>u\<in>kmkey K ` skeys (Z i). u \<sqsubseteq> ?a)"
      using mix_possible_principal [of ?a "SKeyMix K (Z i)"] unfolding ka mposs_SKeyMix .
    also have "\<dots> \<longleftrightarrow> (\<exists>u\<in>skeys (Z i). proj K\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>)"
      unfolding cb_below_iff ka by auto
    finally show ?thesis unfolding possible_at_principal .
  qed
  have "split_possible_at K \<kappa> C \<longleftrightarrow> (\<forall>i. split_possible_at K \<kappa> (split_principal (Z i)))"
    unfolding CZ using split_possible_at_lub [OF ch] split_possible_at_below [OF _ is_ub_thelub [OF ch]] by blast
  then show ?thesis unfolding M mix_possible_lub [OF chM] each ..
qed

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
    unfolding keymix_possible [OF c] using refuted_TT_impossible impossible_refuted by blast
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

end

end
