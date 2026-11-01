theory Split_Csem
  imports Split_Semantics
begin

section \<open>Content semantics over split datasets\<close>

text \<open>The contents of an expression over a split dataset, at a frame and a key, are the dataset as
  seen from each entry: selected at the entry's selector, exactly at the key's part.  A value entry
  sees the selection through its view (its columns and key part).  A guard entry sees it filtered:
  by its key guard together with the frame's slice, coarsened to the entry's upper part, on the
  possible keys, and by its row guard together with the frame's ambient filter on the definite
  rows.  The extended semantics \<^emph>\<open>factors through the contents\<close> when it is a function of them, the
  frame and the key, wherever the selected parts are compact.\<close>

context split_dataspace
begin

definition sel_select :: "'k selector \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" where
  "sel_select S F k = split_select (sel_at S (flod F)) (proj (sel_at S (flod F))\<cdot>k)"

definition gcontent_ext :: "('r, 'k) split_pd \<Rightarrow> ('k, 'r guard \<times> 'k guard) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('r, 'k) split_pd" where
  "gcontent_ext D e F k = split_rowguard (gand (amb F) (eguard e))\<cdot>
     (split_keyguard (gand (sopen (coarsen (eupper e) (slice F))) (ekguard e))\<cdot>(sel_select (esel e) F k\<cdot>D))"

definition vcontent_ext :: "('r, 'k) split_pd \<Rightarrow> ('k, 'r semi_factor) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('r, 'k) split_pd" where
  "vcontent_ext D e F k = split_view (eview e)\<cdot>(sel_select (esel e) F k\<cdot>D)"

abbreviation gcontents_ext :: "('r, 'k) split_pd \<Rightarrow> ('k, 'r guard \<times> 'k guard) entry list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('r, 'k) split_pd list" where
  "gcontents_ext D gs F k \<equiv> map (\<lambda>e. gcontent_ext D e F k) gs"

abbreviation vcontents_ext :: "('r, 'k) split_pd \<Rightarrow> ('k, 'r semi_factor) entry list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('r, 'k) split_pd list" where
  "vcontents_ext D es F k \<equiv> map (\<lambda>e. vcontent_ext D e F k) es"

abbreviation sel_compact :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> bool" where
  "sel_compact X F k \<equiv> \<forall>S\<in>set (esels X). compact (proj (sel_at S (flod F))\<cdot>k)"

text \<open>The factorisation is stated for datasets below a conforming one, where the semantics is
  meant.\<close>

abbreviation conf_bounded :: "('r, 'k) split_pd \<Rightarrow> bool" where
  "conf_bounded D \<equiv> \<exists>C. D \<sqsubseteq> C \<and> conforming_rows (split_rows\<cdot>C)"

definition ext_csem :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow>
    (('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd) \<Rightarrow> bool" where
  "ext_csem X c \<longleftrightarrow> (\<forall>D F k. conf_bounded D \<longrightarrow> sel_compact X F k \<longrightarrow>
     sem_ext X D F k = c (gcontents_ext D (eguards X) F k) (vcontents_ext D (evalues X) F k) F k)"

lemma ext_csemI:
  "(\<And>D F k. conf_bounded D \<Longrightarrow> sel_compact X F k \<Longrightarrow>
      sem_ext X D F k = c (gcontents_ext D (eguards X) F k) (vcontents_ext D (evalues X) F k) F k) \<Longrightarrow>
     ext_csem X c"
  unfolding ext_csem_def by blast

lemma ext_csemD:
  "ext_csem X c \<Longrightarrow> conf_bounded D \<Longrightarrow> sel_compact X F k \<Longrightarrow>
     sem_ext X D F k = c (gcontents_ext D (eguards X) F k) (vcontents_ext D (evalues X) F k) F k"
  unfolding ext_csem_def by blast


subsection \<open>Contents at the key of the key LOD\<close>

text \<open>An entry's selector reads the key below the key LOD of a semilawful expression, so its
  contents at a key and at the key's projection to the key LOD agree.\<close>

lemma sel_select_proj: "sel_at S (flod F) \<sqsubseteq> K \<Longrightarrow> sel_select S F (proj K\<cdot>k) = sel_select S F k"
  unfolding sel_select_def by (simp only: proj_le)

lemma sel_below_kd: "semilawful X \<Longrightarrow> S \<in> set (esels X) \<Longrightarrow> sel_at S (flod F) \<sqsubseteq> kd X F"
  by (rule lattice_join_mono [OF lower_below_mind lattice_meet_le2])

lemma contents_kd:
  assumes X: "semilawful X"
  shows "gcontents_ext D (eguards X) F (proj (kd X F)\<cdot>k) = gcontents_ext D (eguards X) F k"
    and "vcontents_ext D (evalues X) F (proj (kd X F)\<cdot>k) = vcontents_ext D (evalues X) F k"
  by (auto simp: gcontent_ext_def vcontent_ext_def sel_select_proj [OF sel_below_kd [OF X]] esels_guardI esels_valueI)

lemma sel_compact_kd: "semilawful X \<Longrightarrow> sel_compact X F k \<Longrightarrow> sel_compact X F (proj (kd X F)\<cdot>k)"
  by (simp add: proj_le sel_below_kd)

lemma ext_csemD_kd:
  assumes c: "ext_csem X c" and X: "semilawful X" and D: "conf_bounded D" and k: "sel_compact X F k"
  shows "sem_ext X D F (proj (kd X F)\<cdot>k) = c (gcontents_ext D (eguards X) F k) (vcontents_ext D (evalues X) F k) F (proj (kd X F)\<cdot>k)"
  using ext_csemD [OF c D sel_compact_kd [OF X k]] by (simp only: contents_kd [OF X])


subsection \<open>Presence on views and trivial guards\<close>

lemma split_rowguard_TT [simp]: "split_rowguard (\<Lambda> _. TT)\<cdot>C = C"
  by (induct C rule: split_pd.principal_induct) (simp, simp, rule split_principal_eqI, simp_all)

lemma split_keyguard_TT [simp]: "split_keyguard (\<Lambda> _. TT)\<cdot>C = C"
  by (induct C rule: split_pd.principal_induct) (simp, simp, rule split_principal_eqI, simp_all)

text \<open>A view keeps whether there are rows and whether there are possible keys.\<close>

lemma split_view_rows_bot: "split_rows\<cdot>(split_view v\<cdot>C) = \<bottom> \<longleftrightarrow> split_rows\<cdot>C = \<bottom>"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and CZ: "C = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have chV: "chain (\<lambda>i. split_principal (SView v (Z i)))"
    by (rule split_pd.ch2ch_principal) (blast intro: Z [rule_format] SView_split_mono)
  have V: "split_view v\<cdot>C = (\<Squnion>i. split_principal (SView v (Z i)))" unfolding CZ contlub_cfun_arg [OF ch] by simp
  have "split_rows\<cdot>(split_view v\<cdot>C) = \<bottom> \<longleftrightarrow> (\<forall>i. split_rows\<cdot>(split_principal (SView v (Z i))) = \<bottom>)"
    unfolding V contlub_cfun_arg [OF chV] by (rule lub_eq_bottom_iff [OF ch2ch_Rep_cfunR [OF chV]])
  also have "\<dots> \<longleftrightarrow> (\<forall>i. split_rows\<cdot>(split_principal (Z i)) = \<bottom>)" by (simp only: split_rows_principal_bot srows_SView image_is_empty)
  also have "\<dots> \<longleftrightarrow> split_rows\<cdot>C = \<bottom>"
    unfolding CZ contlub_cfun_arg [OF ch] by (rule lub_eq_bottom_iff [OF ch2ch_Rep_cfunR [OF ch], symmetric])
  finally show ?thesis .
qed

lemma split_keys_principal_Top: "split_keys\<cdot>(split_principal t) = Top \<longleftrightarrow> skeys t = {}"
  by (simp add: skeys_upper_def down_beta)

lemma split_view_keys_Top: "split_keys\<cdot>(split_view v\<cdot>C) = Top \<longleftrightarrow> split_keys\<cdot>C = Top"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and CZ: "C = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have chV: "chain (\<lambda>i. split_principal (SView v (Z i)))"
    by (rule split_pd.ch2ch_principal) (blast intro: Z [rule_format] SView_split_mono)
  have V: "split_view v\<cdot>C = (\<Squnion>i. split_principal (SView v (Z i)))" unfolding CZ contlub_cfun_arg [OF ch] by simp
  have "split_keys\<cdot>(split_view v\<cdot>C) = Top \<longleftrightarrow> (\<exists>i. Top \<sqsubseteq> split_keys\<cdot>(split_principal (SView v (Z i))))"
    unfolding V contlub_cfun_arg [OF chV] Top_below [symmetric]
    by (rule compact_below_lub_iff [OF compact_Top ch2ch_Rep_cfunR [OF chV]])
  also have "\<dots> \<longleftrightarrow> (\<exists>i. Top \<sqsubseteq> split_keys\<cdot>(split_principal (Z i)))"
    by (simp only: Top_below split_keys_principal_Top skeys_SView image_is_empty)
  also have "\<dots> \<longleftrightarrow> split_keys\<cdot>C = Top"
    unfolding CZ contlub_cfun_arg [OF ch] Top_below [symmetric]
    by (rule compact_below_lub_iff [OF compact_Top ch2ch_Rep_cfunR [OF ch], symmetric])
  finally show ?thesis .
qed

lemma split_present_view [simp]: "split_present (split_view v\<cdot>C) = split_present C"
  unfolding split_present_def by (simp only: split_view_rows_bot split_view_keys_Top)


subsection \<open>The combinators\<close>

theorem ext_csem_const: "ext_csem (const_ext v) (\<lambda>Gs Xs F k. Present\<cdot>v)"
  by (rule ext_csemI) simp

theorem ext_csem_smap:
  "ext_csem X c \<Longrightarrow> ext_csem (smap_ext g X) (\<lambda>Gs Xs F k. map_option_pd g\<cdot>(c Gs Xs F k))"
  by (rule ext_csemI) (simp add: ext_csemD del: ex_simps)

theorem ext_csem_key_at: "ext_csem (key_at_ext c) (\<lambda>Gs Xs F k. split_present (hd Xs) \<odot> Present\<cdot>(proj c\<cdot>k))"
proof (rule ext_csemI)
  fix D F k assume Dc: "conf_bounded D" and comp: "sel_compact (key_at_ext c) F k"
  have L: "sel_at (sel c c) (flod F) = c" by (simp add: join_meet_self)
  have kc: "compact (proj c\<cdot>k)" using comp by (simp add: L)
  have "key_at_sem c D k = split_present (split_select c (proj c\<cdot>k)\<cdot>D) \<odot> Present\<cdot>(proj c\<cdot>k)"
    by (simp add: select_test_guarded [OF kc])
  then show "sem_ext (key_at_ext c) D F k =
      split_present (hd (vcontents_ext D (evalues (key_at_ext c)) F k)) \<odot> Present\<cdot>(proj c\<cdot>k)"
    by (simp add: vcontent_ext_def sel_select_def L)
qed

theorem ext_csem_restrict:
  "ext_csem X c \<Longrightarrow> ext_csem (restrict_ext \<gamma> X) (\<lambda>Gs Xs F k. c Gs Xs (frestrict \<gamma> F) k)"
proof (rule ext_csemI)
  fix D F k assume c: "ext_csem X c" and Dc: "conf_bounded D" and comp: "sel_compact (restrict_ext \<gamma> X) F k"
  have comp': "sel_compact X (frestrict \<gamma> F) k" using comp by (simp add: comp_def)
  have g: "gcontents_ext D (eguards X) (frestrict \<gamma> F) k = gcontents_ext D (map (restrict_entry \<gamma>) (eguards X)) F k"
    by (simp add: gcontent_ext_def sel_select_def gand_assoc)
  have v: "vcontents_ext D (evalues X) (frestrict \<gamma> F) k = vcontents_ext D (evalues X) F k"
    by (simp add: vcontent_ext_def sel_select_def)
  show "sem_ext (restrict_ext \<gamma> X) D F k =
      c (gcontents_ext D (eguards (restrict_ext \<gamma> X)) F k) (vcontents_ext D (evalues (restrict_ext \<gamma> X)) F k) (frestrict \<gamma> F) k"
    using ext_csemD [OF c Dc comp'] by (simp only: restrict_ext_simps restrict_simps g v)
qed

theorem ext_csem_present_at:
  assumes c: "ext_csem X c" and X: "semilawful X"
  shows "ext_csem (present_at_ext a \<rho> X)
    (\<lambda>Gs Xs F k. split_present (hd Gs) \<odot> c (tl Gs) Xs F (proj (kd X F)\<cdot>k))"
proof (rule ext_csemI)
  fix D F k assume Dc: "conf_bounded D" and comp: "sel_compact (present_at_ext a \<rho> X) F k"
  let ?L = "(emind X \<squnion> a) \<squnion> (\<rho> \<sqinter> flod F)"
  have kc: "compact (proj ?L\<cdot>k)" using comp by simp
  have compX: "sel_compact X F k" using comp by simp
  have p: "populated_ext D (emind X \<squnion> a) \<rho> F k
      = split_present (gcontent_ext D (mk_guard (sel (emind X \<squnion> a) \<rho>) gtrue gtrue \<bottom>) F k)"
    unfolding populated_ext_def select_test_guarded [OF kc] gcontent_ext_def sel_select_def by simp
  show "sem_ext (present_at_ext a \<rho> X) D F k =
      split_present (hd (gcontents_ext D (eguards (present_at_ext a \<rho> X)) F k)) \<odot>
        c (tl (gcontents_ext D (eguards (present_at_ext a \<rho> X)) F k)) (vcontents_ext D (evalues (present_at_ext a \<rho> X)) F k) F
          (proj (kd X F)\<cdot>k)"
    using ext_csemD_kd [OF c X Dc compX] by (simp add: p)
qed

theorem ext_csem_combine:
  assumes c\<^sub>1: "ext_csem X\<^sub>1 c\<^sub>1" and c\<^sub>2: "ext_csem X\<^sub>2 c\<^sub>2" and X\<^sub>1: "semilawful X\<^sub>1" and X\<^sub>2: "semilawful X\<^sub>2"
  shows "ext_csem (combine_ext f X\<^sub>1 X\<^sub>2) (\<lambda>Gs Xs F k. lift2_option_pd f\<cdot>
     (c\<^sub>1 (take (length (eguards X\<^sub>1)) Gs) (take (length (evalues X\<^sub>1)) Xs) F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>
     (c\<^sub>2 (drop (length (eguards X\<^sub>1)) Gs) (drop (length (evalues X\<^sub>1)) Xs) F (proj (kd X\<^sub>2 F)\<cdot>k)))"
proof (rule ext_csemI)
  fix D F k assume Dc: "conf_bounded D" and comp: "sel_compact (combine_ext f X\<^sub>1 X\<^sub>2) F k"
  have comp1: "sel_compact X\<^sub>1 F k" and comp2: "sel_compact X\<^sub>2 F k" using comp by auto
  show "sem_ext (combine_ext f X\<^sub>1 X\<^sub>2) D F k = lift2_option_pd f\<cdot>
     (c\<^sub>1 (take (length (eguards X\<^sub>1)) (gcontents_ext D (eguards (combine_ext f X\<^sub>1 X\<^sub>2)) F k))
        (take (length (evalues X\<^sub>1)) (vcontents_ext D (evalues (combine_ext f X\<^sub>1 X\<^sub>2)) F k)) F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>
     (c\<^sub>2 (drop (length (eguards X\<^sub>1)) (gcontents_ext D (eguards (combine_ext f X\<^sub>1 X\<^sub>2)) F k))
        (drop (length (evalues X\<^sub>1)) (vcontents_ext D (evalues (combine_ext f X\<^sub>1 X\<^sub>2)) F k)) F (proj (kd X\<^sub>2 F)\<cdot>k))"
    using ext_csemD_kd [OF c\<^sub>1 X\<^sub>1 Dc comp1] ext_csemD_kd [OF c\<^sub>2 X\<^sub>2 Dc comp2] by simp
qed

text \<open>A column reads the join of the sections of the selected definite rows, through its view.
  The rows of the viewed selection approximate the selected rows of the dataset and conversely, so
  both have the same upper bounds and the same join.\<close>

definition col_content_value :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> 'k \<Rightarrow> 'r" where
  "col_content_value c a X k = (if maximal_at a (proj a\<cdot>k) then lub {z \<downharpoonright> c | z. split_definite z X} else \<bottom>)"

lemma lub_same_ubs: "(\<And>u. S <| u \<longleftrightarrow> T <| u) \<Longrightarrow> lub S = lub T"
  unfolding lub_def is_lub_def by simp

lemma col_content_ubs:
  assumes kc: "compact (proj a\<cdot>k)" and mx: "maximal_at a (proj a\<cdot>k)"
  shows "col_sections c a D k <| u \<longleftrightarrow> {z \<downharpoonright> c | z. split_definite z (split_view (c, a)\<cdot>(split_select a (proj a\<cdot>k)\<cdot>D))} <| u"
proof -
  let ?\<kappa> = "proj a\<cdot>k" and ?v = "(c, a) :: ('r, 'k) view"
  let ?X = "split_view ?v\<cdot>(split_select a ?\<kappa>\<cdot>D)"
  let ?A = "col_sections c a D k" and ?B = "{z \<downharpoonright> c | z. split_definite z ?X}"
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and DZ: "D = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have ZS: "\<forall>i. split_le (SView ?v (SSelect a ?\<kappa> (Z i))) (SView ?v (SSelect a ?\<kappa> (Z (Suc i))))"
    using Z by (blast intro: SView_split_mono SSelect_split_mono)
  have chS: "chain (\<lambda>i. split_principal (SSelect a ?\<kappa> (Z i)))"
    by (rule split_pd.ch2ch_principal) (blast intro: Z [rule_format] SSelect_split_mono)
  have X: "?X = (\<Squnion>i. split_principal (SView ?v (SSelect a ?\<kappa> (Z i))))"
  proof -
    have "split_select a ?\<kappa>\<cdot>D = (\<Squnion>i. split_principal (SSelect a ?\<kappa> (Z i)))" unfolding DZ contlub_cfun_arg [OF ch] by simp
    then show ?thesis by (simp only: contlub_cfun_arg [OF chS] split_view_principal)
  qed
  obtain r :: "nat \<Rightarrow> 'r \<rightarrow> 'r" where r: "approx_chain r" using bifinite by blast
  interpret R: approx_chain r by (fact r)
  have rc: "compact (r n\<cdot>x)" for n x by (rule finite_deflation.compact [OF R.finite_deflation_approx])
  have rb: "r n\<cdot>x \<sqsubseteq> x" for n x by (rule deflation.below [OF finite_deflation_imp_deflation [OF R.finite_deflation_approx]])
  have sec: "(x \<downharpoonright> (c \<squnion> key_supp\<cdot>a)) \<downharpoonright> c = x \<downharpoonright> c" for x :: 'r by (rule proj_le [OF lattice_join_ge1])
  have BA: "\<exists>w\<in>?A. r n\<cdot>b \<sqsubseteq> w" if b: "b \<in> ?B" for b n
  proof -
    obtain z where z: "split_definite z ?X" and bz: "b = z \<downharpoonright> c" using b by blast
    let ?f = "\<Lambda> z. r n\<cdot>(z \<downharpoonright> c)"
    obtain z' where z': "compact z'" "z' \<sqsubseteq> z" "?f\<cdot>z' = ?f\<cdot>z" by (rule compact_approx_value [of ?f z]) (simp add: rc)
    have "split_definite z' (\<Squnion>i. split_principal (SView ?v (SSelect a ?\<kappa> (Z i))))"
      using split_definite_below [OF z z'(2)] unfolding X .
    then obtain i x' where x': "x' \<in> srows (SView ?v (SSelect a ?\<kappa> (Z i)))" "z' \<sqsubseteq> Rep_compact_basis x'"
      by (rule definite_chain_generator [OF ZS _ z'(1)])
    then obtain x where x: "x \<in> srows (Z i)" "rproj a (Rep_compact_basis x) = ?\<kappa>" and xx: "x' = vrow ?v x" by auto
    have "split_definite (Rep_compact_basis x) D"
      by (rule split_definite_mono [OF generator_definite [OF x(1)]]) (simp only: DZ is_ub_thelub [OF ch])
    then have w: "Rep_compact_basis x \<downharpoonright> c \<in> ?A" using x(2) by (auto simp: col_sections_def)
    have "r n\<cdot>b = r n\<cdot>(z' \<downharpoonright> c)" using z'(3) bz by simp
    also have "\<dots> \<sqsubseteq> z' \<downharpoonright> c" by (rule rb)
    also have "\<dots> \<sqsubseteq> Rep_compact_basis x' \<downharpoonright> c" by (intro monofun_cfun_arg x'(2))
    also have "\<dots> = Rep_compact_basis x \<downharpoonright> c" unfolding xx Rep_vrow by (simp add: sec)
    finally show ?thesis using w by blast
  qed
  have AB: "\<exists>w\<in>?B. r n\<cdot>y \<sqsubseteq> w" if y: "y \<in> ?A" for y n
  proof -
    obtain y0 where y0: "split_definite y0 D" "rproj a y0 = ?\<kappa>" and yy: "y = y0 \<downharpoonright> c"
      using y by (auto simp: col_sections_def)
    let ?f = "\<Lambda> y. (rproj a y, r n\<cdot>(y \<downharpoonright> c))"
    obtain y' where y': "compact y'" "y' \<sqsubseteq> y0" "?f\<cdot>y' = ?f\<cdot>y0"
      by (rule compact_approx_value [of ?f y0]) (simp add: y0(2) kc rc)
    have "split_definite y' (\<Squnion>i. split_principal (Z i))" using split_definite_below [OF y0(1) y'(2)] unfolding DZ .
    then obtain i x where x: "x \<in> srows (Z i)" "y' \<sqsubseteq> Rep_compact_basis x"
      by (rule definite_chain_generator [OF Z _ y'(1)])
    have ky': "rproj a y' = ?\<kappa>" using y'(3) y0(2) by simp
    have "rproj a y' \<sqsubseteq> rproj a (Rep_compact_basis x)" by (intro monofun_cfun_arg x(2))
    then have xk: "rproj a (Rep_compact_basis x) = ?\<kappa>" unfolding ky' by (rule maximal_at_eq [OF mx proj_idem])
    have "vrow ?v x \<in> srows (SView ?v (SSelect a ?\<kappa> (Z i)))" using x(1) xk mx kc by auto
    then have "split_definite (Rep_compact_basis (vrow ?v x)) ?X"
      by (rule split_definite_mono [OF generator_definite]) (simp only: X is_ub_thelub [OF split_pd.ch2ch_principal [OF ZS]])
    then have "split_definite (Rep_compact_basis x \<downharpoonright> (c \<squnion> key_supp\<cdot>a)) ?X" by simp
    then have w: "Rep_compact_basis x \<downharpoonright> c \<in> ?B" by (blast intro: sec [symmetric])
    have "r n\<cdot>y = r n\<cdot>(y' \<downharpoonright> c)" using y'(3) yy by simp
    also have "\<dots> \<sqsubseteq> y' \<downharpoonright> c" by (rule rb)
    also have "\<dots> \<sqsubseteq> Rep_compact_basis x \<downharpoonright> c" by (intro monofun_cfun_arg x(2))
    finally show ?thesis using w by blast
  qed
  have ub: "S <| u" if ST: "\<And>s n. s \<in> S \<Longrightarrow> \<exists>w\<in>T. r n\<cdot>s \<sqsubseteq> w" and T: "T <| u" for S T u
  proof (rule is_ubI)
    fix s assume s: "s \<in> S"
    have "r n\<cdot>s \<sqsubseteq> u" for n using ST [OF s, of n] T by (blast intro: below_trans is_ubD)
    then have "(\<Squnion>n. r n\<cdot>s) \<sqsubseteq> u" by (intro lub_below ch2ch_Rep_cfunL R.chain_approx)
    then show "s \<sqsubseteq> u" by (simp add: contlub_cfun_fun [OF R.chain_approx, symmetric] R.lub_approx)
  qed
  show ?thesis by (blast intro: ub [OF BA] ub [OF AB])
qed

lemma col_value_content:
  assumes kc: "compact (proj a\<cdot>k)"
  shows "col_value c a D k = col_content_value c a (split_view (c, a)\<cdot>(split_select a (proj a\<cdot>k)\<cdot>D)) k"
proof (cases "maximal_at a (proj a\<cdot>k)")
  case False
  then show ?thesis by (simp add: col_value_def col_content_value_def)
next
  case mx: True
  have "lub (col_sections c a D k) = lub {z \<downharpoonright> c | z. split_definite z (split_view (c, a)\<cdot>(split_select a (proj a\<cdot>k)\<cdot>D))}"
    by (rule lub_same_ubs) (rule col_content_ubs [OF kc mx])
  then show ?thesis by (simp add: col_value_def col_content_value_def mx)
qed

theorem ext_csem_column:
  "ext_csem (column_ext c a v)
     (\<lambda>Gs Xs F k. split_present (hd Xs) \<odot> Present\<cdot>(v\<cdot>(col_content_value c a (hd Xs) k)))"
proof (rule ext_csemI)
  fix D F k assume Dc: "conf_bounded D" and comp: "sel_compact (column_ext c a v) F k"
  have L: "sel_at (sel a a) (flod F) = a" by (simp add: join_meet_self)
  have kc: "compact (proj a\<cdot>k)" using comp by (simp add: L)
  show "sem_ext (column_ext c a v) D F k =
      split_present (hd (vcontents_ext D (evalues (column_ext c a v)) F k)) \<odot>
        Present\<cdot>(v\<cdot>(col_content_value c a (hd (vcontents_ext D (evalues (column_ext c a v)) F k)) k))"
    by (simp add: vcontent_ext_def sel_select_def L select_test_guarded [OF kc] col_value_content [OF kc])
qed

text \<open>Including dimensions and filtering for keys transform the selectors as the frame changes.\<close>

lemma gcontent_ext_include: "gcontent_ext D (include_entry M e) F k = gcontent_ext D e (finclude M F) k"
  unfolding gcontent_ext_def sel_select_def include_entry_simps include_lod by simp

lemma vcontent_ext_include: "vcontent_ext D (include_entry M e) F k = vcontent_ext D e (finclude M F) k"
  unfolding vcontent_ext_def sel_select_def include_entry_simps include_lod by simp

theorem ext_csem_include_dims:
  "ext_csem X c \<Longrightarrow> ext_csem (include_dims_ext M X) (\<lambda>Gs Xs F k. c Gs Xs (finclude M F) k)"
proof (rule ext_csemI)
  fix D F k assume c: "ext_csem X c" and Dc: "conf_bounded D" and comp: "sel_compact (include_dims_ext M X) F k"
  have comp': "sel_compact X (finclude M F) k"
  proof
    fix S assume "S \<in> set (esels X)"
    then have "include_sel M S \<in> set (esels (include_dims_ext M X))" by (auto simp: comp_def)
    then have "compact (proj (sel_at (include_sel M S) (flod F))\<cdot>k)" using comp by blast
    then show "compact (proj (sel_at S (flod (finclude M F)))\<cdot>k)" by (simp only: include_lod)
  qed
  show "sem_ext (include_dims_ext M X) D F k =
      c (gcontents_ext D (eguards (include_dims_ext M X)) F k) (vcontents_ext D (evalues (include_dims_ext M X)) F k) (finclude M F) k"
    using ext_csemD [OF c Dc comp'] by (simp add: gcontent_ext_include vcontent_ext_include comp_def)
qed

lemma sel_select_ffor:
  assumes am: "lower_part S \<sqsubseteq> m"
  shows "sel_select S (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = sel_select (trunc_sel \<tau> S) F k"
  unfolding sel_select_def trunc_sel_simps ffor_key [OF am] ..

lemma gcontent_ext_ffor:
  "elower e \<sqsubseteq> m \<Longrightarrow> gcontent_ext D e (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = gcontent_ext D (for_entry \<tau> G e) F k"
  unfolding gcontent_ext_def sel_select_ffor
  by (simp add: coarsen_conj coarsen_coarsen sopen_gand gand_assoc)

lemma vcontent_ext_ffor:
  "elower e \<sqsubseteq> m \<Longrightarrow> vcontent_ext D e (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = vcontent_ext D (for_value \<tau> e) F k"
  unfolding vcontent_ext_def sel_select_ffor by simp

theorem ext_csem_filtfor:
  assumes c: "ext_csem X c" and X: "semilawful X"
  shows "ext_csem (filtfor_ext \<tau> G X) (\<lambda>Gs Xs F k. c Gs Xs (ffor \<tau> G F) (proj (kd X (ffor \<tau> G F))\<cdot>k))"
proof (rule ext_csemI)
  fix D F k assume Dc: "conf_bounded D" and comp: "sel_compact (filtfor_ext \<tau> G X) F k"
  let ?k = "proj (kd X (ffor \<tau> G F))\<cdot>k"
  have lm: "lower_part S \<sqsubseteq> emind X" if "S \<in> set (esels X)" for S by (rule lower_below_mind [OF X that])
  have comp': "sel_compact X (ffor \<tau> G F) ?k"
  proof
    fix S assume S: "S \<in> set (esels X)"
    have "trunc_sel \<tau> S \<in> set (esels (filtfor_ext \<tau> G X))" using S by (auto simp: comp_def)
    then have "compact (proj (sel_at (trunc_sel \<tau> S) (flod F))\<cdot>k)" using comp by blast
    moreover have "proj (sel_at S (flod (ffor \<tau> G F)))\<cdot>?k = proj (sel_at (trunc_sel \<tau> S) (flod F))\<cdot>k"
      by (simp only: ffor_key [OF lm [OF S]] trunc_sel_simps)
    ultimately show "compact (proj (sel_at S (flod (ffor \<tau> G F)))\<cdot>?k)" by simp
  qed
  have g: "gcontents_ext D (eguards X) (ffor \<tau> G F) ?k = gcontents_ext D (map (for_entry \<tau> G) (eguards X)) F k"
    unfolding map_map comp_def by (rule map_cong [OF refl], rule gcontent_ext_ffor [OF lm [OF esels_guardI]])
  have v: "vcontents_ext D (evalues X) (ffor \<tau> G F) ?k = vcontents_ext D (map (for_value \<tau>) (evalues X)) F k"
    unfolding map_map comp_def by (rule map_cong [OF refl], rule vcontent_ext_ffor [OF lm [OF esels_valueI]])
  show "sem_ext (filtfor_ext \<tau> G X) D F k =
      c (gcontents_ext D (eguards (filtfor_ext \<tau> G X)) F k) (vcontents_ext D (evalues (filtfor_ext \<tau> G X)) F k) (ffor \<tau> G F) ?k"
    using ext_csemD [OF c Dc comp'] by (simp only: filtfor_ext_simps filtfor_simps g v)
qed

text \<open>An expression \<^emph>\<open>factors\<close> when some function of the contents gives its extended semantics.\<close>

definition ext_factors :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> bool" where
  "ext_factors X \<longleftrightarrow> (\<exists>c. ext_csem X c)"

lemma semilawful_tuple_ext: "(\<And>X. X \<in> set Xs \<Longrightarrow> semilawful X) \<Longrightarrow> semilawful (tuple_ext Xs)"
  by (induct Xs) (simp_all add: semilawful_const_expr semilawful_combine)

theorem ext_factors_tuple:
  "(\<And>X. X \<in> set Xs \<Longrightarrow> ext_factors X \<and> semilawful X) \<Longrightarrow> ext_factors (tuple_ext Xs)"
proof (induct Xs)
  case Nil
  show ?case unfolding ext_factors_def tuple_ext.simps by (rule exI, rule ext_csem_const)
next
  case (Cons X Xs)
  obtain c where c: "ext_csem X c" and sX: "semilawful X" using Cons.prems unfolding ext_factors_def by auto
  obtain c' where c': "ext_csem (tuple_ext Xs) c'" using Cons unfolding ext_factors_def by auto
  have sXs: "semilawful (tuple_ext Xs)" by (rule semilawful_tuple_ext) (use Cons.prems in auto)
  show ?case unfolding ext_factors_def tuple_ext.simps by (rule exI, rule ext_csem_combine [OF c c' sX sXs])
qed

subsection \<open>Monotonicity in the contents\<close>

text \<open>A content semantics is \<^emph>\<open>monotone\<close> on the contents below those of a conforming dataset.
  It cannot be monotone everywhere: a column joins the sections of its rows, which are bounded only
  where the rows conform.\<close>

definition csem_mono :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow>
    (('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd) \<Rightarrow> bool" where
  "csem_mono X c \<longleftrightarrow> (\<forall>C F k Gs Gs' Xs Xs'. conforming_rows (split_rows\<cdot>C) \<longrightarrow> sel_compact X F k \<longrightarrow>
     list_all2 (\<sqsubseteq>) Gs Gs' \<longrightarrow> list_all2 (\<sqsubseteq>) Gs' (gcontents_ext C (eguards X) F k) \<longrightarrow>
     list_all2 (\<sqsubseteq>) Xs Xs' \<longrightarrow> list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues X) F k) \<longrightarrow> c Gs Xs F k \<sqsubseteq> c Gs' Xs' F k)"

lemma csem_monoI:
  "(\<And>C F k Gs Gs' Xs Xs'. conforming_rows (split_rows\<cdot>C) \<Longrightarrow> sel_compact X F k \<Longrightarrow>
     list_all2 (\<sqsubseteq>) Gs Gs' \<Longrightarrow> list_all2 (\<sqsubseteq>) Gs' (gcontents_ext C (eguards X) F k) \<Longrightarrow>
     list_all2 (\<sqsubseteq>) Xs Xs' \<Longrightarrow> list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues X) F k) \<Longrightarrow> c Gs Xs F k \<sqsubseteq> c Gs' Xs' F k) \<Longrightarrow>
     csem_mono X c"
  unfolding csem_mono_def by blast

lemma csem_monoD:
  "csem_mono X c \<Longrightarrow> conforming_rows (split_rows\<cdot>C) \<Longrightarrow> sel_compact X F k \<Longrightarrow>
     list_all2 (\<sqsubseteq>) Gs Gs' \<Longrightarrow> list_all2 (\<sqsubseteq>) Gs' (gcontents_ext C (eguards X) F k) \<Longrightarrow>
     list_all2 (\<sqsubseteq>) Xs Xs' \<Longrightarrow> list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues X) F k) \<Longrightarrow> c Gs Xs F k \<sqsubseteq> c Gs' Xs' F k"
  unfolding csem_mono_def by blast

text \<open>A dataset with rows has possible keys; so presence is monotone.\<close>

lemma split_rows_keys: "split_rows\<cdot>C \<noteq> \<bottom> \<Longrightarrow> split_keys\<cdot>C \<noteq> Top"
proof -
  assume r: "split_rows\<cdot>C \<noteq> \<bottom>"
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and CZ: "C = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have "\<not> (\<forall>i. split_rows\<cdot>(split_principal (Z i)) = \<bottom>)"
    using r unfolding CZ contlub_cfun_arg [OF ch] lub_eq_bottom_iff [OF ch2ch_Rep_cfunR [OF ch]] by simp
  then obtain i0 where i0: "srows (Z i0) \<noteq> {}" by (auto simp: srows_lower_def split: if_splits)
  have ne: "skeys (Z (j + i0)) \<noteq> {}" for j
  proof -
    have "split_rows\<cdot>(split_principal (Z i0)) \<sqsubseteq> split_rows\<cdot>(split_principal (Z (j + i0)))"
      by (intro monofun_cfun_arg chain_mono [OF ch]) simp
    then have "srows (Z (j + i0)) \<noteq> {}" using i0 by (auto simp: srows_lower_def split: if_splits)
    then obtain x where "x \<in> srows (Z (j + i0))" by blast
    then show ?thesis using split_basis_consistentD by blast
  qed
  have chK: "chain (\<lambda>j. split_keys\<cdot>(split_principal (Z (j + i0))))" by (intro ch2ch_Rep_cfunR chain_shift [OF ch])
  have "split_keys\<cdot>C = (\<Squnion>j. split_keys\<cdot>(split_principal (Z (j + i0))))"
    unfolding CZ contlub_cfun_arg [OF ch] lub_range_shift [OF ch2ch_Rep_cfunR [OF ch]] ..
  moreover have "\<not> (Top \<sqsubseteq> (\<Squnion>j. split_keys\<cdot>(split_principal (Z (j + i0)))))"
    unfolding compact_below_lub_iff [OF compact_Top chK] using ne by (simp add: skeys_upper_def down_beta)
  ultimately show ?thesis by simp
qed

lemma split_present_mono:
  assumes le: "C \<sqsubseteq> C'"
  shows "split_present C \<sqsubseteq> split_present C'"
proof (cases "split_rows\<cdot>C \<noteq> \<bottom>")
  case True
  then have "split_rows\<cdot>C' \<noteq> \<bottom>" using monofun_cfun_arg [OF le, of split_rows] by (auto simp: bottomI)
  then show ?thesis using True by (simp add: split_present_def)
next
  case nR: False
  show ?thesis
  proof (cases "split_keys\<cdot>C = Top")
    case True
    then have kT: "split_keys\<cdot>C' = Top" using monofun_cfun_arg [OF le, of split_keys] by simp
    then have "split_rows\<cdot>C' = \<bottom>" using split_rows_keys by blast
    then show ?thesis using nR True kT by (simp add: split_present_def)
  next
    case False
    then show ?thesis using nR by (simp add: split_present_def)
  qed
qed

theorem csem_mono_const: "csem_mono (const_ext v) (\<lambda>Gs Xs F k. Present\<cdot>v)"
  by (rule csem_monoI) simp

theorem csem_mono_smap: "csem_mono X c \<Longrightarrow> csem_mono (smap_ext g X) (\<lambda>Gs Xs F k. map_option_pd g\<cdot>(c Gs Xs F k))"
  by (rule csem_monoI) (simp add: monofun_cfun_arg csem_monoD)

theorem csem_mono_key_at: "csem_mono (key_at_ext c) (\<lambda>Gs Xs F k. split_present (hd Xs) \<odot> Present\<cdot>(proj c\<cdot>k))"
proof (rule csem_monoI)
  fix C F k Gs Gs' and Xs Xs' :: "('r, 'k) split_pd list"
  assume X: "list_all2 (\<sqsubseteq>) Xs Xs'" and X': "list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues (key_at_ext c)) F k)"
  obtain x' where x': "Xs' = [x']" using X' by (auto simp: list_all2_Cons2)
  obtain x where x: "Xs = [x]" "x \<sqsubseteq> x'" using X unfolding x' by (auto simp: list_all2_Cons2)
  show "split_present (hd Xs) \<odot> Present\<cdot>(proj c\<cdot>k) \<sqsubseteq> split_present (hd Xs') \<odot> Present\<cdot>(proj c\<cdot>k)"
    unfolding x x' by (simp add: monofun_cfun_fun monofun_cfun_arg split_present_mono x(2))
qed

lemma gcontents_frestrict: "gcontents_ext D (eguards X) (frestrict \<gamma> F) k = gcontents_ext D (map (restrict_entry \<gamma>) (eguards X)) F k"
  by (simp add: gcontent_ext_def sel_select_def gand_assoc)

lemma vcontents_frestrict: "vcontents_ext D es (frestrict \<gamma> F) k = vcontents_ext D es F k"
  by (simp add: vcontent_ext_def sel_select_def)

theorem csem_mono_restrict: "csem_mono X c \<Longrightarrow> csem_mono (restrict_ext \<gamma> X) (\<lambda>Gs Xs F k. c Gs Xs (frestrict \<gamma> F) k)"
proof (rule csem_monoI)
  fix C F k Gs Gs' Xs Xs'
  assume c: "csem_mono X c" and cC: "conforming_rows (split_rows\<cdot>C)" and comp: "sel_compact (restrict_ext \<gamma> X) F k"
    and G: "list_all2 (\<sqsubseteq>) Gs Gs'" and G': "list_all2 (\<sqsubseteq>) Gs' (gcontents_ext C (eguards (restrict_ext \<gamma> X)) F k)"
    and V: "list_all2 (\<sqsubseteq>) Xs Xs'" and V': "list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues (restrict_ext \<gamma> X)) F k)"
  have comp': "sel_compact X (frestrict \<gamma> F) k" using comp by (simp add: comp_def)
  show "c Gs Xs (frestrict \<gamma> F) k \<sqsubseteq> c Gs' Xs' (frestrict \<gamma> F) k"
    by (rule csem_monoD [OF c cC comp' G _ V]) (use G' V' in \<open>simp_all add: gcontents_frestrict vcontents_frestrict\<close>)
qed

lemma gcontents_finclude: "gcontents_ext D (eguards X) (finclude M F) k = gcontents_ext D (map (include_entry M) (eguards X)) F k"
  by (simp add: gcontent_ext_include)

lemma vcontents_finclude: "vcontents_ext D (evalues X) (finclude M F) k = vcontents_ext D (map (include_entry M) (evalues X)) F k"
  by (simp add: vcontent_ext_include)

theorem csem_mono_include_dims: "csem_mono X c \<Longrightarrow> csem_mono (include_dims_ext M X) (\<lambda>Gs Xs F k. c Gs Xs (finclude M F) k)"
proof (rule csem_monoI)
  fix C F k Gs Gs' Xs Xs'
  assume c: "csem_mono X c" and cC: "conforming_rows (split_rows\<cdot>C)" and comp: "sel_compact (include_dims_ext M X) F k"
    and G: "list_all2 (\<sqsubseteq>) Gs Gs'" and G': "list_all2 (\<sqsubseteq>) Gs' (gcontents_ext C (eguards (include_dims_ext M X)) F k)"
    and V: "list_all2 (\<sqsubseteq>) Xs Xs'" and V': "list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues (include_dims_ext M X)) F k)"
  have comp': "sel_compact X (finclude M F) k"
  proof
    fix S assume "S \<in> set (esels X)"
    then have "include_sel M S \<in> set (esels (include_dims_ext M X))" by (auto simp: comp_def)
    then have "compact (proj (sel_at (include_sel M S) (flod F))\<cdot>k)" using comp by blast
    then show "compact (proj (sel_at S (flod (finclude M F)))\<cdot>k)" by (simp only: include_lod)
  qed
  show "c Gs Xs (finclude M F) k \<sqsubseteq> c Gs' Xs' (finclude M F) k"
    by (rule csem_monoD [OF c cC comp' G _ V]) (use G' V' in \<open>simp_all only: gcontents_finclude vcontents_finclude include_dims_ext_simps include_dims_simps\<close>)
qed

theorem csem_mono_present_at:
  assumes c: "csem_mono X c" and X: "semilawful X"
  shows "csem_mono (present_at_ext a \<rho> X) (\<lambda>Gs Xs F k. split_present (hd Gs) \<odot> c (tl Gs) Xs F (proj (kd X F)\<cdot>k))"
proof (rule csem_monoI)
  fix C F k Gs Gs' Xs Xs'
  assume cC: "conforming_rows (split_rows\<cdot>C)" and comp: "sel_compact (present_at_ext a \<rho> X) F k"
    and G: "list_all2 (\<sqsubseteq>) Gs Gs'" and G': "list_all2 (\<sqsubseteq>) Gs' (gcontents_ext C (eguards (present_at_ext a \<rho> X)) F k)"
    and V: "list_all2 (\<sqsubseteq>) Xs Xs'" and V': "list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues (present_at_ext a \<rho> X)) F k)"
  have compX: "sel_compact X F (proj (kd X F)\<cdot>k)" by (rule sel_compact_kd [OF X]) (use comp in simp)
  obtain g' Gt' where g': "Gs' = g' # Gt'" and Gt': "list_all2 (\<sqsubseteq>) Gt' (gcontents_ext C (eguards X) F k)"
    using G' by (auto simp: list_all2_Cons2)
  obtain g Gt where g: "Gs = g # Gt" "g \<sqsubseteq> g'" and Gt: "list_all2 (\<sqsubseteq>) Gt Gt'" using G unfolding g' by (auto simp: list_all2_Cons2)
  have "c Gt Xs F (proj (kd X F)\<cdot>k) \<sqsubseteq> c Gt' Xs' F (proj (kd X F)\<cdot>k)"
    by (rule csem_monoD [OF c cC compX Gt _ V]) (use Gt' V' in \<open>simp_all only: contents_kd [OF X] present_at_ext_simps present_at_simps\<close>)
  then show "split_present (hd Gs) \<odot> c (tl Gs) Xs F (proj (kd X F)\<cdot>k) \<sqsubseteq> split_present (hd Gs') \<odot> c (tl Gs') Xs' F (proj (kd X F)\<cdot>k)"
    unfolding g g' by (simp add: monofun_cfun monofun_cfun_arg split_present_mono g(2))
qed

theorem csem_mono_combine:
  assumes c\<^sub>1: "csem_mono X\<^sub>1 c\<^sub>1" and c\<^sub>2: "csem_mono X\<^sub>2 c\<^sub>2" and X\<^sub>1: "semilawful X\<^sub>1" and X\<^sub>2: "semilawful X\<^sub>2"
  shows "csem_mono (combine_ext f X\<^sub>1 X\<^sub>2) (\<lambda>Gs Xs F k. lift2_option_pd f\<cdot>
     (c\<^sub>1 (take (length (eguards X\<^sub>1)) Gs) (take (length (evalues X\<^sub>1)) Xs) F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>
     (c\<^sub>2 (drop (length (eguards X\<^sub>1)) Gs) (drop (length (evalues X\<^sub>1)) Xs) F (proj (kd X\<^sub>2 F)\<cdot>k)))"
proof (rule csem_monoI)
  fix C F k Gs Gs' Xs Xs'
  assume cC: "conforming_rows (split_rows\<cdot>C)" and comp: "sel_compact (combine_ext f X\<^sub>1 X\<^sub>2) F k"
    and G: "list_all2 (\<sqsubseteq>) Gs Gs'" and G': "list_all2 (\<sqsubseteq>) Gs' (gcontents_ext C (eguards (combine_ext f X\<^sub>1 X\<^sub>2)) F k)"
    and V: "list_all2 (\<sqsubseteq>) Xs Xs'" and V': "list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues (combine_ext f X\<^sub>1 X\<^sub>2)) F k)"
  let ?n = "length (eguards X\<^sub>1)" and ?m = "length (evalues X\<^sub>1)"
  have comp1: "sel_compact X\<^sub>1 F (proj (kd X\<^sub>1 F)\<cdot>k)" by (rule sel_compact_kd [OF X\<^sub>1]) (use comp in auto)
  have comp2: "sel_compact X\<^sub>2 F (proj (kd X\<^sub>2 F)\<cdot>k)" by (rule sel_compact_kd [OF X\<^sub>2]) (use comp in auto)
  have G1: "list_all2 (\<sqsubseteq>) (take ?n Gs') (gcontents_ext C (eguards X\<^sub>1) F (proj (kd X\<^sub>1 F)\<cdot>k))"
    and G2: "list_all2 (\<sqsubseteq>) (drop ?n Gs') (gcontents_ext C (eguards X\<^sub>2) F (proj (kd X\<^sub>2 F)\<cdot>k))"
    using list_all2_takeI [OF G', of ?n] list_all2_dropI [OF G', of ?n] by (simp_all add: contents_kd X\<^sub>1 X\<^sub>2)
  have V1: "list_all2 (\<sqsubseteq>) (take ?m Xs') (vcontents_ext C (evalues X\<^sub>1) F (proj (kd X\<^sub>1 F)\<cdot>k))"
    and V2: "list_all2 (\<sqsubseteq>) (drop ?m Xs') (vcontents_ext C (evalues X\<^sub>2) F (proj (kd X\<^sub>2 F)\<cdot>k))"
    using list_all2_takeI [OF V', of ?m] list_all2_dropI [OF V', of ?m] by (simp_all add: contents_kd X\<^sub>1 X\<^sub>2)
  show "lift2_option_pd f\<cdot>(c\<^sub>1 (take ?n Gs) (take ?m Xs) F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(c\<^sub>2 (drop ?n Gs) (drop ?m Xs) F (proj (kd X\<^sub>2 F)\<cdot>k))
      \<sqsubseteq> lift2_option_pd f\<cdot>(c\<^sub>1 (take ?n Gs') (take ?m Xs') F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(c\<^sub>2 (drop ?n Gs') (drop ?m Xs') F (proj (kd X\<^sub>2 F)\<cdot>k))"
    by (intro monofun_cfun monofun_cfun_arg csem_monoD [OF c\<^sub>1 cC comp1 _ G1 _ V1] csem_monoD [OF c\<^sub>2 cC comp2 _ G2 _ V2]
        list_all2_takeI list_all2_dropI G V)
qed

lemma sel_compact_ffor:
  assumes X: "semilawful X" and comp: "sel_compact (filtfor_ext \<tau> G X) F k"
  shows "sel_compact X (ffor \<tau> G F) (proj (kd X (ffor \<tau> G F))\<cdot>k)"
proof
  fix S assume S: "S \<in> set (esels X)"
  have lm: "lower_part S \<sqsubseteq> emind X" by (rule lower_below_mind [OF X S])
  have "trunc_sel \<tau> S \<in> set (esels (filtfor_ext \<tau> G X))" using S by (auto simp: comp_def)
  then have "compact (proj (sel_at (trunc_sel \<tau> S) (flod F))\<cdot>k)" using comp by blast
  moreover have "proj (sel_at S (flod (ffor \<tau> G F)))\<cdot>(proj (kd X (ffor \<tau> G F))\<cdot>k) = proj (sel_at (trunc_sel \<tau> S) (flod F))\<cdot>k"
    by (simp only: ffor_key [OF lm] trunc_sel_simps)
  ultimately show "compact (proj (sel_at S (flod (ffor \<tau> G F)))\<cdot>(proj (kd X (ffor \<tau> G F))\<cdot>k))" by simp
qed

lemma contents_ffor:
  assumes X: "semilawful X"
  shows "gcontents_ext D (eguards X) (ffor \<tau> G F) (proj (kd X (ffor \<tau> G F))\<cdot>k) = gcontents_ext D (map (for_entry \<tau> G) (eguards X)) F k"
    and "vcontents_ext D (evalues X) (ffor \<tau> G F) (proj (kd X (ffor \<tau> G F))\<cdot>k) = vcontents_ext D (map (for_value \<tau>) (evalues X)) F k"
  unfolding map_map comp_def
  by (rule map_cong [OF refl], rule gcontent_ext_ffor [OF lower_below_mind [OF X esels_guardI]], assumption,
      rule map_cong [OF refl], rule vcontent_ext_ffor [OF lower_below_mind [OF X esels_valueI]], assumption)

theorem csem_mono_filtfor:
  assumes c: "csem_mono X c" and X: "semilawful X"
  shows "csem_mono (filtfor_ext \<tau> G X) (\<lambda>Gs Xs F k. c Gs Xs (ffor \<tau> G F) (proj (kd X (ffor \<tau> G F))\<cdot>k))"
proof (rule csem_monoI)
  fix C F k Gs Gs' Xs Xs'
  assume cC: "conforming_rows (split_rows\<cdot>C)" and comp: "sel_compact (filtfor_ext \<tau> G X) F k"
    and G: "list_all2 (\<sqsubseteq>) Gs Gs'" and G': "list_all2 (\<sqsubseteq>) Gs' (gcontents_ext C (eguards (filtfor_ext \<tau> G X)) F k)"
    and V: "list_all2 (\<sqsubseteq>) Xs Xs'" and V': "list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues (filtfor_ext \<tau> G X)) F k)"
  show "c Gs Xs (ffor \<tau> G F) (proj (kd X (ffor \<tau> G F))\<cdot>k) \<sqsubseteq> c Gs' Xs' (ffor \<tau> G F) (proj (kd X (ffor \<tau> G F))\<cdot>k)"
    by (rule csem_monoD [OF c cC sel_compact_ffor [OF X comp] G _ V])
      (use G' V' in \<open>simp_all only: contents_ffor [OF X] filtfor_ext_simps filtfor_simps\<close>)
qed

text \<open>The sections of the selected rows of a conforming dataset are bounded, so the column's
  content value is monotone below it.\<close>

lemma col_content_bounded:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))" and cC: "conforming_rows (split_rows\<cdot>C)"
    and kc: "compact (proj a\<cdot>k)" and mx: "maximal_at a (proj a\<cdot>k)"
  shows "\<exists>b. {z \<downharpoonright> c | z. split_definite z (split_view (c, a)\<cdot>(split_select a (proj a\<cdot>k)\<cdot>C))} <| b"
proof (cases "col_sections c a C k = {}")
  case True
  then have "col_sections c a C k <| \<bottom>" by simp
  then show ?thesis using col_content_ubs [OF kc mx] by blast
next
  case False
  then obtain b where "col_sections c a C k <| b" using col_sections_ub [OF fd cC mx] by blast
  then show ?thesis using col_content_ubs [OF kc mx] by blast
qed

theorem csem_mono_column:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))"
  shows "csem_mono (column_ext c a v) (\<lambda>Gs Xs F k. split_present (hd Xs) \<odot> Present\<cdot>(v\<cdot>(col_content_value c a (hd Xs) k)))"
proof (rule csem_monoI)
  fix C F k Gs Gs' and Xs Xs' :: "('r, 'k) split_pd list"
  assume cC: "conforming_rows (split_rows\<cdot>C)" and comp: "sel_compact (column_ext c a v) F k"
    and X: "list_all2 (\<sqsubseteq>) Xs Xs'" and X': "list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues (column_ext c a v)) F k)"
  have L: "sel_at (sel a a) (flod F) = a" by (simp add: join_meet_self)
  have kc: "compact (proj a\<cdot>k)" using comp by (simp add: L)
  let ?XC = "split_view (c, a)\<cdot>(split_select a (proj a\<cdot>k)\<cdot>C)"
  obtain x' where x': "Xs' = [x']" and xC: "x' \<sqsubseteq> ?XC"
    using X' by (auto simp: list_all2_Cons2 vcontent_ext_def sel_select_def L)
  obtain x where x: "Xs = [x]" and xx: "x \<sqsubseteq> x'" using X unfolding x' by (auto simp: list_all2_Cons2)
  have cv: "col_content_value c a x k \<sqsubseteq> col_content_value c a x' k"
  proof (cases "maximal_at a (proj a\<cdot>k) \<and> {z \<downharpoonright> c | z. split_definite z x} \<noteq> {}")
    case True
    then have mx: "maximal_at a (proj a\<cdot>k)" and ne: "{z \<downharpoonright> c | z. split_definite z x} \<noteq> {}" by simp_all
    obtain b where b: "{z \<downharpoonright> c | z. split_definite z ?XC} <| b" using col_content_bounded [OF fd cC kc mx] by blast
    have s1: "{z \<downharpoonright> c | z. split_definite z x} \<subseteq> {z \<downharpoonright> c | z. split_definite z x'}"
      using split_definite_mono [OF _ xx] by blast
    have "{z \<downharpoonright> c | z. split_definite z x'} \<subseteq> {z \<downharpoonright> c | z. split_definite z ?XC}"
      using split_definite_mono [OF _ xC] by blast
    then have b': "{z \<downharpoonright> c | z. split_definite z x'} <| b" using b by (auto simp: is_ub_def)
    show ?thesis unfolding col_content_value_def by (simp only: if_P [OF mx]) (rule lub_subset_below [OF ne s1 b'])
  next
    case False
    then show ?thesis unfolding col_content_value_def by (auto simp: lub_empty)
  qed
  show "split_present (hd Xs) \<odot> Present\<cdot>(v\<cdot>(col_content_value c a (hd Xs) k)) \<sqsubseteq>
      split_present (hd Xs') \<odot> Present\<cdot>(v\<cdot>(col_content_value c a (hd Xs') k))"
    unfolding x x' by (simp add: monofun_cfun monofun_cfun_arg split_present_mono xx cv)
qed

subsection \<open>Inner contents of an aggregate\<close>

text \<open>An aggregate releases its argument's entries: a released entry selects only at its upper
  part within the frame, and keys its content by the lower part as well.  At an inner key whose
  part at the frame LOD is the outer key, the argument's contents are the released contents
  selected further at the inner key: guard contents directly, value contents through the view and
  back down to their own keys.\<close>

lemma upper_frame_part:
  assumes kk: "proj (flod F)\<cdot>\<kappa> = k"
  shows "proj (eupper e \<sqinter> flod F)\<cdot>\<kappa> = proj (eupper e \<sqinter> flod F)\<cdot>k"
proof -
  have "proj (eupper e \<sqinter> flod F)\<cdot>(proj (flod F)\<cdot>\<kappa>) = proj (eupper e \<sqinter> flod F)\<cdot>\<kappa>"
    by (rule proj_le) (rule lattice_meet_le2)
  then show ?thesis using kk by simp
qed

lemma inner_select:
  assumes kk: "proj (flod F)\<cdot>\<kappa> = k" and c: "compact (proj l\<cdot>\<kappa>)" and cU: "compact (proj (eupper e \<sqinter> flod F)\<cdot>k)"
  shows "split_select l (proj l\<cdot>\<kappa>)\<cdot>(split_select (eupper e \<sqinter> flod F) (proj (eupper e \<sqinter> flod F)\<cdot>k)\<cdot>D)
    = split_select (l \<squnion> (eupper e \<sqinter> flod F)) (proj (l \<squnion> (eupper e \<sqinter> flod F))\<cdot>\<kappa>)\<cdot>D"
  using split_select_join [OF c cU refl upper_frame_part [OF kk]] by simp

lemma inner_gcontent:
  assumes kk: "proj (flod F)\<cdot>\<kappa> = k" and c: "compact (proj (sel_at (esel e) (flod F))\<cdot>\<kappa>)"
    and cU: "compact (proj (eupper e \<sqinter> flod F)\<cdot>k)"
  shows "gcontent_ext D e F \<kappa> = split_select (sel_at (esel e) (flod F)) (proj (sel_at (esel e) (flod F))\<cdot>\<kappa>)\<cdot>(gcontent_ext D (release e) F k)"
proof -
  let ?L = "sel_at (esel e) (flod F)" and ?U = "eupper e \<sqinter> flod F"
  have U: "sel_at (esel (release e)) (flod F) = ?U" by simp
  have LU: "?L \<squnion> ?U = ?L" by (rule lattice_join_absorb1) (rule lattice_join_ge2)
  have "split_select ?L (proj ?L\<cdot>\<kappa>)\<cdot>(split_select ?U (proj ?U\<cdot>k)\<cdot>D) = split_select ?L (proj ?L\<cdot>\<kappa>)\<cdot>D"
    using inner_select [OF kk c cU] by (simp only: LU)
  then show ?thesis
    unfolding gcontent_ext_def sel_select_def U by (simp add: split_select_keyguard_comm split_select_rowguard_comm)
qed

lemma inner_vcontent:
  assumes kk: "proj (flod F)\<cdot>\<kappa> = k" and c: "compact (proj (sel_at (esel e) (flod F))\<cdot>\<kappa>)"
    and cU: "compact (proj (eupper e \<sqinter> flod F)\<cdot>k)"
  shows "vcontent_ext D e F \<kappa> = split_view (eview e)\<cdot>(split_select (elower e) (proj (elower e)\<cdot>\<kappa>)\<cdot>(vcontent_ext D (release e) F k))"
proof -
  let ?L = "sel_at (esel e) (flod F)" and ?U = "eupper e \<sqinter> flod F" and ?l = "elower e"
  have U: "sel_at (esel (release e)) (flod F) = ?U" by simp
  have cl: "compact (proj ?l\<cdot>\<kappa>)"
  proof -
    have "proj ?l\<cdot>(proj ?L\<cdot>\<kappa>) = proj ?l\<cdot>\<kappa>" by (rule proj_le) (rule lattice_join_ge1)
    then show ?thesis using compact_proj_compact [OF c, of ?l] by simp
  qed
  have lv: "?l \<sqsubseteq> snd (eview (release e))" by (simp add: lattice_join_ge2)
  have "split_select ?l (proj ?l\<cdot>\<kappa>)\<cdot>(vcontent_ext D (release e) F k)
      = split_view (eview (release e))\<cdot>(split_select ?l (proj ?l\<cdot>\<kappa>)\<cdot>(split_select ?U (proj ?U\<cdot>k)\<cdot>D))"
    unfolding vcontent_ext_def sel_select_def U by (rule split_select_view [OF lv])
  also have "\<dots> = split_view (eview (release e))\<cdot>(split_select ?L (proj ?L\<cdot>\<kappa>)\<cdot>D)"
    by (simp only: inner_select [OF kk cl cU])
  finally show ?thesis
    unfolding vcontent_ext_def sel_select_def by (simp add: split_view_view lattice_join_ge1)
qed

text \<open>The presence of an inner key is read off the fold guard's content, selected at the inner key.\<close>

lemma inner_presence:
  assumes kk: "proj (flod F)\<cdot>\<kappa> = k" and kK: "proj (kd X F)\<cdot>\<kappa> = \<kappa>" and c: "compact \<kappa>"
  shows "populated_ext D (emind X) \<top> F \<kappa> =
    split_present (split_select (kd X F) \<kappa>\<cdot>(gcontent_ext D (mk_guard (sel \<bottom> \<top>) gtrue gtrue (emind X)) F k))"
proof -
  have T: "\<top> \<sqinter> L = L" for L :: "'k semi_factor" by (rule lattice_meet_top_left)
  have K: "emind X \<squnion> (\<top> \<sqinter> flod F) = kd X F" by (simp only: T)
  have B: "\<bottom> \<squnion> (\<top> \<sqinter> flod F) = flod F" by (simp only: T lattice_join_bot_left)
  have kf: "proj (flod F)\<cdot>k = k" unfolding kk [symmetric] by (rule proj_idem)
  have le: "flod F \<sqsubseteq> kd X F" by (rule lattice_join_ge2)
  have sel: "split_select (kd X F) \<kappa>\<cdot>(split_select (flod F) k\<cdot>D) = split_select (kd X F) \<kappa>\<cdot>D"
    by (rule split_select_compose [OF c le kk])
  have pe: "populated_ext D (emind X) \<top> F \<kappa> = select_test (kd X F) \<kappa> (amb F) (sopen (coarsen \<top> (slice F))) D"
    unfolding populated_ext_def K kK ..
  show ?thesis
    unfolding pe select_test_guarded [OF c] gcontent_ext_def sel_select_def
    by (simp only: entry.select_convs selector.select_convs fst_conv snd_conv B kf split_select_keyguard_comm split_select_rowguard_comm sel gand_gtrue)
qed

text \<open>The guard filters and selection only drop definite rows and possible keys: a definite row of
  the filtered dataset is one of the dataset, and a key part possible there is possible in it.\<close>

lemma filter_definite:
  fixes \<Phi> :: "('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" and C :: "('r, 'k) split_pd"
  assumes P: "\<And>t. \<Phi>\<cdot>(split_principal t) = split_principal (\<Psi> t)" and S: "\<And>t. srows (\<Psi> t) \<subseteq> srows t"
    and M: "\<And>s t. split_le s t \<Longrightarrow> split_le (\<Psi> s) (\<Psi> t)" and d: "split_definite y (\<Phi>\<cdot>C)"
  shows "split_definite y C"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and CZ: "C = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have ZP: "\<forall>i. split_le (\<Psi> (Z i)) (\<Psi> (Z (Suc i)))" using Z M by blast
  have PC: "\<Phi>\<cdot>C = (\<Squnion>i. split_principal (\<Psi> (Z i)))" unfolding CZ contlub_cfun_arg [OF ch] P ..
  obtain r :: "nat \<Rightarrow> 'r \<rightarrow> 'r" where r: "approx_chain r" using bifinite by blast
  interpret R: approx_chain r by (fact r)
  have "split_definite (r n\<cdot>y) C" for n
  proof -
    have c: "compact (r n\<cdot>y)" by (rule finite_deflation.compact [OF R.finite_deflation_approx])
    have "split_definite (r n\<cdot>y) (\<Squnion>i. split_principal (\<Psi> (Z i)))"
      unfolding PC [symmetric]
      by (rule split_definite_below [OF d deflation.below [OF finite_deflation_imp_deflation [OF R.finite_deflation_approx]]])
    then obtain i x where x: "x \<in> srows (\<Psi> (Z i))" "r n\<cdot>y \<sqsubseteq> Rep_compact_basis x"
      by (rule definite_chain_generator [OF ZP _ c])
    have "split_definite (Rep_compact_basis x) C"
      by (rule split_definite_mono [OF generator_definite [OF subsetD [OF S x(1)]]]) (simp only: CZ is_ub_thelub [OF ch])
    then show ?thesis by (rule split_definite_below [OF _ x(2)])
  qed
  then have "(\<Squnion>n. split_open_unit\<cdot>(r n\<cdot>y)) \<sqsubseteq> C" unfolding split_definite_def by (intro lub_below ch2ch_Rep_cfunR ch2ch_Rep_cfunL R.chain_approx)
  then show ?thesis unfolding split_definite_def
    by (simp add: contlub_cfun_arg [OF ch2ch_Rep_cfunL [OF R.chain_approx], symmetric] contlub_cfun_fun [OF R.chain_approx, symmetric] R.lub_approx)
qed

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

lemma filter_possible:
  fixes \<Phi> :: "('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" and C :: "('r, 'k) split_pd"
  assumes P: "\<And>t. \<Phi>\<cdot>(split_principal t) = split_principal (\<Psi> t)" and S: "\<And>t. skeys (\<Psi> t) \<subseteq> skeys t"
    and M: "\<And>s t. split_le s t \<Longrightarrow> split_le (\<Psi> s) (\<Psi> t)" and p: "split_possible_at K \<kappa> (\<Phi>\<cdot>C)"
  shows "split_possible_at K \<kappa> C"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and CZ: "C = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have chP: "chain (\<lambda>i. split_principal (\<Psi> (Z i)))" by (rule split_pd.ch2ch_principal) (blast intro: Z [rule_format] M)
  have PC: "\<Phi>\<cdot>C = (\<Squnion>i. split_principal (\<Psi> (Z i)))" unfolding CZ contlub_cfun_arg [OF ch] P ..
  have "split_possible_at K \<kappa> (split_principal (Z i))" for i
  proof -
    have "split_possible_at K \<kappa> (split_principal (\<Psi> (Z i)))"
      by (rule split_possible_at_below [OF p]) (simp only: PC is_ub_thelub [OF chP])
    then show ?thesis unfolding possible_at_principal using S by blast
  qed
  then show ?thesis unfolding CZ by (rule split_possible_at_lub [OF ch])
qed

text \<open>The content of a guard entry is such a filtered selection.\<close>

lemma gcontent_definite: "split_definite y (gcontent_ext D e F k) \<Longrightarrow> split_definite y D"
  unfolding gcontent_ext_def sel_select_def
  by (rule filter_definite [where \<Phi> = "split_rowguard _ oo split_keyguard _ oo split_select _ _"
        and \<Psi> = "\<lambda>t. SRowGuard _ (SKeyGuard _ (SSelect _ _ t))"])
     (auto intro: SRowGuard_split_mono SKeyGuard_split_mono SSelect_split_mono)

lemma gcontent_possible: "split_possible_at K \<kappa> (gcontent_ext D e F k) \<Longrightarrow> split_possible_at K \<kappa> D"
  unfolding gcontent_ext_def sel_select_def
  by (rule filter_possible [where \<Phi> = "split_rowguard _ oo split_keyguard _ oo split_select _ _"
        and \<Psi> = "\<lambda>t. SRowGuard _ (SKeyGuard _ (SSelect _ _ t))"])
     (auto intro: SRowGuard_split_mono SKeyGuard_split_mono SSelect_split_mono)


subsection \<open>The aggregate on its contents\<close>

text \<open>Members whose value is the fold's unit do not change it, and members below the unit only
  lower it.\<close>

lemma agg_fold_neutral_left:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and B: "finite B" and AB: "A \<subseteq> B"
    and v: "\<And>a. a \<in> B - A \<Longrightarrow> v a = Absent"
  shows "agg_fold f v A = agg_fold f v B"
proof -
  interpret agg: comm_monoid_set "\<lambda>x y. combine_option_pd f\<cdot>x\<cdot>y" Absent
    unfolding comm_monoid_set_def by (rule comm_monoid_combine_option_pd [OF f])
  show ?thesis unfolding agg_fold_finite [OF f B] agg_fold_finite [OF f finite_subset [OF AB B]]
    using B AB v by (intro agg.mono_neutral_left) auto
qed

lemma agg_fold_below_unit:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and B: "finite B" and AB: "A \<subseteq> B"
    and v: "\<And>a. a \<in> B - A \<Longrightarrow> v a \<sqsubseteq> Absent"
  shows "agg_fold f v B \<sqsubseteq> agg_fold f v A"
proof -
  let ?w = "\<lambda>a. if a \<in> A then v a else Absent"
  have "agg_fold f v B \<sqsubseteq> agg_fold f ?w B" by (rule agg_fold_mono [OF f B]) (use v in auto)
  also have "\<dots> = agg_fold f ?w A" by (rule agg_fold_neutral_left [OF f B AB, symmetric]) simp
  also have "\<dots> = agg_fold f v A" by (rule agg_fold_cong [OF f]) simp_all
  finally show ?thesis .
qed

lemma tr_mult_plus_Absent: "t \<noteq> TT \<Longrightarrow> t \<odot> x + Absent = t \<odot> x"
  by (cases t rule: trE) (simp_all add: plus_option_pd_assoc)

text \<open>The aggregate's argument contents at an inner key are read off its released contents at the
  outer key; the inner key's presence off the fold guard's content.  The content aggregate folds
  these over the inner keys definite and possible in the fold guard's content.\<close>

definition agg_inner_g :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow>
    ('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list" where
  "agg_inner_g X F \<kappa> Gr = map2 (\<lambda>e G. sel_select (esel e) F \<kappa>\<cdot>G) (eguards X) Gr"

definition agg_inner_v :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> 'k \<Rightarrow> ('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list" where
  "agg_inner_v X \<kappa> Xr = map2 (\<lambda>e V. split_view (eview e)\<cdot>(split_select (elower e) (proj (elower e)\<cdot>\<kappa>)\<cdot>V)) (evalues X) Xr"

definition cagg_value :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow>
    (('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd) \<Rightarrow>
    ('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd" where
  "cagg_value X c Gs Xs F \<kappa> = split_present (split_select (kd X F) \<kappa>\<cdot>(hd Gs)) \<odot>
     c (agg_inner_g X F \<kappa> (tl Gs)) (agg_inner_v X \<kappa> Xs) F \<kappa>"

definition cagg_member :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow>
    (('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd) \<Rightarrow>
    ('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> 'v option_pd" where
  "cagg_member X c Gs Xs F k \<kappa> = (if \<kappa> \<in> agg_definite X (hd Gs) F k then cagg_value X c Gs Xs F \<kappa>
     else cagg_value X c Gs Xs F \<kappa> + Absent)"

definition cagg_glb :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext \<Rightarrow>
    (('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd) \<Rightarrow>
    ('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd" where
  "cagg_glb f X c Gs Xs F k = glb {agg_fold f (cagg_member X c Gs Xs F k) (agg_definite X (hd Gs) F k \<union> C) | C.
     finite C \<and> C \<subseteq> agg_possible X (hd Gs) F k}"

text \<open>The aggregate's selected parts at the outer key are compact.\<close>

lemma agg_upper_compact:
  assumes k: "sel_compact (aggregate_ext f X) F k" and S: "S \<in> set (esels X)"
  shows "compact (proj (upper_part S \<sqinter> flod F)\<cdot>k)"
proof -
  have "sel \<bottom> (upper_part S) \<in> set (esels (aggregate_ext f X))" using S by (auto simp: image_iff)
  then have "compact (proj (sel_at (sel \<bottom> (upper_part S)) (flod F))\<cdot>k)" using k by blast
  then show ?thesis by (simp only: selector.select_convs lattice_join_bot_left)
qed

lemma agg_frame_compact:
  assumes k: "sel_compact (aggregate_ext f X) F k"
  shows "compact (proj (flod F)\<cdot>k)"
proof -
  have "sel \<bottom> \<top> \<in> set (esels (aggregate_ext f X))" by simp
  then have "compact (proj (sel_at (sel \<bottom> \<top>) (flod F))\<cdot>k)" using k by blast
  then show ?thesis by (simp only: selector.select_convs lattice_meet_top_left lattice_join_bot_left)
qed

text \<open>An inner key at the key LOD is compact: its part at the inner minimal LOD is, if that is
  small, and its part at the frame LOD is the outer key.\<close>

lemma inner_key_compact:
  assumes m: "lod_small (emind X)" and kK: "proj (kd X F)\<cdot>\<kappa> = \<kappa>" and ck: "compact (proj (flod F)\<cdot>\<kappa>)"
  shows "compact \<kappa>"
proof -
  have "compact (proj (emind X)\<cdot>\<kappa> \<squnion> proj (flod F)\<cdot>\<kappa>)"
    by (rule compact_join [OF lod_small_proj [OF m] ck joinableI [OF proj_below proj_below]])
  then show ?thesis by (simp only: proj_sup [symmetric] kK)
qed

lemma agg_inner_contents:
  assumes k: "sel_compact (aggregate_ext f X) F k" and kk: "proj (flod F)\<cdot>\<kappa> = k" and c: "compact \<kappa>"
  shows "agg_inner_g X F \<kappa> (gcontents_ext D (map release (eguards X)) F k) = gcontents_ext D (eguards X) F \<kappa>"
    and "agg_inner_v X \<kappa> (vcontents_ext D (map release (evalues X)) F k) = vcontents_ext D (evalues X) F \<kappa>"
proof -
  have cS: "compact (proj (sel_at (esel e) (flod F))\<cdot>\<kappa>)" for e :: "('k, 'p) entry"
    by (rule compact_proj_compact [OF c])
  show "agg_inner_g X F \<kappa> (gcontents_ext D (map release (eguards X)) F k) = gcontents_ext D (eguards X) F \<kappa>"
    unfolding agg_inner_g_def map_map comp_def map2_map
  proof (rule map_cong [OF refl])
    fix e assume e: "e \<in> set (eguards X)"
    show "sel_select (esel e) F \<kappa>\<cdot>(gcontent_ext D (release e) F k) = gcontent_ext D e F \<kappa>"
      unfolding sel_select_def
      by (rule inner_gcontent [OF kk cS agg_upper_compact [OF k esels_guardI [OF e]], symmetric])
  qed
  show "agg_inner_v X \<kappa> (vcontents_ext D (map release (evalues X)) F k) = vcontents_ext D (evalues X) F \<kappa>"
    unfolding agg_inner_v_def map_map comp_def map2_map
  proof (rule map_cong [OF refl])
    fix e assume e: "e \<in> set (evalues X)"
    show "split_view (eview e)\<cdot>(split_select (elower e) (proj (elower e)\<cdot>\<kappa>)\<cdot>(vcontent_ext D (release e) F k)) = vcontent_ext D e F \<kappa>"
      by (rule inner_vcontent [OF kk cS agg_upper_compact [OF k esels_valueI [OF e]], symmetric])
  qed
qed

text \<open>At an inner key, the aggregate's member value is the content one.\<close>

lemma agg_value_contents:
  assumes c: "ext_csem X c" and D: "conf_bounded D" and k: "sel_compact (aggregate_ext f X) F k"
    and kk: "proj (flod F)\<cdot>\<kappa> = k" and kK: "proj (kd X F)\<cdot>\<kappa> = \<kappa>" and c\<kappa>: "compact \<kappa>"
  shows "populated_ext D (emind X) \<top> F \<kappa> \<odot> sem_ext X D F \<kappa> =
    cagg_value X c (gcontents_ext D (eguards (aggregate_ext f X)) F k) (vcontents_ext D (evalues (aggregate_ext f X)) F k) F \<kappa>"
proof -
  have sk: "sel_compact X F \<kappa>" by (blast intro: compact_proj_compact [OF c\<kappa>])
  show ?thesis
    unfolding cagg_value_def aggregate_ext_simps aggregate_simps list.map list.sel
      agg_inner_contents [OF k kk c\<kappa>] inner_presence [OF kk kK c\<kappa>, symmetric] ext_csemD [OF c D sk] ..
qed

text \<open>The inner keys definite or possible at the outer key lie in the key LOD above the outer key.\<close>

lemma agg_keys_at:
  assumes "\<kappa> \<in> agg_definite X D F k \<union> agg_possible X D F k"
  shows "proj (flod F)\<cdot>\<kappa> = k \<and> proj (kd X F)\<cdot>\<kappa> = \<kappa> \<and> \<kappa> \<in> Rep_cfun (proj (kd X F)) ` conforming_keyspace"
  using assms unfolding agg_definite_def agg_possible_def by (auto simp: maximal_at_lives proj_idem)

lemma present_select_TT:
  assumes c: "compact \<kappa>" and p: "split_present (split_select K \<kappa>\<cdot>G) = TT"
  shows "\<exists>y. split_definite y G \<and> rproj K y = \<kappa>"
proof -
  have "select_test K \<kappa> (\<Lambda> _. TT) (\<Lambda> _. TT) G = TT" unfolding select_test_guarded [OF c] using p by simp
  then show ?thesis unfolding select_test_def by (auto split: if_split_asm)
qed

lemma present_select_FF:
  assumes c: "compact \<kappa>" and p: "\<not> split_possible_at K \<kappa> G"
  shows "split_present (split_select K \<kappa>\<cdot>G) = FF"
  using select_test_impossible [OF c p, where g = "\<Lambda> _. TT" and h = "\<Lambda> _. TT"] unfolding select_test_guarded [OF c] by simp

text \<open>At a compact dataset below a conforming one, the aggregate is the content aggregate of its
  contents.  The fold guard's content has fewer definite and possible inner keys than the dataset,
  but the missing ones do not change the greatest lower bound: a key definite in the dataset only
  is not present for sure, so its member is already below the unit; a key possible in the dataset
  only is refuted, so its member is the unit.\<close>

theorem agg_glb_contents:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and c: "ext_csem X c" and m: "lod_small (emind X)"
    and D: "conf_bounded D" and cD: "compact D" and k: "sel_compact (aggregate_ext f X) F k"
  shows "agg_glb f X D F k = cagg_glb f X c (gcontents_ext D (eguards (aggregate_ext f X)) F k)
    (vcontents_ext D (evalues (aggregate_ext f X)) F k) F k"
proof -
  let ?Gs = "gcontents_ext D (eguards (aggregate_ext f X)) F k" and ?Xs = "vcontents_ext D (evalues (aggregate_ext f X)) F k"
  let ?G = "gcontent_ext D (mk_guard (sel \<bottom> \<top>) gtrue gtrue (emind X)) F k" and ?K = "kd X F"
  have hG: "hd ?Gs = ?G" by simp
  let ?DefD = "agg_definite X D F k" and ?PosD = "agg_possible X D F k"
  let ?DefG = "agg_definite X ?G F k" and ?PosG = "agg_possible X ?G F k"
  let ?MD = "agg_member X D F k" and ?MG = "cagg_member X c ?Gs ?Xs F k"
  let ?p = "\<lambda>\<kappa>. split_present (split_select ?K \<kappa>\<cdot>?G)"
  have ck: "compact (proj (flod F)\<cdot>k)" by (rule agg_frame_compact [OF k])
  have key: "proj (flod F)\<cdot>\<kappa> = k" "proj ?K\<cdot>\<kappa> = \<kappa>" "\<kappa> \<in> Rep_cfun (proj ?K) ` conforming_keyspace" "compact \<kappa>"
    if "\<kappa> \<in> ?DefD \<union> ?PosD" for \<kappa>
  proof -
    show kk: "proj (flod F)\<cdot>\<kappa> = k" and kK: "proj ?K\<cdot>\<kappa> = \<kappa>" and "\<kappa> \<in> Rep_cfun (proj ?K) ` conforming_keyspace"
      using agg_keys_at [OF that] by simp_all
    have "compact (proj (flod F)\<cdot>\<kappa>)" using ck by (simp only: kk [symmetric] proj_idem)
    then show "compact \<kappa>" by (rule inner_key_compact [OF m kK])
  qed
  have defG: "?DefG \<subseteq> ?DefD" unfolding agg_definite_def using gcontent_definite by blast
  have posG: "?PosG \<subseteq> ?PosD" unfolding agg_possible_def using gcontent_possible by blast
  have val: "populated_ext D (emind X) \<top> F \<kappa> \<odot> sem_ext X D F \<kappa> = cagg_value X c ?Gs ?Xs F \<kappa>"
    if "\<kappa> \<in> ?DefD \<union> ?PosD" for \<kappa>
    by (rule agg_value_contents [OF c D k key(1,2,4) [OF that]])
  have pv: "cagg_value X c ?Gs ?Xs F \<kappa> = ?p \<kappa> \<odot> c (agg_inner_g X F \<kappa> (tl ?Gs)) (agg_inner_v X \<kappa> ?Xs) F \<kappa>" for \<kappa>
    unfolding cagg_value_def hG ..
  have nTT: "?p \<kappa> \<noteq> TT" if d: "\<kappa> \<in> ?DefD" and n: "\<kappa> \<notin> ?DefG" for \<kappa>
  proof
    assume T: "?p \<kappa> = TT"
    obtain y where y: "split_definite y ?G" "rproj ?K y = \<kappa>"
      using present_select_TT [OF key(4) [OF UnI1 [OF d]] T] by blast
    have "\<kappa> \<in> ?DefG" using d y unfolding agg_definite_def by blast
    then show False using n by blast
  qed
  have FF: "?p \<kappa> = FF" if "\<kappa> \<in> ?DefD \<union> ?PosD" "\<kappa> \<notin> ?PosG" for \<kappa>
  proof (rule present_select_FF [OF key(4) [OF that(1)]])
    show "\<not> split_possible_at ?K \<kappa> ?G" using that key(1,3) [OF that(1)] unfolding agg_possible_def by blast
  qed
  have mem: "?MD \<kappa> = ?MG \<kappa>" if "\<kappa> \<in> ?DefD \<union> ?PosD" for \<kappa>
  proof (cases "\<kappa> \<in> ?DefG")
    case True
    then show ?thesis using defG val [OF that] unfolding agg_member_def cagg_member_def hG by auto
  next
    case nG: False
    show ?thesis
    proof (cases "\<kappa> \<in> ?DefD")
      case True
      have "cagg_value X c ?Gs ?Xs F \<kappa> + Absent = cagg_value X c ?Gs ?Xs F \<kappa>"
        unfolding pv by (rule tr_mult_plus_Absent [OF nTT [OF True nG]])
      then show ?thesis using True nG val [OF that] unfolding agg_member_def cagg_member_def hG by simp
    next
      case False
      then show ?thesis using nG val [OF that] unfolding agg_member_def cagg_member_def hG by simp
    qed
  qed
  have absG: "?MG \<kappa> = Absent" if "\<kappa> \<in> ?DefD \<union> ?PosD" "\<kappa> \<notin> ?PosG" for \<kappa>
  proof -
    have "cagg_value X c ?Gs ?Xs F \<kappa> = Absent" unfolding pv FF [OF that] by simp
    then show ?thesis unfolding cagg_member_def by simp
  qed
  have lowG: "?MG \<kappa> \<sqsubseteq> Absent" if "\<kappa> \<notin> ?DefG" for \<kappa>
    using that unfolding cagg_member_def hG by (simp add: plus_option_pd_below2)
  have fD: "finite ?DefD" by (rule agg_definite_finite [OF cD])
  let ?SD = "{agg_fold f ?MD (?DefD \<union> C) | C. finite C \<and> C \<subseteq> ?PosD}"
  let ?SG = "{agg_fold f ?MG (?DefG \<union> C) | C. finite C \<and> C \<subseteq> ?PosG}"
  have SD: "agg_glb f X D F k = glb ?SD" unfolding agg_glb_def ..
  have SG: "cagg_glb f X c ?Gs ?Xs F k = glb ?SG" unfolding cagg_glb_def hG ..
  have "glb ?SD \<sqsubseteq> glb ?SG"
  proof (rule glb_greatest, blast, intro ballI)
    fix y assume "y \<in> ?SG"
    then obtain C where y: "y = agg_fold f ?MG (?DefG \<union> C)" and fC: "finite C" and C: "C \<subseteq> ?PosG" by blast
    have "glb ?SD \<sqsubseteq> agg_fold f ?MD (?DefD \<union> C)"
      by (rule glb_below, rule CollectI, rule exI [of _ C]) (use fC C posG in blast)
    also have "\<dots> = agg_fold f ?MG (?DefD \<union> C)" by (rule agg_fold_cong [OF f refl], rule mem) (use C posG in blast)
    also have "\<dots> \<sqsubseteq> y" unfolding y
      by (rule agg_fold_below_unit [OF f finite_UnI [OF fD fC]]) (use defG lowG in blast)+
    finally show "glb ?SD \<sqsubseteq> y" .
  qed
  moreover have "glb ?SG \<sqsubseteq> glb ?SD"
  proof (rule glb_greatest, blast, intro ballI)
    fix x assume "x \<in> ?SD"
    then obtain C' where x: "x = agg_fold f ?MD (?DefD \<union> C')" and fC': "finite C'" and C': "C' \<subseteq> ?PosD" by blast
    let ?C = "(?DefD \<union> C') \<inter> ?PosG"
    have "glb ?SG \<sqsubseteq> agg_fold f ?MG (?DefG \<union> ?C)"
      by (rule glb_below, rule CollectI, rule exI [of _ ?C]) (use fD fC' in auto)
    also have "\<dots> = agg_fold f ?MG (?DefD \<union> C')"
      by (rule agg_fold_neutral_left [OF f finite_UnI [OF fD fC']]) (use defG absG C' in blast)+
    also have "\<dots> = x" unfolding x by (rule agg_fold_cong [OF f refl], rule mem [symmetric]) (use C' in blast)
    finally show "glb ?SG \<sqsubseteq> x" .
  qed
  ultimately show ?thesis unfolding SD SG by (rule below_antisym)
qed


text \<open>The content aggregate is monotone on contents below those of a conforming dataset, where
  the fold guard's content is compact: then its definite inner keys are finitely many, and possible
  since they are compact.\<close>

lemma list_all2_map2_mono:
  assumes xy: "list_all2 (\<sqsubseteq>) xs ys" and g: "\<And>e x y. x \<sqsubseteq> y \<Longrightarrow> g e x \<sqsubseteq> g e y"
  shows "list_all2 (\<sqsubseteq>) (map2 g es xs) (map2 g es ys)"
  using xy
proof (induct arbitrary: es rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case by (cases es) (simp_all add: g)
qed

lemma agg_inner_g_mono: "list_all2 (\<sqsubseteq>) Gr Gr' \<Longrightarrow> list_all2 (\<sqsubseteq>) (agg_inner_g X F \<kappa> Gr) (agg_inner_g X F \<kappa> Gr')"
  unfolding agg_inner_g_def by (rule list_all2_map2_mono, assumption, rule monofun_cfun_arg)

lemma agg_inner_v_mono: "list_all2 (\<sqsubseteq>) Xr Xr' \<Longrightarrow> list_all2 (\<sqsubseteq>) (agg_inner_v X \<kappa> Xr) (agg_inner_v X \<kappa> Xr')"
  unfolding agg_inner_v_def by (rule list_all2_map2_mono, assumption, intro monofun_cfun_arg)

lemma cagg_value_mono:
  assumes c: "csem_mono X c" and cC: "conforming_rows (split_rows\<cdot>C)" and k: "sel_compact (aggregate_ext f X) F k"
    and kk: "proj (flod F)\<cdot>\<kappa> = k" and c\<kappa>: "compact \<kappa>"
    and G: "list_all2 (\<sqsubseteq>) Gs Gs'" and G': "list_all2 (\<sqsubseteq>) Gs' (gcontents_ext C (eguards (aggregate_ext f X)) F k)"
    and V: "list_all2 (\<sqsubseteq>) Xs Xs'" and V': "list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues (aggregate_ext f X)) F k)"
  shows "cagg_value X c Gs Xs F \<kappa> \<sqsubseteq> cagg_value X c Gs' Xs' F \<kappa>"
proof -
  obtain g' Gt' where g': "Gs' = g' # Gt'" and Gt': "list_all2 (\<sqsubseteq>) Gt' (gcontents_ext C (map release (eguards X)) F k)"
    using G' by (auto simp: list_all2_Cons2)
  obtain g Gt where g: "Gs = g # Gt" "g \<sqsubseteq> g'" and Gt: "list_all2 (\<sqsubseteq>) Gt Gt'" using G unfolding g' by (auto simp: list_all2_Cons2)
  have Vt': "list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (map release (evalues X)) F k)"
    using V' by (simp only: aggregate_ext_simps aggregate_simps)
  have sk: "sel_compact X F \<kappa>" by (blast intro: compact_proj_compact [OF c\<kappa>])
  have GI: "list_all2 (\<sqsubseteq>) (agg_inner_g X F \<kappa> Gt') (gcontents_ext C (eguards X) F \<kappa>)"
    using agg_inner_g_mono [OF Gt', of X F \<kappa>] unfolding agg_inner_contents(1) [OF k kk c\<kappa>] .
  have VI: "list_all2 (\<sqsubseteq>) (agg_inner_v X \<kappa> Xs') (vcontents_ext C (evalues X) F \<kappa>)"
    using agg_inner_v_mono [OF Vt', of X \<kappa>] unfolding agg_inner_contents(2) [OF k kk c\<kappa>] .
  have cc: "c (agg_inner_g X F \<kappa> Gt) (agg_inner_v X \<kappa> Xs) F \<kappa> \<sqsubseteq> c (agg_inner_g X F \<kappa> Gt') (agg_inner_v X \<kappa> Xs') F \<kappa>"
    by (rule csem_monoD [OF c cC sk agg_inner_g_mono [OF Gt] GI agg_inner_v_mono [OF V] VI])
  have pp: "split_present (split_select (kd X F) \<kappa>\<cdot>g) \<sqsubseteq> split_present (split_select (kd X F) \<kappa>\<cdot>g')"
    by (rule split_present_mono [OF monofun_cfun_arg [OF g(2)]])
  show ?thesis unfolding cagg_value_def g g' list.sel by (rule monofun_cfun [OF monofun_cfun_arg [OF pp] cc])
qed

theorem cagg_glb_mono:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and c: "csem_mono X c" and m: "lod_small (emind X)"
    and cC: "conforming_rows (split_rows\<cdot>C)" and k: "sel_compact (aggregate_ext f X) F k"
    and G: "list_all2 (\<sqsubseteq>) Gs Gs'" and G': "list_all2 (\<sqsubseteq>) Gs' (gcontents_ext C (eguards (aggregate_ext f X)) F k)"
    and V: "list_all2 (\<sqsubseteq>) Xs Xs'" and V': "list_all2 (\<sqsubseteq>) Xs' (vcontents_ext C (evalues (aggregate_ext f X)) F k)"
    and cG: "compact (hd Gs')"
  shows "cagg_glb f X c Gs Xs F k \<sqsubseteq> cagg_glb f X c Gs' Xs' F k"
proof -
  obtain g' Gt' where g': "Gs' = g' # Gt'" using G' by (auto simp: list_all2_Cons2)
  obtain g Gt where g: "Gs = g # Gt" "g \<sqsubseteq> g'" using G unfolding g' by (auto simp: list_all2_Cons2)
  have hG: "hd Gs = g" and hG': "hd Gs' = g'" unfolding g g' by simp_all
  let ?K = "kd X F"
  let ?Def = "agg_definite X g F k" and ?Def' = "agg_definite X g' F k"
  let ?Pos = "agg_possible X g F k" and ?Pos' = "agg_possible X g' F k"
  let ?M = "cagg_member X c Gs Xs F k" and ?M' = "cagg_member X c Gs' Xs' F k"
  let ?S = "{agg_fold f ?M (?Def \<union> C) | C. finite C \<and> C \<subseteq> ?Pos}"
  let ?S' = "{agg_fold f ?M' (?Def' \<union> C) | C. finite C \<and> C \<subseteq> ?Pos'}"
  have ck: "compact (proj (flod F)\<cdot>k)" by (rule agg_frame_compact [OF k])
  have key: "proj (flod F)\<cdot>\<kappa> = k" "compact \<kappa>" if "\<kappa> \<in> ?Def' \<union> ?Pos'" for \<kappa>
  proof -
    have kk: "proj (flod F)\<cdot>\<kappa> = k" and kK: "proj ?K\<cdot>\<kappa> = \<kappa>" using agg_keys_at [OF that] by simp_all
    show "proj (flod F)\<cdot>\<kappa> = k" by (rule kk)
    have "compact (proj (flod F)\<cdot>\<kappa>)" using ck by (simp only: kk [symmetric] proj_idem)
    then show "compact \<kappa>" by (rule inner_key_compact [OF m kK])
  qed
  have dm: "?Def \<subseteq> ?Def'" by (rule agg_definite_mono [OF g(2)])
  have pm: "?Pos' \<subseteq> ?Pos" by (rule agg_possible_mono [OF g(2)])
  have dp: "?Def' \<subseteq> ?Pos'"
  proof
    fix \<kappa> assume d: "\<kappa> \<in> ?Def'"
    then obtain y where mx: "maximal_at ?K \<kappa>" and kk: "proj (flod F)\<cdot>\<kappa> = k"
      and r: "\<kappa> \<in> Rep_cfun (proj ?K) ` conforming_keyspace"
      and y: "split_definite y g'" "rproj ?K y = \<kappa>" by (auto simp: agg_definite_def)
    have cy: "compact (rproj ?K y)" using key(2) [OF UnI1 [OF d]] y(2) by simp
    have "split_possible_at ?K \<kappa> g'" using definite_maximal_possible [OF y(1) cy] mx y(2) by simp
    then show "\<kappa> \<in> ?Pos'" unfolding agg_possible_def using kk r by blast
  qed
  have fD': "finite ?Def'" by (rule agg_definite_finite) (use cG g' in simp)
  have mem: "?M \<kappa> \<sqsubseteq> ?M' \<kappa>" if "\<kappa> \<in> ?Def' \<union> ?Pos'" for \<kappa>
  proof -
    have v: "cagg_value X c Gs Xs F \<kappa> \<sqsubseteq> cagg_value X c Gs' Xs' F \<kappa>"
      by (rule cagg_value_mono [OF c cC k key [OF that] G G' V V'])
    show ?thesis
    proof (cases "\<kappa> \<in> ?Def")
      case True
      then show ?thesis using v dm unfolding cagg_member_def hG hG' by auto
    next
      case nD: False
      have l: "cagg_value X c Gs Xs F \<kappa> + Absent \<sqsubseteq> cagg_value X c Gs' Xs' F \<kappa>"
        by (rule below_trans [OF plus_option_pd_below1 v])
      show ?thesis
      proof (cases "\<kappa> \<in> ?Def'")
        case True
        then show ?thesis using nD l unfolding cagg_member_def hG hG' by simp
      next
        case False
        then show ?thesis using nD unfolding cagg_member_def hG hG'
          by (simp add: plus_option_pd_greatest [OF l plus_option_pd_below2])
      qed
    qed
  qed
  have S: "cagg_glb f X c Gs Xs F k = glb ?S" unfolding cagg_glb_def g list.sel ..
  have S': "cagg_glb f X c Gs' Xs' F k = glb ?S'" unfolding cagg_glb_def g' list.sel ..
  have "glb ?S \<sqsubseteq> glb ?S'"
  proof (rule glb_greatest, blast, intro ballI)
    fix x assume "x \<in> ?S'"
    then obtain C' where x: "x = agg_fold f ?M' (?Def' \<union> C')" and fC': "finite C'" and C': "C' \<subseteq> ?Pos'" by blast
    let ?C'' = "(?Def' - ?Def) \<union> C'"
    have eq: "?Def \<union> ?C'' = ?Def' \<union> C'" using dm by blast
    have "glb ?S \<sqsubseteq> agg_fold f ?M (?Def \<union> ?C'')"
      by (rule glb_below, rule CollectI, rule exI [of _ ?C'']) (use fD' fC' C' dp pm in auto)
    also have "\<dots> = agg_fold f ?M (?Def' \<union> C')" by (simp only: eq)
    also have "\<dots> \<sqsubseteq> x" unfolding x
      by (rule agg_fold_mono [OF f finite_UnI [OF fD' fC']], rule mem) (use C' in blast)
    finally show "glb ?S \<sqsubseteq> x" .
  qed
  then show ?thesis unfolding S S' .
qed

end

end
