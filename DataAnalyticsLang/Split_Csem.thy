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

definition ext_csem :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow>
    (('r, 'k) split_pd list \<Rightarrow> ('r, 'k) split_pd list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd) \<Rightarrow> bool" where
  "ext_csem X c \<longleftrightarrow> (\<forall>D F k. sel_compact X F k \<longrightarrow>
     sem_ext X D F k = c (gcontents_ext D (eguards X) F k) (vcontents_ext D (evalues X) F k) F k)"

lemma ext_csemI:
  "(\<And>D F k. sel_compact X F k \<Longrightarrow> sem_ext X D F k = c (gcontents_ext D (eguards X) F k) (vcontents_ext D (evalues X) F k) F k) \<Longrightarrow>
     ext_csem X c"
  unfolding ext_csem_def by blast

lemma ext_csemD:
  "ext_csem X c \<Longrightarrow> sel_compact X F k \<Longrightarrow> sem_ext X D F k = c (gcontents_ext D (eguards X) F k) (vcontents_ext D (evalues X) F k) F k"
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
  assumes c: "ext_csem X c" and X: "semilawful X" and k: "sel_compact X F k"
  shows "sem_ext X D F (proj (kd X F)\<cdot>k) = c (gcontents_ext D (eguards X) F k) (vcontents_ext D (evalues X) F k) F (proj (kd X F)\<cdot>k)"
  using ext_csemD [OF c sel_compact_kd [OF X k]] by (simp only: contents_kd [OF X])


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
  by (rule ext_csemI) (simp add: ext_csemD)

theorem ext_csem_key_at: "ext_csem (key_at_ext c) (\<lambda>Gs Xs F k. split_present (hd Xs) \<odot> Present\<cdot>(proj c\<cdot>k))"
proof (rule ext_csemI)
  fix D F k assume comp: "sel_compact (key_at_ext c) F k"
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
  fix D F k assume c: "ext_csem X c" and comp: "sel_compact (restrict_ext \<gamma> X) F k"
  have comp': "sel_compact X (frestrict \<gamma> F) k" using comp by (simp add: comp_def)
  have g: "gcontents_ext D (eguards X) (frestrict \<gamma> F) k = gcontents_ext D (map (restrict_entry \<gamma>) (eguards X)) F k"
    by (simp add: gcontent_ext_def sel_select_def gand_assoc)
  have v: "vcontents_ext D (evalues X) (frestrict \<gamma> F) k = vcontents_ext D (evalues X) F k"
    by (simp add: vcontent_ext_def sel_select_def)
  show "sem_ext (restrict_ext \<gamma> X) D F k =
      c (gcontents_ext D (eguards (restrict_ext \<gamma> X)) F k) (vcontents_ext D (evalues (restrict_ext \<gamma> X)) F k) (frestrict \<gamma> F) k"
    using ext_csemD [OF c comp', of D] by (simp only: restrict_ext_simps restrict_simps g v)
qed

theorem ext_csem_present_at:
  assumes c: "ext_csem X c" and X: "semilawful X"
  shows "ext_csem (present_at_ext a \<rho> X)
    (\<lambda>Gs Xs F k. split_present (hd Gs) \<odot> c (tl Gs) Xs F (proj (kd X F)\<cdot>k))"
proof (rule ext_csemI)
  fix D F k assume comp: "sel_compact (present_at_ext a \<rho> X) F k"
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
    using ext_csemD_kd [OF c X compX, of D] by (simp add: p)
qed

theorem ext_csem_combine:
  assumes c\<^sub>1: "ext_csem X\<^sub>1 c\<^sub>1" and c\<^sub>2: "ext_csem X\<^sub>2 c\<^sub>2" and X\<^sub>1: "semilawful X\<^sub>1" and X\<^sub>2: "semilawful X\<^sub>2"
  shows "ext_csem (combine_ext f X\<^sub>1 X\<^sub>2) (\<lambda>Gs Xs F k. lift2_option_pd f\<cdot>
     (c\<^sub>1 (take (length (eguards X\<^sub>1)) Gs) (take (length (evalues X\<^sub>1)) Xs) F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>
     (c\<^sub>2 (drop (length (eguards X\<^sub>1)) Gs) (drop (length (evalues X\<^sub>1)) Xs) F (proj (kd X\<^sub>2 F)\<cdot>k)))"
proof (rule ext_csemI)
  fix D F k assume comp: "sel_compact (combine_ext f X\<^sub>1 X\<^sub>2) F k"
  have comp1: "sel_compact X\<^sub>1 F k" and comp2: "sel_compact X\<^sub>2 F k" using comp by auto
  show "sem_ext (combine_ext f X\<^sub>1 X\<^sub>2) D F k = lift2_option_pd f\<cdot>
     (c\<^sub>1 (take (length (eguards X\<^sub>1)) (gcontents_ext D (eguards (combine_ext f X\<^sub>1 X\<^sub>2)) F k))
        (take (length (evalues X\<^sub>1)) (vcontents_ext D (evalues (combine_ext f X\<^sub>1 X\<^sub>2)) F k)) F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>
     (c\<^sub>2 (drop (length (eguards X\<^sub>1)) (gcontents_ext D (eguards (combine_ext f X\<^sub>1 X\<^sub>2)) F k))
        (drop (length (evalues X\<^sub>1)) (vcontents_ext D (evalues (combine_ext f X\<^sub>1 X\<^sub>2)) F k)) F (proj (kd X\<^sub>2 F)\<cdot>k))"
    using ext_csemD_kd [OF c\<^sub>1 X\<^sub>1 comp1, of D] ext_csemD_kd [OF c\<^sub>2 X\<^sub>2 comp2, of D] by simp
qed

text \<open>A column reads the join of the sections of the selected definite rows, through its view.
  The rows of the viewed selection approximate the selected rows of the dataset and conversely, so
  both have the same upper bounds and the same join.\<close>

definition col_content_value :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> 'k \<Rightarrow> 'r" where
  "col_content_value c a X k = (if maximal_at a (proj a\<cdot>k) then lub {z \<downharpoonright> c | z. split_definite z X} else \<bottom>)"

lemma lub_same_ubs: "(\<And>u. S <| u \<longleftrightarrow> T <| u) \<Longrightarrow> lub S = lub T"
  unfolding lub_def is_lub_def by simp

lemma col_value_content:
  assumes kc: "compact (proj a\<cdot>k)"
  shows "col_value c a D k = col_content_value c a (split_view (c, a)\<cdot>(split_select a (proj a\<cdot>k)\<cdot>D)) k"
proof (cases "maximal_at a (proj a\<cdot>k)")
  case False
  then show ?thesis by (simp add: col_value_def col_content_value_def)
next
  case mx: True
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
  have "lub ?A = lub ?B" by (rule lub_same_ubs) (blast intro: ub [OF BA] ub [OF AB])
  then show ?thesis by (simp add: col_value_def col_content_value_def mx)
qed

theorem ext_csem_column:
  "ext_csem (column_ext c a v)
     (\<lambda>Gs Xs F k. split_present (hd Xs) \<odot> Present\<cdot>(v\<cdot>(col_content_value c a (hd Xs) k)))"
proof (rule ext_csemI)
  fix D F k assume comp: "sel_compact (column_ext c a v) F k"
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
  fix D F k assume c: "ext_csem X c" and comp: "sel_compact (include_dims_ext M X) F k"
  have comp': "sel_compact X (finclude M F) k"
  proof
    fix S assume "S \<in> set (esels X)"
    then have "include_sel M S \<in> set (esels (include_dims_ext M X))" by (auto simp: comp_def)
    then have "compact (proj (sel_at (include_sel M S) (flod F))\<cdot>k)" using comp by blast
    then show "compact (proj (sel_at S (flod (finclude M F)))\<cdot>k)" by (simp only: include_lod)
  qed
  show "sem_ext (include_dims_ext M X) D F k =
      c (gcontents_ext D (eguards (include_dims_ext M X)) F k) (vcontents_ext D (evalues (include_dims_ext M X)) F k) (finclude M F) k"
    using ext_csemD [OF c comp', of D] by (simp add: gcontent_ext_include vcontent_ext_include comp_def)
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
  fix D F k assume comp: "sel_compact (filtfor_ext \<tau> G X) F k"
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
    using ext_csemD [OF c comp', of D] by (simp only: filtfor_ext_simps filtfor_simps g v)
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

end

end
