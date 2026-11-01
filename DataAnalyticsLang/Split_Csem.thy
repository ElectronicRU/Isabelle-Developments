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

end

end
