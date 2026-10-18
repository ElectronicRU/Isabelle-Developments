theory Expr_Combinators
  imports Content_Law
begin

section \<open>Combinators\<close>

text \<open>Each combinator transforms the entries of its inner expressions' dims along with their
  semantics, and is lawful on lawful inner expressions.  Collecting a list of expressions into a
  tuple, followed by a map, expresses every operator of any arity.\<close>

subsection \<open>Tuples\<close>

text \<open>A collected entry is present where every component is; its value is a tuple that is lazy in
  the components, so an undefined component does not make the tuple undefined.  No order classes
  are needed for values; they will be once tuples are key values.\<close>

domain ('a::"domain") ltuple = LNil | LCons (lazy "'a") "'a ltuple"

fun ltuple_of :: "'a::domain list \<Rightarrow> 'a ltuple" where
  "ltuple_of [] = LNil"
| "ltuple_of (x # xs) = LCons\<cdot>x\<cdot>(ltuple_of xs)"

lemma ltuple_of_not_bottom: "ltuple_of xs \<noteq> \<bottom>"
  by (induct xs) simp_all

lemma those_not_None_iff: "those xs \<noteq> None \<longleftrightarrow> (\<forall>x\<in>set xs. x \<noteq> None)"
  by (induct xs) (auto split: option.splits)

context dataspace
begin

subsection \<open>Values\<close>

text \<open>A function of the key at an LOD \<open>c\<close>, at the frame's data keys.  It reads the key part
  \<open>c\<close> of the key's own group.\<close>

definition value_at :: "'k semi_factor \<Rightarrow> ('k \<rightarrow> 'v::cpo) \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "value_at c g = \<lparr>emind = c, edims = [(c, lattice_top, obs_key c)],
     esem = \<lambda>F k. if keyimg S F (c \<squnion> flod F) k then Some (g\<cdot>(proj c\<cdot>k)) else None\<rparr>"

lemma value_at_simps [simp]:
  "emind (value_at c g) = c" "edims (value_at c g) = [(c, lattice_top, obs_key c)]"
  "esem (value_at c g) F k = (if keyimg S F (c \<squnion> flod F) k then Some (g\<cdot>(proj c\<cdot>k)) else None)"
  by (simp_all add: value_at_def)

lemma content_key_top:
  assumes k: "proj (c \<squnion> flod G)\<cdot>k = k"
  shows "content (c, lattice_top, obs_key c) G k
    = (if keyimg S G (c \<squnion> flod G) k then {emb\<cdot>(proj c\<cdot>k)} else {})"
proof -
  have v: "rproj c y = proj c\<cdot>k" if "rproj (c \<squnion> flod G) y = k" for y
    using proj_le[OF lattice_join_ge1, of c "flod G" "rkey\<cdot>y"] that by simp
  show ?thesis
    by (auto simp: keyimg_group_top[OF k] group_top[OF k] obs_key_apply v image_iff)
qed

theorem lawful_value_at: "lawfulE (value_at c g)"
proof (rule lawfulI, simp_all only: value_at_simps)
  show "truncate \<rho> c \<sqsubseteq> a" if "(a, \<rho>, f) \<in> set [(c, lattice_top, obs_key c)]" for a \<rho> f
    using that by (simp add: truncate_top)
  show "c = fold (\<squnion>) (map fst [(c, lattice_top, obs_key c)]) \<bottom>" by (simp add: lattice_join_bot_right)
  show "keyimg S F (c \<squnion> flod F) k"
    if "(if keyimg S F (c \<squnion> flod F) k then Some (g\<cdot>(proj c\<cdot>k)) else None) \<noteq> None" for F k
    using that by (simp split: if_splits)
  show "(if keyimg S F (c \<squnion> flod F) k then Some (g\<cdot>(proj c\<cdot>k)) else None)
      = (if keyimg S F' (c \<squnion> flod F') k' then Some (g\<cdot>(proj c\<cdot>k')) else None)"
    if k: "proj (c \<squnion> flod F)\<cdot>k = k" "proj (c \<squnion> flod F')\<cdot>k' = k'"
      and e: "contents [(c, lattice_top, obs_key c)] F k = contents [(c, lattice_top, obs_key c)] F' k'"
    for F F' k k'
  proof -
    have e1: "content (c, lattice_top, obs_key c) F k = content (c, lattice_top, obs_key c) F' k'"
      using e by (simp only: list.map list.inject)
    have e2: "(if keyimg S F (c \<squnion> flod F) k then {emb\<cdot>(proj c\<cdot>k)} else {})
        = (if keyimg S F' (c \<squnion> flod F') k' then {emb\<cdot>(proj c\<cdot>k')} else {})"
      using e1 by (simp only: content_key_top[OF k(1)] content_key_top[OF k(2)])
    show ?thesis
    proof (cases "keyimg S F (c \<squnion> flod F) k")
      case True
      then have F': "keyimg S F' (c \<squnion> flod F') k'" and "emb\<cdot>(proj c\<cdot>k) = emb\<cdot>(proj c\<cdot>k')"
        using e2 by (simp_all split: if_splits)
      then have "proj c\<cdot>k = proj c\<cdot>k'" by (blast intro: emb_inj)
      then show ?thesis using True F' by simp
    next
      case False
      then have "\<not> keyimg S F' (c \<squnion> flod F') k'" using e2 by (simp split: if_splits)
      then show ?thesis using False by simp
    qed
  qed
qed

subsection \<open>Maps\<close>

definition smap :: "('v::cpo \<rightarrow> 'w::cpo) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'w) expr" where
  "smap g E = \<lparr>emind = emind E, edims = edims E, esem = \<lambda>F k. map_option (Rep_cfun g) (esem E F k)\<rparr>"

lemma smap_simps [simp]:
  "emind (smap g E) = emind E" "edims (smap g E) = edims E"
  "esem (smap g E) F k = map_option (Rep_cfun g) (esem E F k)"
  by (simp_all add: smap_def)

theorem lawful_smap: assumes "lawfulE E" shows "lawfulE (smap g E)"
proof -
  interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S "emind E" "edims E" "esem E"
    by (fact assms)
  show ?thesis
  proof (rule lawfulI, simp_all only: smap_simps)
    show "truncate \<rho> (emind E) \<sqsubseteq> a" if "(a, \<rho>, f) \<in> set (edims E)" for a \<rho> f
      by (rule E.saturated[OF that])
    show "emind E = fold (\<squnion>) (map fst (edims E)) \<bottom>" by (rule E.mind_lub)
    show "map_option (Rep_cfun g) (esem E F k) = map_option (Rep_cfun g) (esem E F' k')"
      if "proj (emind E \<squnion> flod F)\<cdot>k = k" "proj (emind E \<squnion> flod F')\<cdot>k' = k'"
        "contents (edims E) F k = contents (edims E) F' k'" for F F' k k'
      by (simp only: E.content_law[OF that])
    show "keyimg S F (emind E \<squnion> flod F) k" if "map_option (Rep_cfun g) (esem E F k) \<noteq> None" for F k
      using that by (intro E.key_law) simp
  qed
qed

subsection \<open>\<open>RESTRICT\<close>\<close>

text \<open>Restricting conjoins a slicer to the ambient filter, on the rows' keys: inner groups are the
  outer groups' rows passing it, so each entry is tupled with whether a row passes.\<close>

abbreviation frestrict_key :: "'f \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> ('k semi_factor, 'f, 'r) frame" where
  "frestrict_key G \<equiv> frestrict (sel_vimage rkey (sopen G))"

definition restrict :: "'f \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "restrict G E = \<lparr>emind = emind E,
     edims = map (\<lambda>(a, \<rho>, f). (a, \<rho>, obs_pair f (obs_holds G))) (edims E),
     esem = \<lambda>F. esem E (frestrict_key G F)\<rparr>"

lemma restrict_simps [simp]:
  "emind (restrict G E) = emind E"
  "edims (restrict G E) = map (\<lambda>(a, \<rho>, f). (a, \<rho>, obs_pair f (obs_holds G))) (edims E)"
  "esem (restrict G E) F = esem E (frestrict_key G F)"
  by (simp_all add: restrict_def)

lemma group_frestrict_key:
  "group a \<rho> (frestrict_key G F) k = {y \<in> group a \<rho> F k. holds G (rkey\<cdot>y)}"
  by (auto simp: group_def holds_def)

lemma content_frestrict_key:
  "content (a, \<rho>, f) (frestrict_key G F) k = sel_snd (emb\<cdot>TT) (content (a, \<rho>, obs_pair f (obs_holds G)) F k)"
  by (simp add: sel_snd_obs_pair obs_holds_TT group_frestrict_key)

theorem lawful_restrict: assumes "lawfulE E" shows "lawfulE (restrict G E)"
proof -
  interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S "emind E" "edims E" "esem E"
    by (fact assms)
  let ?t = "\<lambda>(a, \<rho>, f). (a, \<rho>, obs_pair f (obs_holds G))"
  show ?thesis
  proof (rule lawfulI, simp_all only: restrict_simps)
    show "truncate \<rho> (emind E) \<sqsubseteq> a" if "(a, \<rho>, f) \<in> set (map ?t (edims E))" for a \<rho> f
      using that by (auto intro: E.saturated)
    show "emind E = fold (\<squnion>) (map fst (map ?t (edims E))) \<bottom>"
      using map_fst_tuple[of "\<lambda>\<rho>. \<rho>" "\<lambda>\<rho> f. obs_pair f (obs_holds G)" "edims E"]
      by (simp only: E.mind_lub[symmetric])
    show "esem E (frestrict_key G F) k = esem E (frestrict_key G F') k'"
      if k: "proj (emind E \<squnion> flod F)\<cdot>k = k" "proj (emind E \<squnion> flod F')\<cdot>k' = k'"
        and e: "contents (map ?t (edims E)) F k = contents (map ?t (edims E)) F' k'" for F F' k k'
    proof (rule E.content_law)
      show "proj (emind E \<squnion> flod (frestrict_key G F))\<cdot>k = k" using k(1) by simp
      show "proj (emind E \<squnion> flod (frestrict_key G F'))\<cdot>k' = k'" using k(2) by simp
      have inner: "contents (edims E) (frestrict_key G H) \<kappa>
          = map (sel_snd (emb\<cdot>TT)) (contents (map ?t (edims E)) H \<kappa>)" for H \<kappa>
        by (auto simp: content_def content_frestrict_key[simplified] split: prod.splits)
      show "contents (edims E) (frestrict_key G F) k = contents (edims E) (frestrict_key G F') k'"
        by (simp only: inner e)
    qed
    show "keyimg S F (emind E \<squnion> flod F) k" if "esem E (frestrict_key G F) k \<noteq> None" for F k
    proof -
      have "keyimg S (frestrict_key G F) (emind E \<squnion> flod F) k"
        using E.key_law[OF that] by simp
      then show ?thesis by (rule keyimg_mono[rotated]) (simp add: frows_frestrict)
    qed
  qed
qed

subsection \<open>\<open>FOR\<close> and \<open>FIXED\<close>\<close>

text \<open>\<open>E FOR \<tau> G\<close>: the inner expression under the frame with LOD and slice truncated to \<open>\<tau>\<close>
  and \<open>G\<close> conjoined, at the truncated key, guarded by the incoming key's own group.  Its upper
  parts meet \<open>\<tau>\<close>; each entry is tupled with whether a row passes \<open>G\<close> coarsened to the entry's
  upper part; the guard reads the own group.  \<open>FIXED D\<close> is \<open>FOR D\<close> without a filter.\<close>

definition filtfor :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "filtfor \<tau> G E = \<lparr>emind = emind E,
     edims = (emind E, lattice_top, \<bottom>) #
       map (\<lambda>(a, \<rho>, f). (a, \<rho> \<sqinter> \<tau>, obs_pair f (obs_holds (coarsen \<rho> G)))) (edims E),
     esem = \<lambda>F k. if keyimg S F (emind E \<squnion> flod F) k
       then esem E (ffor \<tau> G F) (proj (emind E \<squnion> flod (ffor \<tau> G F))\<cdot>k) else None\<rparr>"

abbreviation fixed :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "fixed D \<equiv> filtfor D \<^bold>1"

lemma filtfor_simps [simp]:
  "emind (filtfor \<tau> G E) = emind E"
  "edims (filtfor \<tau> G E) = (emind E, lattice_top, \<bottom>) #
       map (\<lambda>(a, \<rho>, f). (a, \<rho> \<sqinter> \<tau>, obs_pair f (obs_holds (coarsen \<rho> G)))) (edims E)"
  "esem (filtfor \<tau> G E) F k = (if keyimg S F (emind E \<squnion> flod F) k
       then esem E (ffor \<tau> G F) (proj (emind E \<squnion> flod (ffor \<tau> G F))\<cdot>k) else None)"
  by (simp_all add: filtfor_def)

text \<open>Inside the truncated frame, at the truncated key, a group is the outer group through the
  composite mask, cut down by the filter coarsened to the inner upper part.\<close>

lemma group_ffor:
  assumes am: "a \<sqsubseteq> m"
  shows "group a \<rho> (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k)
       = {y \<in> group a (\<rho> \<sqinter> \<tau>) F k. holds (coarsen \<rho> G) (rkey\<cdot>y)}"
proof -
  let ?X = "a \<squnion> truncate (\<rho> \<sqinter> \<tau>) (flod F)"
  have lod: "a \<squnion> truncate \<rho> (flod (ffor \<tau> G F)) = ?X" by (simp add: truncate_inf_comp)
  have le: "?X \<sqsubseteq> m \<squnion> flod (ffor \<tau> G F)"
    unfolding flod_ffor truncate_inf_comp by (rule lattice_join_mono[OF am truncate_below])
  have key: "proj ?X\<cdot>(proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = proj ?X\<cdot>k" by (rule proj_le[OF le])
  have sl: "holds (coarsen \<rho> (slice (ffor \<tau> G F))) k' \<longleftrightarrow>
      holds (coarsen (\<rho> \<sqinter> \<tau>) (slice F)) k' \<and> holds (coarsen \<rho> G) k'" for k'
    by (simp add: coarsen_conj coarsen_coarsen)
  show ?thesis unfolding group_def lod key sl by auto
qed

lemma content_ffor:
  assumes "a \<sqsubseteq> m"
  shows "content (a, \<rho>, f) (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k)
       = sel_snd (emb\<cdot>TT) (content (a, \<rho> \<sqinter> \<tau>, obs_pair f (obs_holds (coarsen \<rho> G))) F k)"
  by (simp only: content_simp group_ffor[OF assms]) (simp add: sel_snd_obs_pair obs_holds_TT)

lemma content_const_top:
  assumes "proj (c \<squnion> flod F)\<cdot>k = k"
  shows "content (c, lattice_top, \<bottom>) F k = (if keyimg S F (c \<squnion> flod F) k then {\<bottom>} else {})"
  by (auto simp: keyimg_group_top[OF assms])

theorem lawful_filtfor: assumes "lawfulE E" shows "lawfulE (filtfor \<tau> G E)"
proof -
  interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S "emind E" "edims E" "esem E"
    by (fact assms)
  let ?m = "emind E"
  let ?t = "\<lambda>(a, \<rho>, f). (a, \<rho> \<sqinter> \<tau>, obs_pair f (obs_holds (coarsen \<rho> G)))"
  have inner: "contents (edims E) (ffor \<tau> G H) (proj (?m \<squnion> flod (ffor \<tau> G H))\<cdot>\<kappa>)
      = map (sel_snd (emb\<cdot>TT)) (contents (map ?t (edims E)) H \<kappa>)" for H \<kappa>
  proof -
    have "content e (ffor \<tau> G H) (proj (?m \<squnion> flod (ffor \<tau> G H))\<cdot>\<kappa>) = sel_snd (emb\<cdot>TT) (content (?t e) H \<kappa>)"
      if e: "e \<in> set (edims E)" for e
    proof -
      obtain a \<rho> f where ae: "e = (a, \<rho>, f)" by (cases e) auto
      show ?thesis unfolding ae
        by (simp only: content_ffor[OF E.lower_below_mind[OF e[unfolded ae]]] prod.case)
    qed
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule lawfulI, simp_all only: filtfor_simps)
    show "truncate \<rho> ?m \<sqsubseteq> a" if "(a, \<rho>, f) \<in> set ((?m, lattice_top, \<bottom>) # map ?t (edims E))" for a \<rho> f
    proof -
      from that consider "a = ?m" "\<rho> = lattice_top" | \<rho>0 f0 where "(a, \<rho>0, f0) \<in> set (edims E)" "\<rho> = \<rho>0 \<sqinter> \<tau>"
        by auto
      then show ?thesis
      proof cases
        case 1 then show ?thesis by (simp add: truncate_top)
      next
        case 2
        have "truncate \<rho> ?m = truncate \<rho>0 (truncate \<tau> ?m)" by (simp add: 2(2) truncate_inf_comp)
        also have "\<dots> \<sqsubseteq> truncate \<rho>0 ?m" by (rule truncate_mono[OF truncate_below])
        also have "\<dots> \<sqsubseteq> a" by (rule E.saturated[OF 2(1)])
        finally show ?thesis .
      qed
    qed
    show "?m = fold (\<squnion>) (map fst ((?m, lattice_top, \<bottom>) # map ?t (edims E))) \<bottom>"
    proof -
      have a: "fold (\<squnion>) (map fst (edims E)) ?m = ?m"
        by (rule fold_join_absorb) (auto intro: E.lower_below_mind)
      have mf: "map fst (map ?t (edims E)) = map fst (edims E)" by (rule map_fst_tuple)
      show ?thesis
        by (simp only: list.map(2) mf fst_conv fold.simps(2) comp_apply a lattice_join_bot_right)
    qed
    show "keyimg S F (?m \<squnion> flod F) k"
      if "(if keyimg S F (?m \<squnion> flod F) k
          then esem E (ffor \<tau> G F) (proj (?m \<squnion> flod (ffor \<tau> G F))\<cdot>k) else None) \<noteq> None" for F k
      using that by (simp split: if_splits)
    show "(if keyimg S F (?m \<squnion> flod F) k
          then esem E (ffor \<tau> G F) (proj (?m \<squnion> flod (ffor \<tau> G F))\<cdot>k) else None)
        = (if keyimg S F' (?m \<squnion> flod F') k'
          then esem E (ffor \<tau> G F') (proj (?m \<squnion> flod (ffor \<tau> G F'))\<cdot>k') else None)"
      if k: "proj (?m \<squnion> flod F)\<cdot>k = k" "proj (?m \<squnion> flod F')\<cdot>k' = k'"
        and e: "contents ((?m, lattice_top, \<bottom>) # map ?t (edims E)) F k
              = contents ((?m, lattice_top, \<bottom>) # map ?t (edims E)) F' k'" for F F' k k'
    proof -
      have eh: "content (?m, lattice_top, \<bottom>) F k = content (?m, lattice_top, \<bottom>) F' k'"
        and et: "contents (map ?t (edims E)) F k = contents (map ?t (edims E)) F' k'"
        using e by (simp_all only: list.map list.inject)
      have g: "keyimg S F (?m \<squnion> flod F) k \<longleftrightarrow> keyimg S F' (?m \<squnion> flod F') k'"
        using eh by (simp only: content_const_top[OF k(1)] content_const_top[OF k(2)]) (simp split: if_splits)
      have v: "esem E (ffor \<tau> G F) (proj (?m \<squnion> flod (ffor \<tau> G F))\<cdot>k)
          = esem E (ffor \<tau> G F') (proj (?m \<squnion> flod (ffor \<tau> G F'))\<cdot>k')"
        by (rule E.content_law) (simp_all only: proj_idem inner et)
      show ?thesis using g v by simp
    qed
  qed
qed


subsection \<open>Collect\<close>

text \<open>The components are evaluated under the frame extended by all their minimal LODs, so their
  values correspond to the full key; another component's minimal LOD enters a component's entries
  only through their lower parts.\<close>

definition collect_shift :: "'k semi_factor \<Rightarrow> ('k, 'r) entry \<Rightarrow> ('k, 'r) entry" where
  "collect_shift M e = (case e of (a, \<rho>, f) \<Rightarrow> (a \<squnion> truncate \<rho> M, \<rho>, f))"

definition collect :: "('k, 'f, 'r, 'a::domain) expr list \<Rightarrow> ('k, 'f, 'r, 'a ltuple) expr" where
  "collect Es = (let M = fold (\<squnion>) (map emind Es) \<bottom> in
     \<lparr>emind = M, edims = concat (map (\<lambda>E. map (collect_shift M) (edims E)) Es),
      esem = \<lambda>F k. map_option ltuple_of (those (map (\<lambda>E. esem E (finclude M F) k) Es))\<rparr>)"

lemma collect_simps:
  "emind (collect Es) = fold (\<squnion>) (map emind Es) \<bottom>"
  "edims (collect Es) = concat (map (\<lambda>E. map (collect_shift (emind (collect Es))) (edims E)) Es)"
  "esem (collect Es) F k
     = map_option ltuple_of (those (map (\<lambda>E. esem E (finclude (emind (collect Es)) F) k) Es))"
  by (simp_all add: collect_def Let_def)

lemma content_collect_shift: "content (collect_shift M e) F k = content e (finclude M F) k"
proof (cases e)
  case (fields a \<rho> f)
  have lod: "(a \<squnion> truncate \<rho> M) \<squnion> truncate \<rho> (flod F) = a \<squnion> truncate \<rho> (flod (finclude M F))"
    by (simp add: truncate_sup lattice_join_ac)
  have "group (a \<squnion> truncate \<rho> M) \<rho> F k = group a \<rho> (finclude M F) k"
    by (rule group_cong) (simp_all only: amb_finclude slice_finclude lod)
  then show ?thesis by (simp add: fields collect_shift_def)
qed

theorem lawful_collect:
  assumes ne: "Es \<noteq> []" and law: "\<And>E. E \<in> set Es \<Longrightarrow> lawfulE E"
  shows "lawfulE (collect Es)"
proof -
  let ?M = "fold (\<squnion>) (map emind Es) \<bottom>"
  have mE: "emind E \<sqsubseteq> ?M" if "E \<in> set Es" for E
    by (rule fold_join_upper) (simp add: that)
  have kd: "emind E \<squnion> flod (finclude ?M F) = ?M \<squnion> flod F" if "E \<in> set Es" for E F
  proof -
    have "emind E \<squnion> (flod F \<squnion> ?M) = (emind E \<squnion> ?M) \<squnion> flod F" by (simp only: lattice_join_ac)
    also have "emind E \<squnion> ?M = ?M" by (rule lattice_join_absorb2[OF mE[OF that]])
    finally show ?thesis by simp
  qed
  have M: "emind (collect Es) = ?M" by (simp add: collect_simps)
  show ?thesis
  proof (rule lawfulI, simp_all only: collect_simps M)
    show "truncate \<rho> ?M \<sqsubseteq> a"
      if "(a, \<rho>, f) \<in> set (concat (map (\<lambda>E. map (collect_shift ?M) (edims E)) Es))" for a \<rho> f
      using that by (auto simp: collect_shift_def split: prod.splits intro: lattice_join_ge2)
    show "?M = fold (\<squnion>) (map fst (concat (map (\<lambda>E. map (collect_shift ?M) (edims E)) Es))) \<bottom>"
    proof (rule below_antisym)
      let ?R = "fold (\<squnion>) (map fst (concat (map (\<lambda>E. map (collect_shift ?M) (edims E)) Es))) \<bottom>"
      show "?M \<sqsubseteq> ?R"
      proof (rule fold_join_least)
        fix x assume "x \<in> set (map emind Es)"
        then obtain E where E: "E \<in> set Es" and x: "x = emind E" by auto
        interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S "emind E" "edims E" "esem E"
          by (rule law[OF E])
        show "x \<sqsubseteq> ?R" unfolding x E.mind_lub
        proof (rule fold_join_least)
          fix a assume "a \<in> set (map fst (edims E))"
          then obtain \<rho> f where e: "(a, \<rho>, f) \<in> set (edims E)" by auto
          have "a \<sqsubseteq> a \<squnion> truncate \<rho> ?M" by (rule lattice_join_ge1)
          also have "\<dots> \<sqsubseteq> ?R"
            by (rule fold_join_upper) (use E e in \<open>force simp: collect_shift_def\<close>)
          finally show "a \<sqsubseteq> ?R" .
        qed simp
      qed simp
      show "?R \<sqsubseteq> ?M"
      proof (rule fold_join_least)
        fix x assume "x \<in> set (map fst (concat (map (\<lambda>E. map (collect_shift ?M) (edims E)) Es)))"
        then obtain E a \<rho> f where E: "E \<in> set Es" and e: "(a, \<rho>, f) \<in> set (edims E)"
          and x: "x = a \<squnion> truncate \<rho> ?M" by (auto simp: collect_shift_def split: prod.splits)
        interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S "emind E" "edims E" "esem E"
          by (rule law[OF E])
        have "a \<sqsubseteq> ?M" by (rule below_trans[OF E.lower_below_mind[OF e] mE[OF E]])
        then show "x \<sqsubseteq> ?M" unfolding x by (rule lattice_join_least[OF _ truncate_below])
      qed simp
    qed
    show "map_option ltuple_of (those (map (\<lambda>E. esem E (finclude ?M F) k) Es))
        = map_option ltuple_of (those (map (\<lambda>E. esem E (finclude ?M F') k') Es))"
      if k: "proj (?M \<squnion> flod F)\<cdot>k = k" "proj (?M \<squnion> flod F')\<cdot>k' = k'"
        and e: "contents (concat (map (\<lambda>E. map (collect_shift ?M) (edims E)) Es)) F k
              = contents (concat (map (\<lambda>E. map (collect_shift ?M) (edims E)) Es)) F' k'" for F F' k k'
    proof -
      have c: "contents (concat (map (\<lambda>E. map (collect_shift ?M) (edims E)) Es)) G \<kappa>
          = concat (map (\<lambda>E. contents (edims E) (finclude ?M G) \<kappa>) Es)" for G \<kappa>
        by (simp add: map_concat map_map comp_def content_collect_shift)
      have blocks: "contents (edims E) (finclude ?M F) k = contents (edims E) (finclude ?M F') k'"
        if E: "E \<in> set Es" for E
        by (rule concat_map_blocks[where xs = Es, OF e[unfolded c c] _ E]) simp
      have "esem E (finclude ?M F) k = esem E (finclude ?M F') k'" if E: "E \<in> set Es" for E
      proof -
        interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S "emind E" "edims E" "esem E"
          by (rule law[OF E])
        show ?thesis by (rule E.content_law[OF _ _ blocks[OF E]]) (simp_all only: kd[OF E] k)
      qed
      then show ?thesis by (simp cong: map_cong)
    qed
    show "keyimg S F (?M \<squnion> flod F) k"
      if "map_option ltuple_of (those (map (\<lambda>E. esem E (finclude ?M F) k) Es)) \<noteq> None" for F k
    proof -
      obtain E0 where E0: "E0 \<in> set Es" using ne by (cases Es) auto
      interpret E0: expr_sem conj sunit slod sopen coarsen spin rkey S "emind E0" "edims E0" "esem E0"
        by (rule law[OF E0])
      have "esem E0 (finclude ?M F) k \<noteq> None"
        using that E0 by (auto simp: those_not_None_iff simp del: not_None_eq)
      then have "keyimg S (finclude ?M F) (emind E0 \<squnion> flod (finclude ?M F)) k" by (rule E0.key_law)
      then show ?thesis by (simp only: kd[OF E0] keyimg_cong[OF frows_finclude])
    qed
  qed
qed

end

end
