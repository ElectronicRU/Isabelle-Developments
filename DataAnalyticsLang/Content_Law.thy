theory Content_Law
  imports Frame
begin

section \<open>The content law\<close>

text \<open>An expression reads its data through a finite list of \<^emph>\<open>generalized tables\<close>: an entry
  \<open>(a, \<rho>, f)\<close> groups the rows of the frame whose key agrees with the key at hand at
  \<open>a \<squnion> \<rho> \<sqinter> L\<close>, for the frame LOD \<open>L\<close>, among the rows passing the ambient filter and the slice
  coarsened to \<open>\<rho>\<close>, and records the set of values of the observation \<open>f\<close> on that group.  The
  \<^emph>\<open>content law\<close> says that the semantics at a key is determined by these contents: equal
  contents give equal entries, present or missing.\<close>

subsection \<open>Observations\<close>

text \<open>Observations are continuous maps from rows into the universal domain.  A selection reads as
  a continuous truth value; selections pull back along continuous maps.\<close>

definition sel_chi :: "'r::pcpo sel \<Rightarrow> 'r \<rightarrow> tr" where
  "sel_chi P = (\<Lambda> x. if selects P x then TT else \<bottom>)"

lemma cont_sel_chi: "cont (\<lambda>x. if selects P x then TT else (\<bottom>::tr))"
proof (rule contI2)
  show m: "monofun (\<lambda>x. if selects P x then TT else (\<bottom>::tr))"
    by (rule monofunI) (auto dest: selects_up)
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y"
  have ch: "chain (\<lambda>i. if selects P (Y i) then TT else (\<bottom>::tr))"
    by (rule ch2ch_monofun[OF m Y])
  show "(if selects P (\<Squnion>i. Y i) then TT else \<bottom>) \<sqsubseteq> (\<Squnion>i. if selects P (Y i) then TT else (\<bottom>::tr))"
  proof (cases "\<exists>i. selects P (Y i)")
    case True
    then obtain i where i: "selects P (Y i)" by blast
    have "(if selects P (Y i) then TT else (\<bottom>::tr)) \<sqsubseteq> (\<Squnion>i. if selects P (Y i) then TT else (\<bottom>::tr))"
      by (rule is_ub_thelub[OF ch])
    then show ?thesis using i by simp
  next
    case False
    then have "\<not> selects P (\<Squnion>i. Y i)" by (intro admD[OF selects_open Y]) blast
    then show ?thesis by simp
  qed
qed

lemma sel_chi_apply: "sel_chi P\<cdot>x = (if selects P x then TT else \<bottom>)"
  unfolding sel_chi_def by (rule beta_cfun[OF cont_sel_chi])

lift_definition sel_vimage :: "('a::pcpo \<rightarrow> 'b::pcpo) \<Rightarrow> 'b sel \<Rightarrow> 'a sel" is "\<lambda>g P x. P (g\<cdot>x)"
proof (intro conjI allI impI)
  fix g :: "'a \<rightarrow> 'b" and P :: "'b \<Rightarrow> bool" and x y :: 'a
  assume P: "(\<forall>x y. P x \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> P y) \<and> adm (\<lambda>x. \<not> P x)"
  show "P (g\<cdot>y)" if "P (g\<cdot>x)" "x \<sqsubseteq> y" using P that monofun_cfun_arg by blast
next
  fix g :: "'a \<rightarrow> 'b" and P :: "'b \<Rightarrow> bool"
  assume P: "(\<forall>x y. P x \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> P y) \<and> adm (\<lambda>x. \<not> P x)"
  show "adm (\<lambda>x. \<not> P (g\<cdot>x))" by (rule adm_subst[OF cont_Rep_cfun2]) (use P in blast)
qed

lemma selects_sel_vimage [simp]: "selects (sel_vimage g P) x \<longleftrightarrow> selects P (g\<cdot>x)"
  by (simp add: sel_vimage.rep_eq)

text \<open>An observation carries its declared supports: the section of the row it reads (what it
  depends on across datasets) and the part of the key determining it within every conforming dataset.\<close>

record ('r::"{bifinite, distributive_cpo}", 'k::"{bifinite, distributive_cpo}") obs =
  ofun :: "'r \<rightarrow> udom"
  ocols :: "'r semi_factor"
  okeys :: "'k semi_factor"

hide_const (open) obs.truncate

definition obs_bot :: "('r::{bifinite, distributive_cpo}, 'k::{bifinite, distributive_cpo}) obs" where
  "obs_bot = \<lparr>ofun = \<bottom>, ocols = \<bottom>, okeys = \<bottom>\<rparr>"

lemma obs_bot_simps [simp]: "ofun obs_bot = \<bottom>" "ocols obs_bot = \<bottom>" "okeys obs_bot = \<bottom>"
  by (simp_all add: obs_bot_def)

text \<open>Pairing two observations; reading back the first components of the pairs with a given
  second component.\<close>

definition obs_pair ::
  "('r::{bifinite, distributive_cpo}, 'k::{bifinite, distributive_cpo}) obs \<Rightarrow> ('r, 'k) obs \<Rightarrow> ('r, 'k) obs" where
  "obs_pair f g = \<lparr>ofun = \<Lambda> y. emb\<cdot>(ofun f\<cdot>y, ofun g\<cdot>y), ocols = ocols f \<squnion> ocols g,
     okeys = okeys f \<squnion> okeys g\<rparr>"

lemma obs_pair_apply: "ofun (obs_pair f g)\<cdot>y = emb\<cdot>(ofun f\<cdot>y, ofun g\<cdot>y)"
  by (simp add: obs_pair_def)

lemma Rep_ofun_obs_pair: "Rep_cfun (ofun (obs_pair f g)) = (\<lambda>y. emb\<cdot>(ofun f\<cdot>y, ofun g\<cdot>y))"
  by (rule ext) (rule obs_pair_apply)

lemma obs_pair_supports [simp]:
  "ocols (obs_pair f g) = ocols f \<squnion> ocols g" "okeys (obs_pair f g) = okeys f \<squnion> okeys g"
  by (simp_all add: obs_pair_def)

definition sel_snd :: "udom \<Rightarrow> udom set \<Rightarrow> udom set" where
  "sel_snd v X = {fst p |p. p \<in> (\<lambda>u. prj\<cdot>u :: udom \<times> udom) ` X \<and> snd p = v}"

lemma prj_emb_pair: "(prj\<cdot>(emb\<cdot>p) :: udom \<times> udom) = p"
  by (rule ep_pair.e_inverse[OF ep_pair_emb_prj])

lemma sel_snd_obs_pair:
  "sel_snd v (Rep_cfun (ofun (obs_pair f g)) ` Y) = Rep_cfun (ofun f) ` {y \<in> Y. ofun g\<cdot>y = v}"
  unfolding sel_snd_def by (auto simp: obs_pair_apply prj_emb_pair image_iff)

lemma emb_inj: "emb\<cdot>(x::'a::domain) = emb\<cdot>y \<Longrightarrow> x = y"
  by (metis ep_pair.e_inverse[OF ep_pair_emb_prj])

lemma emb_eq_iff: "emb\<cdot>(x::'a::domain) = emb\<cdot>y \<longleftrightarrow> x = y"
  by (blast intro: emb_inj)

text \<open>An entry of an expression's dims: lower part, upper part (doubling as the slicer level), and
  observation.\<close>

type_synonym ('k, 'r) entry = "'k semi_factor \<times> 'k semi_factor \<times> ('r, 'k) obs"

record ('k::"domain", 'f::type, 'r::"{bifinite, distributive_cpo}", 'v::type) expr =
  emind :: "'k semi_factor"
  edims :: "('k, 'r) entry list"
  esem :: "'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<rightharpoonup> 'v"

hide_const (open) expr.truncate

subsection \<open>Groups and contents\<close>

context dataspace
begin

text \<open>Key parts as observations, and whether a row passes a slice.\<close>

definition obs_key :: "'k semi_factor \<Rightarrow> ('r, 'k) obs" where
  "obs_key c = \<lparr>ofun = emb oo proj c oo rkey, ocols = csupp c, okeys = c\<rparr>"

lemma obs_key_apply: "ofun (obs_key c)\<cdot>y = emb\<cdot>(rproj c y)"
  by (simp add: obs_key_def)

lemma obs_key_supports [simp]: "ocols (obs_key c) = csupp c" "okeys (obs_key c) = c"
  by (simp_all add: obs_key_def)

definition obs_holds :: "'f \<Rightarrow> ('r, 'k) obs" where
  "obs_holds X = \<lparr>ofun = emb oo sel_chi (sel_vimage rkey (sopen X)), ocols = csupp (slod X), okeys = slod X\<rparr>"

lemma obs_holds_apply: "ofun (obs_holds X)\<cdot>y = emb\<cdot>(if holds X (rkey\<cdot>y) then TT else \<bottom>)"
  by (simp add: obs_holds_def sel_chi_apply holds_def)

lemma obs_holds_supports [simp]: "ocols (obs_holds X) = csupp (slod X)" "okeys (obs_holds X) = slod X"
  by (simp_all add: obs_holds_def)

lemma obs_holds_TT: "ofun (obs_holds X)\<cdot>y = emb\<cdot>TT \<longleftrightarrow> holds X (rkey\<cdot>y)"
proof
  assume "ofun (obs_holds X)\<cdot>y = emb\<cdot>TT"
  then have "(if holds X (rkey\<cdot>y) then TT else \<bottom>) = TT"
    unfolding obs_holds_apply by (rule emb_inj)
  then show "holds X (rkey\<cdot>y)" by (cases "holds X (rkey\<cdot>y)") simp_all
qed (simp add: obs_holds_apply)

subsection \<open>Supports of observations\<close>

text \<open>An observation is \<^emph>\<open>supported\<close> when its declared supports are supports; the constructors
  compute supported observations.\<close>

definition supported :: "('r, 'k) obs \<Rightarrow> bool" where
  "supported f \<longleftrightarrow> fun_support (ocols f) (okeys f) (ofun f)"

lemma supported_obs_bot: "supported obs_bot"
  unfolding supported_def fun_support_def obs_bot_def universally_def determines_def by simp

lemma supported_obs_key: "supported (obs_key c)"
  unfolding supported_def fun_support_def universally_def determines_def
  by (simp add: obs_key_apply csupp_reads)

lemma supported_obs_holds: "supported (obs_holds X)"
proof -
  have col: "holds X (rkey\<cdot>(x \<downharpoonright> csupp (slod X))) \<longleftrightarrow> holds X (rkey\<cdot>x)" for x
    by (metis holds_lod csupp_reads)
  have c: "ofun (obs_holds X)\<cdot>(x \<downharpoonright> csupp (slod X)) = ofun (obs_holds X)\<cdot>x" for x
    unfolding obs_holds_apply by (simp only: col)
  have eq: "Rep_cfun (ofun (obs_holds X)) = (\<lambda>k. emb\<cdot>(if holds X k then TT else \<bottom>)) \<circ> rproj (slod X)"
    by (rule ext) (simp add: obs_holds_apply holds_lod)
  have k: "determines P (\<bottom>, slod X) (Rep_cfun (ofun (obs_holds X)))" for P
    unfolding eq by (rule determines_key)
  show ?thesis
    unfolding supported_def fun_support_def universally_def obs_holds_supports using c k by blast
qed

lemma supported_obs_pair:
  assumes f: "supported f" and g: "supported g"
  shows "supported (obs_pair f g)"
proof -
  have col: "ofun h\<cdot>(x \<downharpoonright> (ocols f \<squnion> ocols g)) = ofun h\<cdot>x"
    if h: "\<And>x. ofun h\<cdot>(x \<downharpoonright> ocols h) = ofun h\<cdot>x" and le: "ocols h \<sqsubseteq> ocols f \<squnion> ocols g" for h x
    by (metis h proj_le[OF le])
  have key: "universally (\<lambda>P. determines P (\<bottom>, okeys f \<squnion> okeys g) (Rep_cfun (ofun h)))"
    if h: "universally (\<lambda>P. determines P (\<bottom>, okeys h) (Rep_cfun (ofun h)))"
      and le: "okeys h \<sqsubseteq> okeys f \<squnion> okeys g" for h
    using h by (rule universally_mono) (rule determines_trans[OF vfd_refl], simp_all add: vle_def le)
  have cf: "ofun f\<cdot>(x \<downharpoonright> (ocols f \<squnion> ocols g)) = ofun f\<cdot>x"
    and cg: "ofun g\<cdot>(x \<downharpoonright> (ocols f \<squnion> ocols g)) = ofun g\<cdot>x" for x
    using f g by (auto simp: supported_def fun_support_def intro!: col lattice_join_ge1 lattice_join_ge2)
  have kf: "universally (\<lambda>P. determines P (\<bottom>, okeys f \<squnion> okeys g) (Rep_cfun (ofun f)))"
    and kg: "universally (\<lambda>P. determines P (\<bottom>, okeys f \<squnion> okeys g) (Rep_cfun (ofun g)))"
    using f g by (auto simp: supported_def fun_support_def intro!: key lattice_join_ge1 lattice_join_ge2)
  have kp: "universally (\<lambda>P. determines P (\<bottom>, okeys f \<squnion> okeys g) (Rep_cfun (ofun (obs_pair f g))))"
    using kf kg unfolding Rep_ofun_obs_pair by (rule universally_mono2) (rule determines_pair)
  have cp: "ofun (obs_pair f g)\<cdot>(x \<downharpoonright> (ocols f \<squnion> ocols g)) = ofun (obs_pair f g)\<cdot>x" for x
    by (simp only: obs_pair_apply cf cg)
  show ?thesis unfolding supported_def fun_support_def obs_pair_supports using cp kp by blast
qed

definition group :: "'r lower_pd \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "group data a \<rho> F k = {y \<in> lower_maximal data. selects (amb F) y \<and> holds (coarsen \<rho> (slice F)) (rkey\<cdot>y) \<and>
     rproj (a \<squnion> truncate \<rho> (flod F)) y = proj (a \<squnion> truncate \<rho> (flod F))\<cdot>k}"

definition content :: "'r lower_pd \<Rightarrow> ('k, 'r) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> udom set" where
  "content data e F k = (case e of (a, \<rho>, f) \<Rightarrow> Rep_cfun (ofun f) ` group data a \<rho> F k)"

lemma content_simp [simp]: "content data (a, \<rho>, f) F k = Rep_cfun (ofun f) ` group data a \<rho> F k"
  by (simp add: content_def)

abbreviation contents :: "'r lower_pd \<Rightarrow> ('k, 'r) entry list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> udom set list" where
  "contents data es F k \<equiv> map (\<lambda>e. content data e F k) es"

subsection \<open>Column supports of frames and sections of datasets\<close>

text \<open>A selection \<^emph>\<open>reads\<close> a section of the row when it is decided there.  A frame reads a
  section covering its ambient filter and the column support of its slice's LOD.  The
  \<^emph>\<open>point section\<close> of a dataset at a section is the set of its data points cut down to it; it is
  a plain set, not down-closed: contents are sets of values over data points.\<close>

definition sel_reads :: "'r semi_factor \<Rightarrow> 'r sel \<Rightarrow> bool" where
  "sel_reads c P \<longleftrightarrow> (\<forall>y. selects P (y \<downharpoonright> c) \<longleftrightarrow> selects P y)"

definition frame_reads :: "'r semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> bool" where
  "frame_reads c F \<longleftrightarrow> sel_reads c (amb F) \<and> csupp (slod (slice F)) \<sqsubseteq> c"

definition pts_section :: "'r semi_factor \<Rightarrow> 'r lower_pd \<Rightarrow> 'r set" where
  "pts_section c data = (\<lambda>y. y \<downharpoonright> c) ` lower_maximal data"

lemma image_filter_factor:
  assumes "\<And>y. Q (g y) = Q y" and "\<And>y. h (g y) = h y"
  shows "h ` {y \<in> M. Q y} = h ` {z \<in> g ` M. Q z}"
proof -
  have "{z \<in> g ` M. Q z} = g ` {y \<in> M. Q y}" using assms(1) by auto
  then show ?thesis by (simp add: image_image assms(2))
qed

lemma holds_section: "csupp (slod X) \<sqsubseteq> c \<Longrightarrow> holds X (rkey\<cdot>(y \<downharpoonright> c)) \<longleftrightarrow> holds X (rkey\<cdot>y)"
  by (metis holds_lod rproj_section)

text \<open>The content of an entry is computed from the point section at any section covering the
  observation's columns, the group LOD's support and the frame.\<close>

lemma content_section:
  assumes F: "frame_reads c F" and G: "csupp (a \<squnion> truncate \<rho> (flod F)) \<sqsubseteq> c"
    and f: "supported f" and fc: "ocols f \<sqsubseteq> c"
  shows "content data (a, \<rho>, f) F k = Rep_cfun (ofun f) ` {z \<in> pts_section c data. selects (amb F) z \<and>
    holds (coarsen \<rho> (slice F)) (rkey\<cdot>z) \<and> rproj (a \<squnion> truncate \<rho> (flod F)) z = proj (a \<squnion> truncate \<rho> (flod F))\<cdot>k}"
proof -
  let ?G = "a \<squnion> truncate \<rho> (flod F)"
  let ?P = "\<lambda>z. selects (amb F) z \<and> holds (coarsen \<rho> (slice F)) (rkey\<cdot>z) \<and> rproj ?G z = proj ?G\<cdot>k"
  have sl: "csupp (slod (coarsen \<rho> (slice F))) \<sqsubseteq> c"
    using F csupp_mono[OF below_trans[OF slod_coarsen lattice_meet_le1]] unfolding frame_reads_def
    by (blast intro: below_trans)
  have P: "?P (y \<downharpoonright> c) \<longleftrightarrow> ?P y" for y
    using F unfolding frame_reads_def sel_reads_def by (simp add: holds_section[OF sl] rproj_section[OF G])
  have fv: "ofun f\<cdot>(y \<downharpoonright> c) = ofun f\<cdot>y" for y
  proof -
    have "ofun f\<cdot>((y \<downharpoonright> c) \<downharpoonright> ocols f) = ofun f\<cdot>(y \<downharpoonright> ocols f)" by (simp only: proj_le[OF fc])
    then show ?thesis using f by (simp add: supported_def fun_support_def)
  qed
  have "Rep_cfun (ofun f) ` {y \<in> lower_maximal data. ?P y}
      = Rep_cfun (ofun f) ` {z \<in> pts_section c data. ?P z}"
    unfolding pts_section_def by (rule image_filter_factor) (fact P fv)+
  then show ?thesis unfolding content_simp group_def .
qed

text \<open>Groups with the same parameters and rows coincide.\<close>

lemma group_cong:
  assumes "amb F = amb F'" "slice F = slice F'"
    and "a \<squnion> truncate \<rho> (flod F) = a' \<squnion> truncate \<rho> (flod F')"
    and "proj (a \<squnion> truncate \<rho> (flod F))\<cdot>k = proj (a' \<squnion> truncate \<rho> (flod F'))\<cdot>k'"
  shows "group data a \<rho> F k = group data a' \<rho> F' k'"
  using assms unfolding group_def by simp

text \<open>A lower part covering the masked part of the minimal LOD absorbs it.\<close>

lemma sat_absorb:
  fixes a \<rho> m L :: "'k semi_factor"
  assumes "truncate \<rho> m \<sqsubseteq> a"
  shows "a \<squnion> truncate \<rho> (m \<squnion> L) = a \<squnion> truncate \<rho> L"
proof -
  have "a \<squnion> truncate \<rho> (m \<squnion> L) = (a \<squnion> truncate \<rho> m) \<squnion> truncate \<rho> L"
    by (simp only: truncate_sup lattice_join_assoc)
  also have "a \<squnion> truncate \<rho> m = a" by (rule lattice_join_absorb1[OF assms])
  finally show ?thesis .
qed

end

subsection \<open>The laws\<close>

text \<open>Every entry is \<^emph>\<open>saturated\<close>: its lower part covers the part of the minimal LOD the upper
  part keeps, and the minimal LOD is the join of the lower parts.  Then a group depends on the
  frame LOD only through the key LOD.  An expression whose presence and values are governed by its
  contents satisfies the content law; a \<^emph>\<open>lawful\<close> one moreover has entries only at the frame's data
  keys.\<close>

locale expr_laws = dataspace slicing rules keying
  for slicing :: "('f, 'k::{domain, dI, locally_finitely_detailed}) slicer_ops"
    and rules :: "'r::{bifinite, distributive_cpo} schema_rules" and keying :: "('r, 'k) keying" +
  fixes E :: "('k, 'f, 'r, 'v::type) expr"
  assumes saturated: "(a, \<rho>, f) \<in> set (edims E) \<Longrightarrow> truncate \<rho> (emind E) \<sqsubseteq> a"
    and mind_lub: "emind E = fold (\<squnion>) (map fst (edims E)) \<bottom>"
    and entries_supported: "(a, \<rho>, f) \<in> set (edims E) \<Longrightarrow> supported f"
    and content_law: "\<lbrakk>conforms data; conforms data'; proj (emind E \<squnion> flod F)\<cdot>k = k; proj (emind E \<squnion> flod F')\<cdot>k' = k';
                       contents data (edims E) F k = contents data' (edims E) F' k'\<rbrakk> \<Longrightarrow> esem E data F k = esem E data' F' k'"
begin

abbreviation mind :: "'k semi_factor" where "mind \<equiv> emind E"
abbreviation dims :: "('k, 'r) entry list" where "dims \<equiv> edims E"
abbreviation sem :: "'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<rightharpoonup> 'v" where "sem \<equiv> esem E"

abbreviation "kd F \<equiv> mind \<squnion> flod F"

lemma lower_below_mind: "(a, \<rho>, f) \<in> set dims \<Longrightarrow> a \<sqsubseteq> mind"
proof -
  assume "(a, \<rho>, f) \<in> set dims"
  then have "a \<in> set (map fst dims)" by force
  then show ?thesis unfolding mind_lub by (rule fold_join_upper)
qed

text \<open>The frame LOD inside the minimal LOD does not matter: groups only see the key LOD.\<close>

lemma group_kd: "(a, \<rho>, f) \<in> set dims \<Longrightarrow> a \<squnion> truncate \<rho> (flod F) = a \<squnion> truncate \<rho> (kd F)"
  by (rule sat_absorb[symmetric, OF saturated])

lemma contents_kd:
  assumes "amb F = amb F'" "slice F = slice F'" "kd F = kd F'"
  shows "contents data dims F k = contents data dims F' k"
proof (rule map_cong[OF refl])
  fix e assume e: "e \<in> set dims"
  obtain a \<rho> f where ae: "e = (a, \<rho>, f)" by (cases e) auto
  have "group data a \<rho> F k = group data a \<rho> F' k"
    by (rule group_cong[OF assms(1,2)]) (simp_all only: group_kd[OF e[unfolded ae]] assms(3))
  then show "content data e F k = content data e F' k" by (simp add: ae)
qed

text \<open>Pegging the frame to a key does not change that key's contents: the pin's demand within
  a mask is part of the group already, by saturation.\<close>

lemma peg_group:
  assumes e: "(a, \<rho>, f) \<in> set dims" and cK: "compact K" and K: "proj (kd F)\<cdot>K = K"
  shows "group data a \<rho> (peg K F) K = group data a \<rho> F K"
proof -
  let ?G = "a \<squnion> truncate \<rho> (flod F)" and ?T = "truncate \<rho> (kd F)"
  have le: "?T \<sqsubseteq> ?G" unfolding group_kd[OF e] by (rule lattice_join_ge2)
  have pin: "holds (coarsen \<rho> (spin K)) (rkey\<cdot>y)" if y: "rproj ?G y = proj ?G\<cdot>K" for y
  proof -
    have "proj \<rho>\<cdot>K = proj ?T\<cdot>K" by (simp only: proj_inf K)
    also have "\<dots> = proj ?T\<cdot>(proj ?G\<cdot>K)" by (rule proj_le[OF le, symmetric])
    also have "\<dots> = proj ?T\<cdot>(rproj ?G y)" by (simp only: y)
    also have "\<dots> = rproj ?T y" by (rule proj_le[OF le])
    finally have "proj \<rho>\<cdot>K \<sqsubseteq> rkey\<cdot>y" using proj_below[of ?T "rkey\<cdot>y"] by simp
    then show ?thesis by (simp add: coarsen_spin[OF cK] holds_spin[OF compact_proj_compact[OF cK]])
  qed
  show ?thesis unfolding group_def using pin by (auto simp: coarsen_conj)
qed

lemma peg_contents:
  assumes cK: "compact K" and K: "proj (kd F)\<cdot>K = K"
  shows "contents data dims (peg K F) K = contents data dims F K"
proof (rule map_cong[OF refl])
  fix e assume e: "e \<in> set dims"
  obtain a \<rho> f where ae: "e = (a, \<rho>, f)" by (cases e) auto
  show "content data e (peg K F) K = content data e F K"
    by (simp add: ae peg_group[OF e[unfolded ae] cK K])
qed


text \<open>Contents only depend on the point section at a section covering the frame, the key LOD and
  the entries' columns.\<close>

lemma contents_section:
  assumes F: "frame_reads c F" and K: "csupp (kd F) \<sqsubseteq> c"
    and cols: "\<And>a \<rho> f. (a, \<rho>, f) \<in> set dims \<Longrightarrow> ocols f \<sqsubseteq> c"
    and sec: "pts_section c data = pts_section c data'"
  shows "contents data dims F k = contents data' dims F k"
proof (rule map_cong[OF refl])
  fix e assume e: "e \<in> set dims"
  obtain a \<rho> f where ae: "e = (a, \<rho>, f)" by (cases e) auto
  have G: "csupp (a \<squnion> truncate \<rho> (flod F)) \<sqsubseteq> c"
  proof (rule below_trans[OF csupp_mono K])
    show "a \<squnion> truncate \<rho> (flod F) \<sqsubseteq> kd F"
      using lower_below_mind[OF e[unfolded ae]] truncate_below[of \<rho> "flod F"]
      by (blast intro: join_belowI lattice_join_ge1 lattice_join_ge2 below_trans)
  qed
  note sf = entries_supported[OF e[unfolded ae]] and fc = cols[OF e[unfolded ae]]
  show "content data e F k = content data' e F k"
    unfolding ae content_section[OF F G sf fc] sec ..
qed
end

locale expr_sem = expr_laws +
  assumes key_law: "conforms data \<Longrightarrow> sem data F k \<noteq> None \<Longrightarrow> keyimg data F (mind \<squnion> flod F) k"
begin

lemma key_lives: "conforms data \<Longrightarrow> sem data F k \<noteq> None \<Longrightarrow> proj (kd F)\<cdot>k = k"
  using key_law[of data F k] by (auto simp: keyimg_def)

text \<open>The effective-LOD law: the frame LOD matters only through the key LOD.\<close>

theorem eff_law:
  assumes d: "conforms data" and F: "amb F = amb F'" "slice F = slice F'" "kd F = kd F'"
  shows "sem data F = sem data F'"
proof
  fix k
  show "sem data F k = sem data F' k"
  proof (cases "proj (kd F)\<cdot>k = k")
    case True
    then have "proj (kd F')\<cdot>k = k" by (simp add: F(3))
    then show ?thesis by (rule content_law[OF d d True _ contents_kd[OF F]])
  next
    case False
    then have "proj (kd F')\<cdot>k \<noteq> k" by (simp add: F(3))
    then have "sem data F' k = None" using key_lives[OF d, of F' k] by blast
    moreover have "sem data F k = None" using False key_lives[OF d, of F k] by blast
    ultimately show ?thesis by simp
  qed
qed

text \<open>The peg law: pegging the frame to a key does not change the value there.\<close>

theorem peg_law:
  assumes d: "conforms data" and cK: "compact K"
  shows "sem data (peg K F) K = sem data F K"
proof (cases "proj (kd F)\<cdot>K = K")
  case True
  have "proj (kd (peg K F))\<cdot>K = K" using True by simp
  then show ?thesis by (rule content_law[OF d d _ True peg_contents[OF cK True]])
next
  case False
  then have "proj (kd (peg K F))\<cdot>K \<noteq> K" by simp
  then have "sem data (peg K F) K = None" using key_lives[OF d, of "peg K F" K] by blast
  moreover have "sem data F K = None" using False key_lives[OF d, of F K] by blast
  ultimately show ?thesis by simp
qed


text \<open>Locality: the semantics at a frame depends on the dataset only through its point section at
  a section covering the frame, the key LOD and the entries' columns.\<close>

theorem sem_section:
  assumes d: "conforms data" and d': "conforms data'"
    and F: "frame_reads c F" and K: "csupp (kd F) \<sqsubseteq> c"
    and cols: "\<And>a \<rho> f. (a, \<rho>, f) \<in> set dims \<Longrightarrow> ocols f \<sqsubseteq> c"
    and sec: "pts_section c data = pts_section c data'"
  shows "sem data F k = sem data' F k"
proof (cases "proj (kd F)\<cdot>k = k")
  case True
  show ?thesis by (rule content_law[OF d d' True True contents_section[OF F K cols sec]])
next
  case False
  then have "sem data F k = None" "sem data' F k = None" using key_lives[OF d] key_lives[OF d'] by blast+
  then show ?thesis by simp
qed
end

text \<open>Within a dataspace, a semantics with these laws is \<^emph>\<open>lawful\<close>.  The laws quantify over the
  datasets conforming to the schema.\<close>

context dataspace
begin

abbreviation semilawful where "semilawful \<equiv> expr_laws slicing rules keying"
abbreviation lawful where "lawful \<equiv> expr_sem slicing rules keying"

lemma lawfulI:
  assumes "\<And>a \<rho> f. (a, \<rho>, f) \<in> set (edims E) \<Longrightarrow> truncate \<rho> (emind E) \<sqsubseteq> a"
    and "emind E = fold (\<squnion>) (map fst (edims E)) \<bottom>"
    and "\<And>a \<rho> f. (a, \<rho>, f) \<in> set (edims E) \<Longrightarrow> supported f"
    and "\<And>data data' F F' k k'. \<lbrakk>conforms data; conforms data'; proj (emind E \<squnion> flod F)\<cdot>k = k;
           proj (emind E \<squnion> flod F')\<cdot>k' = k'; contents data (edims E) F k = contents data' (edims E) F' k'\<rbrakk> \<Longrightarrow>
           esem E data F k = esem E data' F' k'"
    and "\<And>data F k. conforms data \<Longrightarrow> esem E data F k \<noteq> None \<Longrightarrow> keyimg data F (emind E \<squnion> flod F) k"
  shows "lawful E"
  by (intro expr_sem.intro expr_laws.intro dataspace_axioms expr_laws_axioms.intro
      expr_sem_axioms.intro) (fact assms)+

lemma lawful_supported: "lawful E \<Longrightarrow> (a, \<rho>, f) \<in> set (edims E) \<Longrightarrow> supported f"
  by (rule expr_laws.entries_supported[OF expr_sem.axioms(1)])

end

subsection \<open>Lemmas for the combinators\<close>

lemma fold_join_absorb: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<sqsubseteq> b) \<Longrightarrow> fold (\<squnion>) xs b = (b::'a::lattice_complete)"
  by (induct xs) (simp_all add: lattice_join_absorb2)

lemma fold_join_bots: "fold (\<squnion>) (map (\<lambda>_. \<bottom>) xs) (\<bottom>::'a::lattice_complete) = \<bottom>"
  by (induct xs) (simp_all add: lattice_join_bot_left)

lemma fold_join_least:
  "(\<And>x. x \<in> set xs \<Longrightarrow> x \<sqsubseteq> y) \<Longrightarrow> b \<sqsubseteq> y \<Longrightarrow> fold (\<squnion>) xs b \<sqsubseteq> (y::'a::lattice_complete)"
  by (induct xs arbitrary: b) (simp_all add: lattice_join_least)

lemma fold_join_base: "b \<sqsubseteq> fold (\<squnion>) xs (b::'a::lattice_complete)"
proof (induct xs arbitrary: b)
  case (Cons x xs)
  have "b \<sqsubseteq> x \<squnion> b" by (rule lattice_join_ge2)
  also have "\<dots> \<sqsubseteq> fold (\<squnion>) xs (x \<squnion> b)" by (rule Cons)
  finally show ?case by simp
qed simp

text \<open>Tupling every observation with the same one keeps the lower parts.\<close>

lemma map_fst_tuple: "map fst (map (\<lambda>(a, \<rho>, f). (a, h \<rho>, g \<rho> f)) xs) = map fst xs"
  by (induct xs) auto

lemma mem_tuple:
  "(a, \<rho>', f') \<in> set (map (\<lambda>(a, \<rho>, f). (a, h \<rho>, g \<rho> f)) xs) \<Longrightarrow> \<exists>\<rho> f. (a, \<rho>, f) \<in> set xs \<and> \<rho>' = h \<rho>"
  by auto

lemma concat_map_blocks:
  assumes "concat (map f xs) = concat (map g xs)" and "\<And>x. x \<in> set xs \<Longrightarrow> length (f x) = length (g x)"
    and "x \<in> set xs"
  shows "f x = g x"
  using assms
proof (induct xs)
  case (Cons y ys)
  have l: "length (f y) = length (g y)" by (rule Cons.prems(2)) simp
  have "f y = g y \<and> concat (map f ys) = concat (map g ys)"
    using Cons.prems(1) by (simp add: append_eq_append_conv[OF disjI1[OF l]])
  then show ?case using Cons by auto
qed simp

lemma proj_sup_eq:
  "proj (a \<squnion> b)\<cdot>x = proj (a \<squnion> b)\<cdot>z \<longleftrightarrow> proj a\<cdot>x = proj a\<cdot>z \<and> proj b\<cdot>x = proj b\<cdot>z"
proof
  assume e: "proj (a \<squnion> b)\<cdot>x = proj (a \<squnion> b)\<cdot>z"
  show "proj a\<cdot>x = proj a\<cdot>z \<and> proj b\<cdot>x = proj b\<cdot>z"
    using arg_cong[OF e, of "Rep_cfun (proj a)"] arg_cong[OF e, of "Rep_cfun (proj b)"]
    by (simp add: proj_le lattice_join_ge1 lattice_join_ge2)
qed (simp add: proj_sup)

lemma emb_image_eq: "Rep_cfun emb ` A = Rep_cfun emb ` B \<Longrightarrow> A = (B :: 'a::domain set)"
  by (rule inj_image_eq_iff[THEN iffD1, rotated]) (auto intro: inj_onI emb_inj)

context dataspace
begin

text \<open>The group of the full mask on top of an LOD is the key's own group.\<close>

lemma group_top:
  assumes "proj (c \<squnion> flod F)\<cdot>k = k"
  shows "group data c lattice_top F k = {y \<in> lower_maximal data. frows F y \<and> rproj (c \<squnion> flod F) y = k}"
  using assms by (auto simp: group_def truncate_top frows_def)

lemma keyimg_group_top:
  assumes "proj (c \<squnion> flod F)\<cdot>k = k"
  shows "keyimg data F (c \<squnion> flod F) k \<longleftrightarrow> group data c lattice_top F k \<noteq> {}"
  by (auto simp: group_top[OF assms] keyimg_def)

end

end
