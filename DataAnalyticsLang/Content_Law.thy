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

text \<open>Pairing two observations; reading back the first components of the pairs with a given
  second component.\<close>

definition obs_pair :: "('r::cpo \<rightarrow> udom) \<Rightarrow> ('r \<rightarrow> udom) \<Rightarrow> 'r \<rightarrow> udom" where
  "obs_pair f g = (\<Lambda> y. emb\<cdot>(f\<cdot>y, g\<cdot>y))"

lemma obs_pair_apply: "obs_pair f g\<cdot>y = emb\<cdot>(f\<cdot>y, g\<cdot>y)"
  by (simp add: obs_pair_def)

definition sel_snd :: "udom \<Rightarrow> udom set \<Rightarrow> udom set" where
  "sel_snd v X = {fst p |p. p \<in> (\<lambda>u. prj\<cdot>u :: udom \<times> udom) ` X \<and> snd p = v}"

lemma prj_emb_pair: "(prj\<cdot>(emb\<cdot>p) :: udom \<times> udom) = p"
  by (rule ep_pair.e_inverse[OF ep_pair_emb_prj])

lemma sel_snd_obs_pair: "sel_snd v (Rep_cfun (obs_pair f g) ` Y) = Rep_cfun f ` {y \<in> Y. g\<cdot>y = v}"
  unfolding sel_snd_def by (auto simp: obs_pair_apply prj_emb_pair image_iff)

lemma emb_inj: "emb\<cdot>(x::'a::domain) = emb\<cdot>y \<Longrightarrow> x = y"
  by (metis ep_pair.e_inverse[OF ep_pair_emb_prj])

lemma emb_eq_iff: "emb\<cdot>(x::'a::domain) = emb\<cdot>y \<longleftrightarrow> x = y"
  by (blast intro: emb_inj)

text \<open>An entry of an expression's dims: lower part, upper part (doubling as the slicer level), and
  observation.\<close>

type_synonym ('k, 'r) entry = "'k semi_factor \<times> 'k semi_factor \<times> ('r \<rightarrow> udom)"

record ('k::"domain", 'f::type, 'r::pcpo, 'v::type) expr =
  emind :: "'k semi_factor"
  edims :: "('k, 'r) entry list"
  esem :: "('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<rightharpoonup> 'v"

hide_const (open) expr.truncate

subsection \<open>Groups and contents\<close>

context dataspace
begin

text \<open>Key parts as observations, and whether a row passes a slice.\<close>

definition obs_key :: "'k semi_factor \<Rightarrow> 'r \<rightarrow> udom" where
  "obs_key c = emb oo proj c oo rkey"

lemma obs_key_apply: "obs_key c\<cdot>y = emb\<cdot>(rproj c y)"
  by (simp add: obs_key_def)

definition obs_holds :: "'f \<Rightarrow> 'r \<rightarrow> udom" where
  "obs_holds X = emb oo sel_chi (sel_vimage rkey (sopen X))"

lemma obs_holds_apply: "obs_holds X\<cdot>y = emb\<cdot>(if holds X (rkey\<cdot>y) then TT else \<bottom>)"
  by (simp add: obs_holds_def sel_chi_apply holds_def)

lemma obs_holds_TT: "obs_holds X\<cdot>y = emb\<cdot>TT \<longleftrightarrow> holds X (rkey\<cdot>y)"
proof
  assume "obs_holds X\<cdot>y = emb\<cdot>TT"
  then have "(if holds X (rkey\<cdot>y) then TT else \<bottom>) = TT"
    unfolding obs_holds_apply by (rule emb_inj)
  then show "holds X (rkey\<cdot>y)" by (cases "holds X (rkey\<cdot>y)") simp_all
qed (simp add: obs_holds_apply)

definition group :: "'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "group a \<rho> F k = {y \<in> pts S. selects (amb F) y \<and> holds (coarsen \<rho> (slice F)) (rkey\<cdot>y) \<and>
     rproj (a \<squnion> truncate \<rho> (flod F)) y = proj (a \<squnion> truncate \<rho> (flod F))\<cdot>k}"

definition content :: "('k, 'r) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> udom set" where
  "content e F k = (case e of (a, \<rho>, f) \<Rightarrow> Rep_cfun f ` group a \<rho> F k)"

lemma content_simp [simp]: "content (a, \<rho>, f) F k = Rep_cfun f ` group a \<rho> F k"
  by (simp add: content_def)

abbreviation contents :: "('k, 'r) entry list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> udom set list" where
  "contents es F k \<equiv> map (\<lambda>e. content e F k) es"

text \<open>Groups with the same parameters and rows coincide.\<close>

lemma group_cong:
  assumes "amb F = amb F'" "slice F = slice F'"
    and "a \<squnion> truncate \<rho> (flod F) = a' \<squnion> truncate \<rho> (flod F')"
    and "proj (a \<squnion> truncate \<rho> (flod F))\<cdot>k = proj (a' \<squnion> truncate \<rho> (flod F'))\<cdot>k'"
  shows "group a \<rho> F k = group a' \<rho> F' k'"
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

locale expr_laws = dataspace +
  fixes mind dims sem
  assumes saturated: "(a, \<rho>, f) \<in> set dims \<Longrightarrow> truncate \<rho> mind \<sqsubseteq> a"
    and mind_lub: "mind = fold (\<squnion>) (map fst dims) \<bottom>"
    and content_law: "\<lbrakk>proj (mind \<squnion> flod F)\<cdot>k = k; proj (mind \<squnion> flod F')\<cdot>k' = k';
                       contents dims F k = contents dims F' k'\<rbrakk> \<Longrightarrow> sem F k = sem F' k'"
begin

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
  shows "contents dims F k = contents dims F' k"
proof (rule map_cong[OF refl])
  fix e assume e: "e \<in> set dims"
  obtain a \<rho> f where ae: "e = (a, \<rho>, f)" by (cases e) auto
  have "group a \<rho> F k = group a \<rho> F' k"
    by (rule group_cong[OF assms(1,2)]) (simp_all only: group_kd[OF e[unfolded ae]] assms(3))
  then show "content e F k = content e F' k" by (simp add: ae)
qed

text \<open>Pegging the frame to a key does not change that key's contents: the pin's demand within
  a mask is part of the group already, by saturation.\<close>

lemma peg_group:
  assumes e: "(a, \<rho>, f) \<in> set dims" and cK: "compact K" and K: "proj (kd F)\<cdot>K = K"
  shows "group a \<rho> (peg K F) K = group a \<rho> F K"
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
  shows "contents dims (peg K F) K = contents dims F K"
proof (rule map_cong[OF refl])
  fix e assume e: "e \<in> set dims"
  obtain a \<rho> f where ae: "e = (a, \<rho>, f)" by (cases e) auto
  show "content e (peg K F) K = content e F K"
    by (simp add: ae peg_group[OF e[unfolded ae] cK K])
qed

end

locale expr_sem = expr_laws +
  assumes key_law: "sem F k \<noteq> None \<Longrightarrow> keyimg S F (mind \<squnion> flod F) k"
begin

lemma key_lives: "sem F k \<noteq> None \<Longrightarrow> proj (kd F)\<cdot>k = k"
  using key_law[of F k] by (auto simp: keyimg_def)

text \<open>The effective-LOD law: the frame LOD matters only through the key LOD.\<close>

theorem eff_law:
  assumes "amb F = amb F'" "slice F = slice F'" "kd F = kd F'"
  shows "sem F = sem F'"
proof
  fix k
  show "sem F k = sem F' k"
  proof (cases "proj (kd F)\<cdot>k = k")
    case True
    then have "proj (kd F')\<cdot>k = k" by (simp add: assms(3))
    then show ?thesis by (rule content_law[OF True _ contents_kd[OF assms]])
  next
    case False
    then have "proj (kd F')\<cdot>k \<noteq> k" by (simp add: assms(3))
    then have "sem F' k = None" using key_lives[of F' k] by blast
    moreover have "sem F k = None" using False key_lives[of F k] by blast
    ultimately show ?thesis by simp
  qed
qed

text \<open>The peg law: pegging the frame to a key does not change the value there.\<close>

theorem peg_law:
  assumes cK: "compact K"
  shows "sem (peg K F) K = sem F K"
proof (cases "proj (kd F)\<cdot>K = K")
  case True
  have "proj (kd (peg K F))\<cdot>K = K" using True by simp
  then show ?thesis by (rule content_law[OF _ True peg_contents[OF cK True]])
next
  case False
  then have "proj (kd (peg K F))\<cdot>K \<noteq> K" by simp
  then have "sem (peg K F) K = None" using key_lives[of "peg K F" K] by blast
  moreover have "sem F K = None" using False key_lives[of F K] by blast
  ultimately show ?thesis by simp
qed

end

text \<open>Within a dataspace, a semantics with these laws is \<^emph>\<open>lawful\<close>.\<close>

context dataspace
begin

abbreviation semilawful where "semilawful \<equiv> expr_laws conj sunit slod sopen coarsen spin rkey S"
abbreviation lawful where "lawful \<equiv> expr_sem conj sunit slod sopen coarsen spin rkey S"
abbreviation lawfulE where "lawfulE E \<equiv> lawful (emind E) (edims E) (esem E)"

lemma lawfulI:
  assumes "\<And>a \<rho> f. (a, \<rho>, f) \<in> set dims \<Longrightarrow> truncate \<rho> mind \<sqsubseteq> a"
    and "mind = fold (\<squnion>) (map fst dims) \<bottom>"
    and "\<And>F F' k k'. \<lbrakk>proj (mind \<squnion> flod F)\<cdot>k = k; proj (mind \<squnion> flod F')\<cdot>k' = k';
                       contents dims F k = contents dims F' k'\<rbrakk> \<Longrightarrow> sem F k = sem F' k'"
    and "\<And>F k. sem F k \<noteq> None \<Longrightarrow> keyimg S F (mind \<squnion> flod F) k"
  shows "lawful mind dims sem"
  by (intro expr_sem.intro expr_laws.intro dataspace_axioms expr_laws_axioms.intro
      expr_sem_axioms.intro) (fact assms)+

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
  shows "group c lattice_top F k = {y \<in> pts S. frows F y \<and> rproj (c \<squnion> flod F) y = k}"
  using assms by (auto simp: group_def truncate_top frows_def)

lemma keyimg_group_top:
  assumes "proj (c \<squnion> flod F)\<cdot>k = k"
  shows "keyimg S F (c \<squnion> flod F) k \<longleftrightarrow> group c lattice_top F k \<noteq> {}"
  by (auto simp: group_top[OF assms] keyimg_def)

end

end
