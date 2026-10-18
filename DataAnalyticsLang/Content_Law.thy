theory Content_Law
  imports Expr_Combinators Aggregate
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

record ('k::"domain", 'f::type, 'r::pcpo, 'v::type) cexpr =
  cmind :: "'k semi_factor"
  cdims :: "('k, 'r) entry list"
  csem :: "('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<rightharpoonup> 'v"

hide_const (open) cexpr.truncate

subsection \<open>Groups and contents\<close>

locale content_space = dataspace conj sunit slod sopen coarsen spin rkey S
  for conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) and sunit :: 'f (\<open>\<^bold>1\<close>)
    and slod :: "'f \<Rightarrow> 'k::{domain, dI, locally_finitely_detailed} semi_factor"
    and sopen :: "'f \<Rightarrow> 'k sel" and coarsen spin and rkey :: "'r::pcpo \<rightarrow> 'k" and S :: "'r set"
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

locale content_laws = content_space +
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

locale content_sem = content_laws +
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

context content_space
begin

abbreviation csemilawful where "csemilawful \<equiv> content_laws conj sunit slod sopen coarsen spin rkey S"
abbreviation clawful where "clawful \<equiv> content_sem conj sunit slod sopen coarsen spin rkey S"
abbreviation clawfulE where "clawfulE E \<equiv> clawful (cmind E) (cdims E) (csem E)"

lemma clawfulI:
  assumes "\<And>a \<rho> f. (a, \<rho>, f) \<in> set dims \<Longrightarrow> truncate \<rho> mind \<sqsubseteq> a"
    and "mind = fold (\<squnion>) (map fst dims) \<bottom>"
    and "\<And>F F' k k'. \<lbrakk>proj (mind \<squnion> flod F)\<cdot>k = k; proj (mind \<squnion> flod F')\<cdot>k' = k';
                       contents dims F k = contents dims F' k'\<rbrakk> \<Longrightarrow> sem F k = sem F' k'"
    and "\<And>F k. sem F k \<noteq> None \<Longrightarrow> keyimg S F (mind \<squnion> flod F) k"
  shows "clawful mind dims sem"
  by (intro content_sem.intro content_laws.intro content_space_axioms content_laws_axioms.intro
      content_sem_axioms.intro) (fact assms)+

end


section \<open>Combinators\<close>

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

lemma agg_fold_bij:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and h: "bij_betw h A B"
  shows "agg_fold f (v \<circ> h) A = agg_fold f v B"
proof -
  interpret A: comm_monoid_set "opt_op f" None
    unfolding comm_monoid_set_def by (rule comm_monoid_opt_op[OF f])
  show ?thesis unfolding agg_fold_def comp_def by (rule A.reindex_bij_betw[OF h])
qed

context content_space
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

subsection \<open>Values\<close>

text \<open>A function of the key at an LOD \<open>c\<close>, at the frame's data keys.  It reads the key part
  \<open>c\<close> of the key's own group.\<close>

definition cvalue_at :: "'k semi_factor \<Rightarrow> ('k \<rightarrow> 'v::cpo) \<Rightarrow> ('k, 'f, 'r, 'v) cexpr" where
  "cvalue_at c g = \<lparr>cmind = c, cdims = [(c, lattice_top, obs_key c)],
     csem = \<lambda>F k. if keyimg S F (c \<squnion> flod F) k then Some (g\<cdot>(proj c\<cdot>k)) else None\<rparr>"

lemma cvalue_at_simps [simp]:
  "cmind (cvalue_at c g) = c" "cdims (cvalue_at c g) = [(c, lattice_top, obs_key c)]"
  "csem (cvalue_at c g) F k = (if keyimg S F (c \<squnion> flod F) k then Some (g\<cdot>(proj c\<cdot>k)) else None)"
  by (simp_all add: cvalue_at_def)

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

theorem lawful_cvalue_at: "clawfulE (cvalue_at c g)"
proof (rule clawfulI, simp_all only: cvalue_at_simps)
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

definition csmap :: "('v::cpo \<rightarrow> 'w::cpo) \<Rightarrow> ('k, 'f, 'r, 'v) cexpr \<Rightarrow> ('k, 'f, 'r, 'w) cexpr" where
  "csmap g E = \<lparr>cmind = cmind E, cdims = cdims E, csem = \<lambda>F k. map_option (Rep_cfun g) (csem E F k)\<rparr>"

lemma csmap_simps [simp]:
  "cmind (csmap g E) = cmind E" "cdims (csmap g E) = cdims E"
  "csem (csmap g E) F k = map_option (Rep_cfun g) (csem E F k)"
  by (simp_all add: csmap_def)

theorem lawful_csmap: assumes "clawfulE E" shows "clawfulE (csmap g E)"
proof -
  interpret E: content_sem conj sunit slod sopen coarsen spin rkey S "cmind E" "cdims E" "csem E"
    by (fact assms)
  show ?thesis
  proof (rule clawfulI, simp_all only: csmap_simps)
    show "truncate \<rho> (cmind E) \<sqsubseteq> a" if "(a, \<rho>, f) \<in> set (cdims E)" for a \<rho> f
      by (rule E.saturated[OF that])
    show "cmind E = fold (\<squnion>) (map fst (cdims E)) \<bottom>" by (rule E.mind_lub)
    show "map_option (Rep_cfun g) (csem E F k) = map_option (Rep_cfun g) (csem E F' k')"
      if "proj (cmind E \<squnion> flod F)\<cdot>k = k" "proj (cmind E \<squnion> flod F')\<cdot>k' = k'"
        "contents (cdims E) F k = contents (cdims E) F' k'" for F F' k k'
      by (simp only: E.content_law[OF that])
    show "keyimg S F (cmind E \<squnion> flod F) k" if "map_option (Rep_cfun g) (csem E F k) \<noteq> None" for F k
      using that by (intro E.key_law) simp
  qed
qed

subsection \<open>\<open>RESTRICT\<close>\<close>

text \<open>Restricting conjoins a slicer to the ambient filter, on the rows' keys: inner groups are the
  outer groups' rows passing it, so each entry is tupled with whether a row passes.\<close>

abbreviation frestrict_key :: "'f \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> ('k semi_factor, 'f, 'r) frame" where
  "frestrict_key G \<equiv> frestrict (sel_vimage rkey (sopen G))"

definition crestrict :: "'f \<Rightarrow> ('k, 'f, 'r, 'v) cexpr \<Rightarrow> ('k, 'f, 'r, 'v) cexpr" where
  "crestrict G E = \<lparr>cmind = cmind E,
     cdims = map (\<lambda>(a, \<rho>, f). (a, \<rho>, obs_pair f (obs_holds G))) (cdims E),
     csem = \<lambda>F. csem E (frestrict_key G F)\<rparr>"

lemma crestrict_simps [simp]:
  "cmind (crestrict G E) = cmind E"
  "cdims (crestrict G E) = map (\<lambda>(a, \<rho>, f). (a, \<rho>, obs_pair f (obs_holds G))) (cdims E)"
  "csem (crestrict G E) F = csem E (frestrict_key G F)"
  by (simp_all add: crestrict_def)

lemma group_frestrict_key:
  "group a \<rho> (frestrict_key G F) k = {y \<in> group a \<rho> F k. holds G (rkey\<cdot>y)}"
  by (auto simp: group_def holds_def)

lemma content_frestrict_key:
  "content (a, \<rho>, f) (frestrict_key G F) k = sel_snd (emb\<cdot>TT) (content (a, \<rho>, obs_pair f (obs_holds G)) F k)"
  by (simp add: sel_snd_obs_pair obs_holds_TT group_frestrict_key)

theorem lawful_crestrict: assumes "clawfulE E" shows "clawfulE (crestrict G E)"
proof -
  interpret E: content_sem conj sunit slod sopen coarsen spin rkey S "cmind E" "cdims E" "csem E"
    by (fact assms)
  let ?t = "\<lambda>(a, \<rho>, f). (a, \<rho>, obs_pair f (obs_holds G))"
  show ?thesis
  proof (rule clawfulI, simp_all only: crestrict_simps)
    show "truncate \<rho> (cmind E) \<sqsubseteq> a" if "(a, \<rho>, f) \<in> set (map ?t (cdims E))" for a \<rho> f
      using that by (auto intro: E.saturated)
    show "cmind E = fold (\<squnion>) (map fst (map ?t (cdims E))) \<bottom>"
      using map_fst_tuple[of "\<lambda>\<rho>. \<rho>" "\<lambda>\<rho> f. obs_pair f (obs_holds G)" "cdims E"]
      by (simp only: E.mind_lub[symmetric])
    show "csem E (frestrict_key G F) k = csem E (frestrict_key G F') k'"
      if k: "proj (cmind E \<squnion> flod F)\<cdot>k = k" "proj (cmind E \<squnion> flod F')\<cdot>k' = k'"
        and e: "contents (map ?t (cdims E)) F k = contents (map ?t (cdims E)) F' k'" for F F' k k'
    proof (rule E.content_law)
      show "proj (cmind E \<squnion> flod (frestrict_key G F))\<cdot>k = k" using k(1) by simp
      show "proj (cmind E \<squnion> flod (frestrict_key G F'))\<cdot>k' = k'" using k(2) by simp
      have inner: "contents (cdims E) (frestrict_key G H) \<kappa>
          = map (sel_snd (emb\<cdot>TT)) (contents (map ?t (cdims E)) H \<kappa>)" for H \<kappa>
        by (auto simp: content_def content_frestrict_key[simplified] split: prod.splits)
      show "contents (cdims E) (frestrict_key G F) k = contents (cdims E) (frestrict_key G F') k'"
        by (simp only: inner e)
    qed
    show "keyimg S F (cmind E \<squnion> flod F) k" if "csem E (frestrict_key G F) k \<noteq> None" for F k
    proof -
      have "keyimg S (frestrict_key G F) (cmind E \<squnion> flod F) k"
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

definition cfor :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'f, 'r, 'v) cexpr \<Rightarrow> ('k, 'f, 'r, 'v) cexpr" where
  "cfor \<tau> G E = \<lparr>cmind = cmind E,
     cdims = (cmind E, lattice_top, \<bottom>) #
       map (\<lambda>(a, \<rho>, f). (a, \<rho> \<sqinter> \<tau>, obs_pair f (obs_holds (coarsen \<rho> G)))) (cdims E),
     csem = \<lambda>F k. if keyimg S F (cmind E \<squnion> flod F) k
       then csem E (ffor \<tau> G F) (proj (cmind E \<squnion> flod (ffor \<tau> G F))\<cdot>k) else None\<rparr>"

abbreviation cfixed :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v) cexpr \<Rightarrow> ('k, 'f, 'r, 'v) cexpr" where
  "cfixed D \<equiv> cfor D \<^bold>1"

lemma cfor_simps [simp]:
  "cmind (cfor \<tau> G E) = cmind E"
  "cdims (cfor \<tau> G E) = (cmind E, lattice_top, \<bottom>) #
       map (\<lambda>(a, \<rho>, f). (a, \<rho> \<sqinter> \<tau>, obs_pair f (obs_holds (coarsen \<rho> G)))) (cdims E)"
  "csem (cfor \<tau> G E) F k = (if keyimg S F (cmind E \<squnion> flod F) k
       then csem E (ffor \<tau> G F) (proj (cmind E \<squnion> flod (ffor \<tau> G F))\<cdot>k) else None)"
  by (simp_all add: cfor_def)

lemma amb_ffor' [simp]: "amb (ffor \<tau> G F) = amb F"
  and flod_ffor' [simp]: "flod (ffor \<tau> G F) = truncate \<tau> (flod F)"
  and slice_ffor' [simp]: "slice (ffor \<tau> G F) = coarsen \<tau> (slice F) \<^bold>* G"
  by (simp_all add: ffor_def)

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
    unfolding flod_ffor' truncate_inf_comp by (rule lattice_join_mono[OF am truncate_below])
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

theorem lawful_cfor: assumes "clawfulE E" shows "clawfulE (cfor \<tau> G E)"
proof -
  interpret E: content_sem conj sunit slod sopen coarsen spin rkey S "cmind E" "cdims E" "csem E"
    by (fact assms)
  let ?m = "cmind E"
  let ?t = "\<lambda>(a, \<rho>, f). (a, \<rho> \<sqinter> \<tau>, obs_pair f (obs_holds (coarsen \<rho> G)))"
  have inner: "contents (cdims E) (ffor \<tau> G H) (proj (?m \<squnion> flod (ffor \<tau> G H))\<cdot>\<kappa>)
      = map (sel_snd (emb\<cdot>TT)) (contents (map ?t (cdims E)) H \<kappa>)" for H \<kappa>
  proof -
    have "content e (ffor \<tau> G H) (proj (?m \<squnion> flod (ffor \<tau> G H))\<cdot>\<kappa>) = sel_snd (emb\<cdot>TT) (content (?t e) H \<kappa>)"
      if e: "e \<in> set (cdims E)" for e
    proof -
      obtain a \<rho> f where ae: "e = (a, \<rho>, f)" by (cases e) auto
      show ?thesis unfolding ae
        by (simp only: content_ffor[OF E.lower_below_mind[OF e[unfolded ae]]] prod.case)
    qed
    then show ?thesis by simp
  qed
  show ?thesis
  proof (rule clawfulI, simp_all only: cfor_simps)
    show "truncate \<rho> ?m \<sqsubseteq> a" if "(a, \<rho>, f) \<in> set ((?m, lattice_top, \<bottom>) # map ?t (cdims E))" for a \<rho> f
    proof -
      from that consider "a = ?m" "\<rho> = lattice_top" | \<rho>0 f0 where "(a, \<rho>0, f0) \<in> set (cdims E)" "\<rho> = \<rho>0 \<sqinter> \<tau>"
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
    show "?m = fold (\<squnion>) (map fst ((?m, lattice_top, \<bottom>) # map ?t (cdims E))) \<bottom>"
    proof -
      have a: "fold (\<squnion>) (map fst (cdims E)) ?m = ?m"
        by (rule fold_join_absorb) (auto intro: E.lower_below_mind)
      have mf: "map fst (map ?t (cdims E)) = map fst (cdims E)" by (rule map_fst_tuple)
      show ?thesis
        by (simp only: list.map(2) mf fst_conv fold.simps(2) comp_apply a lattice_join_bot_right)
    qed
    show "keyimg S F (?m \<squnion> flod F) k"
      if "(if keyimg S F (?m \<squnion> flod F) k
          then csem E (ffor \<tau> G F) (proj (?m \<squnion> flod (ffor \<tau> G F))\<cdot>k) else None) \<noteq> None" for F k
      using that by (simp split: if_splits)
    show "(if keyimg S F (?m \<squnion> flod F) k
          then csem E (ffor \<tau> G F) (proj (?m \<squnion> flod (ffor \<tau> G F))\<cdot>k) else None)
        = (if keyimg S F' (?m \<squnion> flod F') k'
          then csem E (ffor \<tau> G F') (proj (?m \<squnion> flod (ffor \<tau> G F'))\<cdot>k') else None)"
      if k: "proj (?m \<squnion> flod F)\<cdot>k = k" "proj (?m \<squnion> flod F')\<cdot>k' = k'"
        and e: "contents ((?m, lattice_top, \<bottom>) # map ?t (cdims E)) F k
              = contents ((?m, lattice_top, \<bottom>) # map ?t (cdims E)) F' k'" for F F' k k'
    proof -
      have eh: "content (?m, lattice_top, \<bottom>) F k = content (?m, lattice_top, \<bottom>) F' k'"
        and et: "contents (map ?t (cdims E)) F k = contents (map ?t (cdims E)) F' k'"
        using e by (simp_all only: list.map list.inject)
      have g: "keyimg S F (?m \<squnion> flod F) k \<longleftrightarrow> keyimg S F' (?m \<squnion> flod F') k'"
        using eh by (simp only: content_const_top[OF k(1)] content_const_top[OF k(2)]) (simp split: if_splits)
      have v: "csem E (ffor \<tau> G F) (proj (?m \<squnion> flod (ffor \<tau> G F))\<cdot>k)
          = csem E (ffor \<tau> G F') (proj (?m \<squnion> flod (ffor \<tau> G F'))\<cdot>k')"
        by (rule E.content_law) (simp_all only: proj_idem inner et)
      show ?thesis using g v by simp
    qed
  qed
qed


subsection \<open>Collect\<close>

text \<open>The components are evaluated under the frame extended by all their minimal LODs, so their
  values correspond to the full key; another component's minimal LOD enters a component's entries
  only through their lower parts.\<close>

definition cshift :: "'k semi_factor \<Rightarrow> ('k, 'r) entry \<Rightarrow> ('k, 'r) entry" where
  "cshift M e = (case e of (a, \<rho>, f) \<Rightarrow> (a \<squnion> truncate \<rho> M, \<rho>, f))"

definition ccollect :: "('k, 'f, 'r, 'a::domain) cexpr list \<Rightarrow> ('k, 'f, 'r, 'a ltuple) cexpr" where
  "ccollect Es = (let M = fold (\<squnion>) (map cmind Es) \<bottom> in
     \<lparr>cmind = M, cdims = concat (map (\<lambda>E. map (cshift M) (cdims E)) Es),
      csem = \<lambda>F k. map_option ltuple_of (those (map (\<lambda>E. csem E (finclude M F) k) Es))\<rparr>)"

lemma ccollect_simps:
  "cmind (ccollect Es) = fold (\<squnion>) (map cmind Es) \<bottom>"
  "cdims (ccollect Es) = concat (map (\<lambda>E. map (cshift (cmind (ccollect Es))) (cdims E)) Es)"
  "csem (ccollect Es) F k
     = map_option ltuple_of (those (map (\<lambda>E. csem E (finclude (cmind (ccollect Es)) F) k) Es))"
  by (simp_all add: ccollect_def Let_def)

lemma content_cshift: "content (cshift M e) F k = content e (finclude M F) k"
proof (cases e)
  case (fields a \<rho> f)
  have lod: "(a \<squnion> truncate \<rho> M) \<squnion> truncate \<rho> (flod F) = a \<squnion> truncate \<rho> (flod (finclude M F))"
    by (simp add: truncate_sup lattice_join_ac)
  have "group (a \<squnion> truncate \<rho> M) \<rho> F k = group a \<rho> (finclude M F) k"
    by (rule group_cong) (simp_all only: amb_finclude slice_finclude lod)
  then show ?thesis by (simp add: fields cshift_def)
qed

theorem lawful_ccollect:
  assumes ne: "Es \<noteq> []" and law: "\<And>E. E \<in> set Es \<Longrightarrow> clawfulE E"
  shows "clawfulE (ccollect Es)"
proof -
  let ?M = "fold (\<squnion>) (map cmind Es) \<bottom>"
  have mE: "cmind E \<sqsubseteq> ?M" if "E \<in> set Es" for E
    by (rule fold_join_upper) (simp add: that)
  have kd: "cmind E \<squnion> flod (finclude ?M F) = ?M \<squnion> flod F" if "E \<in> set Es" for E F
  proof -
    have "cmind E \<squnion> (flod F \<squnion> ?M) = (cmind E \<squnion> ?M) \<squnion> flod F" by (simp only: lattice_join_ac)
    also have "cmind E \<squnion> ?M = ?M" by (rule lattice_join_absorb2[OF mE[OF that]])
    finally show ?thesis by simp
  qed
  have M: "cmind (ccollect Es) = ?M" by (simp add: ccollect_simps)
  show ?thesis
  proof (rule clawfulI, simp_all only: ccollect_simps M)
    show "truncate \<rho> ?M \<sqsubseteq> a"
      if "(a, \<rho>, f) \<in> set (concat (map (\<lambda>E. map (cshift ?M) (cdims E)) Es))" for a \<rho> f
      using that by (auto simp: cshift_def split: prod.splits intro: lattice_join_ge2)
    show "?M = fold (\<squnion>) (map fst (concat (map (\<lambda>E. map (cshift ?M) (cdims E)) Es))) \<bottom>"
    proof (rule below_antisym)
      let ?R = "fold (\<squnion>) (map fst (concat (map (\<lambda>E. map (cshift ?M) (cdims E)) Es))) \<bottom>"
      show "?M \<sqsubseteq> ?R"
      proof (rule fold_join_least)
        fix x assume "x \<in> set (map cmind Es)"
        then obtain E where E: "E \<in> set Es" and x: "x = cmind E" by auto
        interpret E: content_sem conj sunit slod sopen coarsen spin rkey S "cmind E" "cdims E" "csem E"
          by (rule law[OF E])
        show "x \<sqsubseteq> ?R" unfolding x E.mind_lub
        proof (rule fold_join_least)
          fix a assume "a \<in> set (map fst (cdims E))"
          then obtain \<rho> f where e: "(a, \<rho>, f) \<in> set (cdims E)" by auto
          have "a \<sqsubseteq> a \<squnion> truncate \<rho> ?M" by (rule lattice_join_ge1)
          also have "\<dots> \<sqsubseteq> ?R"
            by (rule fold_join_upper) (use E e in \<open>force simp: cshift_def\<close>)
          finally show "a \<sqsubseteq> ?R" .
        qed simp
      qed simp
      show "?R \<sqsubseteq> ?M"
      proof (rule fold_join_least)
        fix x assume "x \<in> set (map fst (concat (map (\<lambda>E. map (cshift ?M) (cdims E)) Es)))"
        then obtain E a \<rho> f where E: "E \<in> set Es" and e: "(a, \<rho>, f) \<in> set (cdims E)"
          and x: "x = a \<squnion> truncate \<rho> ?M" by (auto simp: cshift_def split: prod.splits)
        interpret E: content_sem conj sunit slod sopen coarsen spin rkey S "cmind E" "cdims E" "csem E"
          by (rule law[OF E])
        have "a \<sqsubseteq> ?M" by (rule below_trans[OF E.lower_below_mind[OF e] mE[OF E]])
        then show "x \<sqsubseteq> ?M" unfolding x by (rule lattice_join_least[OF _ truncate_below])
      qed simp
    qed
    show "map_option ltuple_of (those (map (\<lambda>E. csem E (finclude ?M F) k) Es))
        = map_option ltuple_of (those (map (\<lambda>E. csem E (finclude ?M F') k') Es))"
      if k: "proj (?M \<squnion> flod F)\<cdot>k = k" "proj (?M \<squnion> flod F')\<cdot>k' = k'"
        and e: "contents (concat (map (\<lambda>E. map (cshift ?M) (cdims E)) Es)) F k
              = contents (concat (map (\<lambda>E. map (cshift ?M) (cdims E)) Es)) F' k'" for F F' k k'
    proof -
      have c: "contents (concat (map (\<lambda>E. map (cshift ?M) (cdims E)) Es)) G \<kappa>
          = concat (map (\<lambda>E. contents (cdims E) (finclude ?M G) \<kappa>) Es)" for G \<kappa>
        by (simp add: map_concat map_map comp_def content_cshift)
      have blocks: "contents (cdims E) (finclude ?M F) k = contents (cdims E) (finclude ?M F') k'"
        if E: "E \<in> set Es" for E
        by (rule concat_map_blocks[where xs = Es, OF e[unfolded c c] _ E]) simp
      have "csem E (finclude ?M F) k = csem E (finclude ?M F') k'" if E: "E \<in> set Es" for E
      proof -
        interpret E: content_sem conj sunit slod sopen coarsen spin rkey S "cmind E" "cdims E" "csem E"
          by (rule law[OF E])
        show ?thesis by (rule E.content_law[OF _ _ blocks[OF E]]) (simp_all only: kd[OF E] k)
      qed
      then show ?thesis by (simp cong: map_cong)
    qed
    show "keyimg S F (?M \<squnion> flod F) k"
      if "map_option ltuple_of (those (map (\<lambda>E. csem E (finclude ?M F) k) Es)) \<noteq> None" for F k
    proof -
      obtain E0 where E0: "E0 \<in> set Es" using ne by (cases Es) auto
      interpret E0: content_sem conj sunit slod sopen coarsen spin rkey S "cmind E0" "cdims E0" "csem E0"
        by (rule law[OF E0])
      have "csem E0 (finclude ?M F) k \<noteq> None"
        using that E0 by (auto simp: those_not_None_iff simp del: not_None_eq)
      then have "keyimg S (finclude ?M F) (cmind E0 \<squnion> flod (finclude ?M F)) k" by (rule E0.key_law)
      then show ?thesis by (simp only: kd[OF E0] keyimg_cong[OF frows_finclude])
    qed
  qed
qed

subsection \<open>Aggregation\<close>

text \<open>\<open>aggregate R f E\<close> folds the inner entries over each fiber of the frame LOD, the inner
  expression being evaluated under the frame refined by the extra requested dimensions \<open>R\<close> (a
  grouping inside the aggregate).  Its keys are the frame's, so it decides no detail: the lower
  parts of the inner entries move into the observations, and the fold reads the fiber's classes
  at \<open>cmind E \<squnion> R\<close>.\<close>

definition caggregate :: "'k semi_factor \<Rightarrow> ('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) cexpr \<Rightarrow> ('k, 'f, 'r, 'v) cexpr" where
  "caggregate R f E = \<lparr>cmind = \<bottom>,
     cdims = (\<bottom>, lattice_top, obs_key (cmind E \<squnion> R)) #
       map (\<lambda>(a, \<rho>, g). (\<bottom>, \<rho>, obs_pair g (obs_key (a \<squnion> truncate \<rho> R)))) (cdims E),
     csem = \<lambda>F k. agg_fold f (csem E (finclude R F))
       (rproj (cmind E \<squnion> flod (finclude R F)) ` afiber F (flod F) k)\<rparr>"

lemma caggregate_simps [simp]:
  "cmind (caggregate R f E) = \<bottom>"
  "cdims (caggregate R f E) = (\<bottom>, lattice_top, obs_key (cmind E \<squnion> R)) #
       map (\<lambda>(a, \<rho>, g). (\<bottom>, \<rho>, obs_pair g (obs_key (a \<squnion> truncate \<rho> R)))) (cdims E)"
  "csem (caggregate R f E) F k = agg_fold f (csem E (finclude R F))
       (rproj (cmind E \<squnion> flod (finclude R F)) ` afiber F (flod F) k)"
  by (simp_all add: caggregate_def)

theorem lawful_caggregate:
  assumes E: "clawfulE E" and f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "clawfulE (caggregate R f E)"
proof -
  interpret E: content_sem conj sunit slod sopen coarsen spin rkey S "cmind E" "cdims E" "csem E"
    by (fact E)
  let ?m = "cmind E"
  let ?t = "\<lambda>(a, \<rho>, g). (\<bottom>::'k semi_factor, \<rho>, obs_pair g (obs_key (a \<squnion> truncate \<rho> R)))"
  have bj: "\<bottom> \<squnion> X = X" for X :: "'k semi_factor" by (rule lattice_join_bot_left)
  have ok: "Rep_cfun (obs_key c) = (\<lambda>y. emb\<cdot>(rproj c y))" for c by (rule ext) (rule obs_key_apply)
  text \<open>The fold entry reads the fiber.\<close>
  have fiber: "group \<bottom> lattice_top F k = afiber F (flod F) k" if "proj (flod F)\<cdot>k = k" for F k
  proof -
    have "proj (\<bottom> \<squnion> flod F)\<cdot>k = k" using that by (simp only: bj)
    then show ?thesis by (simp add: group_top afiber_def bj)
  qed
  text \<open>An inner group is the outer group through the same upper part, cut down by the inner
    key's lower part and requested part.\<close>
  have ig: "group a \<rho> (finclude R F) (rproj (?m \<squnion> flod (finclude R F)) y)
      = {y' \<in> group \<bottom> \<rho> F k. rproj (a \<squnion> truncate \<rho> R) y' = rproj (a \<squnion> truncate \<rho> R) y}"
    if y: "rproj (flod F) y = k" and am: "a \<sqsubseteq> ?m" for a \<rho> F k y
  proof -
    let ?X = "?m \<squnion> flod (finclude R F)" and ?A = "a \<squnion> truncate \<rho> R" and ?L = "truncate \<rho> (flod F)"
    have lod: "a \<squnion> truncate \<rho> (flod (finclude R F)) = ?A \<squnion> ?L" by (simp add: truncate_sup lattice_join_ac)
    have mR: "?m \<squnion> R \<sqsubseteq> ?X" by (simp add: lattice_join_mono lattice_join_ge2)
    have AX: "?A \<sqsubseteq> ?X" by (rule below_trans[OF lattice_join_mono[OF am truncate_below] mR])
    have LX: "?L \<sqsubseteq> ?X"
      by (rule below_trans[OF truncate_below]) (simp add: below_trans[OF lattice_join_ge1 lattice_join_ge2])
    have kA: "proj ?A\<cdot>(rproj ?X y) = rproj ?A y" by (rule proj_le[OF AX])
    have kL: "proj ?L\<cdot>(rproj ?X y) = proj ?L\<cdot>k"
    proof -
      have "proj ?L\<cdot>(rproj ?X y) = rproj ?L y" by (rule proj_le[OF LX])
      also have "\<dots> = proj ?L\<cdot>(rproj (flod F) y)" by (rule proj_le[OF truncate_below, symmetric])
      finally show ?thesis by (simp only: y)
    qed
    show ?thesis unfolding group_def lod proj_sup_eq kA kL by (auto simp: bj proj_bot)
  qed
  text \<open>Inner keys of a fiber correspond to their parts at \<open>cmind E \<squnion> R\<close>.\<close>
  have bij: "bij_betw (Rep_cfun (proj (?m \<squnion> R))) (rproj (?m \<squnion> flod (finclude R F)) ` afiber F (flod F) k)
      (rproj (?m \<squnion> R) ` afiber F (flod F) k)" for F k
  proof -
    let ?X = "?m \<squnion> flod (finclude R F)" and ?Z = "afiber F (flod F) k"
    have le: "?m \<squnion> R \<sqsubseteq> ?X" by (simp add: lattice_join_mono lattice_join_ge2)
    have pr: "proj (?m \<squnion> R)\<cdot>(rproj ?X y) = rproj (?m \<squnion> R) y" for y by (rule proj_le[OF le])
    show ?thesis
    proof (rule bij_betw_imageI)
      show "inj_on (Rep_cfun (proj (?m \<squnion> R))) (rproj ?X ` ?Z)"
      proof (rule inj_onI)
        fix \<kappa>1 \<kappa>2 assume k1: "\<kappa>1 \<in> rproj ?X ` ?Z" and k2: "\<kappa>2 \<in> rproj ?X ` ?Z"
          and e: "proj (?m \<squnion> R)\<cdot>\<kappa>1 = proj (?m \<squnion> R)\<cdot>\<kappa>2"
        obtain y1 where y1: "y1 \<in> ?Z" "\<kappa>1 = rproj ?X y1" using k1 by blast
        obtain y2 where y2: "y2 \<in> ?Z" "\<kappa>2 = rproj ?X y2" using k2 by blast
        have "rproj (?m \<squnion> R) y1 = rproj (?m \<squnion> R) y2" using e unfolding y1(2) y2(2) pr .
        moreover have "rproj (flod F) y1 = rproj (flod F) y2" using y1(1) y2(1) by (simp add: afiber_def)
        ultimately have "rproj ((?m \<squnion> R) \<squnion> flod F) y1 = rproj ((?m \<squnion> R) \<squnion> flod F) y2"
          by (simp only: rproj_sup_eq)
        moreover have "(?m \<squnion> R) \<squnion> flod F = ?X" by (simp add: lattice_join_ac)
        ultimately show "\<kappa>1 = \<kappa>2" by (simp add: y1(2) y2(2))
      qed
      show "Rep_cfun (proj (?m \<squnion> R)) ` rproj ?X ` ?Z = rproj (?m \<squnion> R) ` ?Z"
        by (simp only: image_image pr)
    qed
  qed
  text \<open>The content of an inner entry at an inner key is read off the outer entry's content.\<close>
  have inner: "content e (finclude R G) \<kappa>
      = sel_snd (emb\<cdot>(proj (fst e \<squnion> truncate (fst (snd e)) R)\<cdot>p)) (content (?t e) G kG)"
    if e: "e \<in> set (cdims E)" and yZ: "y \<in> afiber G (flod G) kG"
      and \<kappa>: "\<kappa> = rproj (?m \<squnion> flod (finclude R G)) y" and py: "proj (?m \<squnion> R)\<cdot>\<kappa> = p" for e G kG \<kappa> y p
  proof -
    obtain a \<rho> g where ae: "e = (a, \<rho>, g)" by (cases e) auto
    have am: "a \<sqsubseteq> ?m" by (rule E.lower_below_mind[OF e[unfolded ae]])
    let ?A = "a \<squnion> truncate \<rho> R"
    have AmR: "?A \<sqsubseteq> ?m \<squnion> R" by (rule lattice_join_mono[OF am truncate_below])
    have mR: "?m \<squnion> R \<sqsubseteq> ?m \<squnion> flod (finclude R G)" by (simp add: lattice_join_mono lattice_join_ge2)
    have yA: "rproj ?A y = proj ?A\<cdot>p"
    proof -
      have "proj ?A\<cdot>p = proj ?A\<cdot>\<kappa>" unfolding py[symmetric] by (rule proj_le[OF AmR])
      also have "\<dots> = rproj ?A y" unfolding \<kappa> by (rule proj_le[OF below_trans[OF AmR mR]])
      finally show ?thesis by simp
    qed
    have gy: "rproj (flod G) y = kG" using yZ by (simp add: afiber_def)
    have grp: "group a \<rho> (finclude R G) \<kappa> = {y' \<in> group \<bottom> \<rho> G kG. rproj ?A y' = proj ?A\<cdot>p}"
      unfolding \<kappa> ig[OF gy am] yA ..
    show ?thesis unfolding ae by (simp add: grp sel_snd_obs_pair obs_key_apply emb_eq_iff)
  qed
  show ?thesis
  proof (rule clawfulI, simp_all only: caggregate_simps)
    show "truncate \<rho> \<bottom> \<sqsubseteq> a"
      if "(a, \<rho>, g) \<in> set ((\<bottom>, lattice_top, obs_key (?m \<squnion> R)) # map ?t (cdims E))" for a \<rho> g
      using that by (auto simp: lattice_meet_bot_right)
    show "(\<bottom>::'k semi_factor) = fold (\<squnion>) (map fst ((\<bottom>, lattice_top, obs_key (?m \<squnion> R)) # map ?t (cdims E))) \<bottom>"
    proof -
      let ?es = "(\<bottom>::'k semi_factor, lattice_top, obs_key (?m \<squnion> R)) # map ?t (cdims E)"
      text \<open>Every lower part is \<open>\<bottom>\<close>, and joining \<open>\<bottom>\<close>s onto \<open>\<bottom>\<close> gives \<open>\<bottom>\<close>.\<close>
      have l: "map fst ?es = map (\<lambda>_. \<bottom>) ?es"
        by (simp only: list.map(2) fst_conv) (simp add: map_map comp_def split_def)
      show ?thesis by (simp only: l fold_join_bots)
    qed
    show "keyimg S F (\<bottom> \<squnion> flod F) k"
      if "agg_fold f (csem E (finclude R F)) (rproj (?m \<squnion> flod (finclude R F)) ` afiber F (flod F) k) \<noteq> None"
      for F k
    proof -
      have "afiber F (flod F) k \<noteq> {}" using agg_fold_nonempty[OF f that] by auto
      then show ?thesis by (auto simp: afiber_def keyimg_def bj)
    qed
    show "agg_fold f (csem E (finclude R F)) (rproj (?m \<squnion> flod (finclude R F)) ` afiber F (flod F) k)
        = agg_fold f (csem E (finclude R F')) (rproj (?m \<squnion> flod (finclude R F')) ` afiber F' (flod F') k')"
      if k: "proj (\<bottom> \<squnion> flod F)\<cdot>k = k" "proj (\<bottom> \<squnion> flod F')\<cdot>k' = k'"
        and e: "contents ((\<bottom>, lattice_top, obs_key (?m \<squnion> R)) # map ?t (cdims E)) F k
              = contents ((\<bottom>, lattice_top, obs_key (?m \<squnion> R)) # map ?t (cdims E)) F' k'" for F F' k k'
    proof -
      have k1: "proj (flod F)\<cdot>k = k" and k2: "proj (flod F')\<cdot>k' = k'" using k by (simp_all only: bj)
      have eh: "content (\<bottom>, lattice_top, obs_key (?m \<squnion> R)) F k = content (\<bottom>, lattice_top, obs_key (?m \<squnion> R)) F' k'"
        and et: "contents (map ?t (cdims E)) F k = contents (map ?t (cdims E)) F' k'"
        using e by (simp_all only: list.map list.inject)
      have ptw: "content (?t e) F k = content (?t e) F' k'" if "e \<in> set (cdims E)" for e
        using et that by (simp add: map_eq_conv)
      let ?Z = "afiber F (flod F) k" and ?Z' = "afiber F' (flod F') k'"
      let ?K = "rproj (?m \<squnion> flod (finclude R F)) ` ?Z" and ?K' = "rproj (?m \<squnion> flod (finclude R F')) ` ?Z'"
      let ?P = "rproj (?m \<squnion> R) ` ?Z" and ?\<pi> = "Rep_cfun (proj (?m \<squnion> R))"
      have P: "rproj (?m \<squnion> R) ` ?Z' = ?P"
      proof (rule emb_image_eq)
        show "Rep_cfun emb ` rproj (?m \<squnion> R) ` ?Z' = Rep_cfun emb ` ?P"
          using eh by (simp add: fiber[OF k1] fiber[OF k2] image_image ok)
      qed
      define \<psi> where "\<psi> = inv_into ?K ?\<pi>"
      define \<psi>' where "\<psi>' = inv_into ?K' ?\<pi>"
      have b: "bij_betw \<psi> ?P ?K" unfolding \<psi>_def by (rule bij_betw_inv_into[OF bij])
      have b': "bij_betw \<psi>' ?P ?K'" unfolding \<psi>'_def using bij_betw_inv_into[OF bij[of F' k']] by (simp only: P)
      have sP: "?\<pi> ` ?K = ?P" by (rule bij_betw_imp_surj_on[OF bij])
      have sP': "?\<pi> ` ?K' = ?P" using bij_betw_imp_surj_on[OF bij[of F' k']] by (simp only: P)
      have pt: "csem E (finclude R F) (\<psi> p) = csem E (finclude R F') (\<psi>' p)" if p: "p \<in> ?P" for p
      proof -
        have pK: "\<psi> p \<in> ?K" unfolding \<psi>_def by (rule inv_into_into) (simp only: sP p)
        have pK': "\<psi>' p \<in> ?K'" unfolding \<psi>'_def by (rule inv_into_into) (simp only: sP' p)
        obtain y where y: "y \<in> ?Z" "\<psi> p = rproj (?m \<squnion> flod (finclude R F)) y" using pK by blast
        obtain y' where y': "y' \<in> ?Z'" "\<psi>' p = rproj (?m \<squnion> flod (finclude R F')) y'" using pK' by blast
        have py: "proj (?m \<squnion> R)\<cdot>(\<psi> p) = p" unfolding \<psi>_def by (rule f_inv_into_f) (simp only: sP p)
        have py': "proj (?m \<squnion> R)\<cdot>(\<psi>' p) = p" unfolding \<psi>'_def by (rule f_inv_into_f) (simp only: sP' p)
        show ?thesis
        proof (rule E.content_law)
          show "proj (?m \<squnion> flod (finclude R F))\<cdot>(\<psi> p) = \<psi> p" by (simp only: y(2) proj_idem)
          show "proj (?m \<squnion> flod (finclude R F'))\<cdot>(\<psi>' p) = \<psi>' p" by (simp only: y'(2) proj_idem)
          show "contents (cdims E) (finclude R F) (\<psi> p) = contents (cdims E) (finclude R F') (\<psi>' p)"
          proof (rule map_cong[OF refl])
            fix e assume e: "e \<in> set (cdims E)"
            show "content e (finclude R F) (\<psi> p) = content e (finclude R F') (\<psi>' p)"
              by (simp only: inner[OF e y(1) y(2) py] inner[OF e y'(1) y'(2) py'] ptw[OF e])
          qed
        qed
      qed
      have "agg_fold f (csem E (finclude R F)) ?K = agg_fold f (csem E (finclude R F) \<circ> \<psi>) ?P"
        by (rule agg_fold_bij[OF f b, symmetric])
      also have "\<dots> = agg_fold f (csem E (finclude R F') \<circ> \<psi>') ?P"
        by (rule agg_fold_cong[OF f refl]) (simp add: pt)
      also have "\<dots> = agg_fold f (csem E (finclude R F')) ?K'"
        by (rule agg_fold_bij[OF f b'])
      finally show ?thesis .
    qed
  qed
qed

end


end
