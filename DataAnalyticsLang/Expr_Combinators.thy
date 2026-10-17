theory Expr_Combinators
  imports Frame
begin

section \<open>Combinators on expression semantics\<close>

text \<open>Record-level constructions do not conform to data on their own; they are lawful
  \<^emph>\<open>up to data\<close> (their guard is lawful), and a single guard where they enter an
  aggregation restores the key-data law.  Collecting a list of expressions into a strict tuple,
  followed by a map, expresses every strict operator of any arity.\<close>

subsection \<open>Strict tuples\<close>

text \<open>A strict tuple is \<open>\<bottom>\<close> as soon as one component is: it has an entry exactly where every
  component has one.  No order classes are needed for values; they will be once tuples are key
  values.\<close>

domain ('a::"domain") stuple = SNil | SCons 'a "'a stuple"

fun stuple_of :: "'a::domain list \<Rightarrow> 'a stuple" where
  "stuple_of [] = SNil"
| "stuple_of (x # xs) = SCons\<cdot>x\<cdot>(stuple_of xs)"

lemma stuple_of_bottom_iff: "stuple_of xs = \<bottom> \<longleftrightarrow> (\<exists>x\<in>set xs. x = \<bottom>)"
  by (induct xs) simp_all

context dataspace
begin

subsection \<open>Key LODs\<close>

definition ekd :: "('k semi_factor, 'f, 'r, 'k, 'v) expr \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor" where
  "ekd E F = emind E \<squnion> flod F"

subsection \<open>Collect\<close>

text \<open>The components are evaluated at the frame extended by all their minds, so they all share
  the collected key LOD; the collected minimal LOD is the join, and the dims are the pointwise
  join: at each mask the collected natural LOD is at least each component's, so the collected
  dims hypothesis gives each component's.\<close>

lemma compact_fun_join:
  fixes f g :: "'a \<Rightarrow> 'c::{bifinite, distributive_cpo} semi_factor"
  assumes f: "compact f" and g: "compact g"
  shows "compact (f \<squnion> g)"
proof -
  have fg: "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)" by (rule fun_join) simp
  have "{x. f x \<squnion> g x \<noteq> \<bottom>} \<subseteq> {x. f x \<noteq> \<bottom>} \<union> {x. g x \<noteq> \<bottom>}" by auto
  moreover have "finite ({x. f x \<noteq> \<bottom>} \<union> {x. g x \<noteq> \<bottom>})" using f g by (simp add: compact_fun_iff)
  ultimately have "finite {x. f x \<squnion> g x \<noteq> \<bottom>}" by (rule finite_subset)
  moreover have "compact (f x \<squnion> g x)" for x
    using f g by (simp add: compact_fun_iff compact_semi_factor_sup)
  ultimately show ?thesis by (simp add: compact_fun_iff fg)
qed

lemma compact_fun_fold_join:
  "(\<And>f. f \<in> set fs \<Longrightarrow> compact f) \<Longrightarrow> compact b
    \<Longrightarrow> compact (fold (\<squnion>) fs b :: 'a \<Rightarrow> 'c::{bifinite, distributive_cpo} semi_factor)"
  by (induct fs arbitrary: b) (simp_all add: compact_fun_join)

lemma fold_join_apply_le:
  fixes fs :: "('a \<Rightarrow> 'c::lattice_complete) list"
  shows "(\<And>f. f \<in> set fs \<Longrightarrow> f x \<sqsubseteq> f y) \<Longrightarrow> b x \<sqsubseteq> b y \<Longrightarrow> fold (\<squnion>) fs b x \<sqsubseteq> fold (\<squnion>) fs b y"
proof (induct fs arbitrary: b)
  case (Cons a fs)
  have "a x \<sqsubseteq> a y" by (rule Cons.prems(1)) simp
  then have "(a \<squnion> b) x \<sqsubseteq> (a \<squnion> b) y" using Cons.prems(2) by (simp add: fun_join lattice_join_mono)
  then show ?case unfolding fold_Cons o_apply by (rule Cons.hyps[rotated]) (rule Cons.prems(1), simp)
qed simp

definition collect :: "('k semi_factor, 'f, 'r, 'k, 'a::domain) expr list \<Rightarrow> ('k semi_factor, 'f, 'r, 'k, 'a stuple) expr"
  where "collect Es =
    (let M = fold (\<squnion>) (map emind Es) \<bottom> in
     \<lparr>emind = M, edims = fold (\<squnion>) (map edims Es) \<bottom>,
      esem = \<lambda>F k. stuple_of (map (\<lambda>E. esem E (finclude M F) k) Es)\<rparr>)"

lemma collect_simps:
  "emind (collect Es) = fold (\<squnion>) (map emind Es) \<bottom>"
  "edims (collect Es) = fold (\<squnion>) (map edims Es) \<bottom>"
  "esem (collect Es) F k = stuple_of (map (\<lambda>E. esem E (finclude (emind (collect Es)) F) k) Es)"
  by (simp_all add: collect_def Let_def)

lemma edims_collect_upper: "E \<in> set Es \<Longrightarrow> edims E \<rho> \<sqsubseteq> edims (collect Es) \<rho>"
  unfolding collect_simps by (rule fun_belowD, rule fold_join_upper) simp

lemma ekd_collect:
  "E \<in> set Es \<Longrightarrow> ekd E (finclude (emind (collect Es)) F) = ekd (collect Es) F"
proof -
  assume "E \<in> set Es"
  then have "emind E \<sqsubseteq> emind (collect Es)" unfolding collect_simps by (simp add: fold_join_upper)
  then have "emind E \<squnion> emind (collect Es) = emind (collect Es)" by (rule lattice_join_absorb2)
  then show ?thesis unfolding ekd_def flod_finclude by (metis lattice_join_commute lattice_join_left_commute)
qed

text \<open>A collection of lawful components is lawful.\<close>

theorem lawful_collect:
  assumes ne: "Es \<noteq> []" and law: "\<And>E. E \<in> set Es \<Longrightarrow> lawfulE E"
  shows "lawfulE (collect Es)"
proof -
  let ?M = "emind (collect Es)"
  have kd: "(emind E \<squnion> flod (finclude ?M F)) = (?M \<squnion> flod F)"
    if "E \<in> set Es" for E and F :: "('k semi_factor, 'f, 'r) frame"
    using ekd_collect[OF that, of F] by (simp only: ekd_def)
  obtain E0 where E0: "E0 \<in> set Es" using ne by (cases Es) auto
  have nb: "esem E (finclude ?M F) k \<noteq> \<bottom>" if "esem (collect Es) F k \<noteq> \<bottom>" "E \<in> set Es" for E F k
    using that by (auto simp: collect_simps stuple_of_bottom_iff)
  interpret E0: expr_sem conj sunit slod sopen coarsen spin rkey S
    "emind E0" "edims E0" "esem E0"
    by (rule law[OF E0])
  show ?thesis
  proof (rule lawfulI)
    show "\<exists>k'. k \<sqsubseteq> k' \<and> holds (slice F) k'" if "esem (collect Es) F k \<noteq> \<bottom>" for F k
      using E0.key_slicer[OF nb[OF that E0]] by simp
    show "proj (?M \<squnion> flod F)\<cdot>k = k" if "esem (collect Es) F k \<noteq> \<bottom>" for F k
      using E0.key_lives[OF nb[OF that E0]] by (simp only: kd[OF E0])
    show "keyimg S F (?M \<squnion> flod F) k" if "esem (collect Es) F k \<noteq> \<bottom>" for F k
      using E0.key_data[OF nb[OF that E0]]
      by (simp only: kd[OF E0] keyimg_cong[OF frows_finclude])
    show "esem (collect Es) (peg K F) K = esem (collect Es) F K" if "compact K" for F K
    proof -
      note cK = that
      have e: "esem E (finclude ?M (peg K F)) K = esem E (finclude ?M F) K" if "E \<in> set Es" for E
      proof -
        interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S
          "emind E" "edims E" "esem E"
          by (rule law[OF that])
        show ?thesis by (simp only: peg_finclude[symmetric] E.peg_law[OF cK])
      qed
      show ?thesis unfolding collect_simps(3)
        by (rule arg_cong[where f = stuple_of], rule map_cong[OF refl e])
    qed
    show "esem (collect Es) F (rproj (?M \<squnion> flod F) x)
        = esem (collect Es) F' (rproj (?M \<squnion> flod F') x)"
      if "amb F = amb F'" "slice F = slice F'" "x \<in> pts S"
        "dims_equivs (edims (collect Es)) F x (?M \<squnion> flod F) (?M \<squnion> flod F')"
        "esem (collect Es) F (rproj (?M \<squnion> flod F) x) \<noteq> \<bottom>"
        "esem (collect Es) F' (rproj (?M \<squnion> flod F') x) \<noteq> \<bottom>" for F F' x
    proof -
      note a = that
      have e: "esem E (finclude ?M F) (rproj (?M \<squnion> flod F) x)
          = esem E (finclude ?M F') (rproj (?M \<squnion> flod F') x)" if E: "E \<in> set Es" for E
      proof -
        interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S
          "emind E" "edims E" "esem E"
          by (rule law[OF E])
        have eq: "dims_equivs (edims E) (finclude ?M F) x
            (E.kd (finclude ?M F)) (E.kd (finclude ?M F'))"
        proof (rule dims_equivsI)
          fix \<rho>
          have "dims_equiv (edims (collect Es) \<rho>) \<rho> F x (?M \<squnion> flod F) (?M \<squnion> flod F')"
            by (rule dims_equivsD[OF a(4)])
          then have "dims_equiv (edims E \<rho>) \<rho> F x (?M \<squnion> flod F) (?M \<squnion> flod F')"
            by (rule dims_equiv_natd_le[OF edims_collect_upper[OF E]])
          then show "dims_equiv (edims E \<rho>) \<rho> (finclude ?M F) x (E.kd (finclude ?M F)) (E.kd (finclude ?M F'))"
            by (simp only: kd[OF E] dims_equiv_def mrows_cong[OF amb_finclude slice_finclude])
        qed
        have "esem E (finclude ?M F) (rproj (E.kd (finclude ?M F)) x)
            = esem E (finclude ?M F') (rproj (E.kd (finclude ?M F')) x)"
          by (rule E.dims_law[OF _ _ a(3) eq])
            (use nb[OF a(5) E] nb[OF a(6) E] in
              \<open>simp_all only: amb_finclude slice_finclude a(1,2) kd[OF E] not_False_eq_True\<close>)
        then show ?thesis by (simp only: kd[OF E])
      qed
      show ?thesis unfolding collect_simps(3)
        by (rule arg_cong[where f = stuple_of], rule map_cong[OF refl e])
    qed
    show "esem (collect Es) F = esem (collect Es) F'"
      if "amb F = amb F'" "slice F = slice F'" "(?M \<squnion> flod F) = (?M \<squnion> flod F')"
      for F F' :: "('k semi_factor, 'f, 'r) frame"
    proof -
      note a = that
      have e: "esem E (finclude ?M F) = esem E (finclude ?M F')" if "E \<in> set Es" for E
      proof -
        interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S
          "emind E" "edims E" "esem E"
          by (rule law[OF that])
        show ?thesis by (rule E.eff_law) (simp_all only: amb_finclude slice_finclude kd[OF that] a)
      qed
      show ?thesis unfolding collect_simps(3)
        by (intro ext arg_cong[where f = stuple_of] map_cong[OF refl]) (simp only: e)
    qed
    show "compact ?M" unfolding collect_simps(1)
      by (rule compact_fold_sup) (auto intro: expr_sem.mind_compact[OF law])
    show "compact (edims (collect Es))" unfolding collect_simps(2)
      by (rule compact_fun_fold_join) (auto intro: expr_sem.dims_compact[OF law])
    show "edims (collect Es) \<rho> \<sqsubseteq> edims (collect Es) \<bottom>" for \<rho> unfolding collect_simps(2)
      by (rule fold_join_apply_le) (auto intro: expr_sem.dims_bot[OF law])
  qed
qed

end

end
