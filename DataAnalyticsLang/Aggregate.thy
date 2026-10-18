theory Aggregate
  imports Frame
begin

section \<open>Aggregation\<close>

text \<open>An aggregate folds the entries of an inner expression over each fiber of the frame's LOD
  with a commutative semigroup operation.  The fold adjoins a unit for the empty fiber, which
  gives no entry; it is not \<open>\<bottom>\<close>: a monotone operation with unit \<open>\<bottom>\<close> would be inflationary
  (\<open>x = x \<oplus> \<bottom> \<sqsubseteq> x \<oplus> y\<close>), which rules out sums on flat values.\<close>

definition opt_op :: "('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> 'v option \<Rightarrow> 'v option \<Rightarrow> 'v option" where
  "opt_op f a b = (case a of None \<Rightarrow> b | Some x \<Rightarrow> Some (case b of None \<Rightarrow> x | Some y \<Rightarrow> f\<cdot>x\<cdot>y))"

lemma comm_monoid_opt_op:
  assumes "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "comm_monoid (opt_op f) None"
proof -
  interpret abel_semigroup "\<lambda>a b. f\<cdot>a\<cdot>b" by (fact assms)
  show ?thesis
    by standard (auto simp: opt_op_def assoc commute left_commute split: option.splits)
qed

definition agg_fold :: "('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('a \<rightharpoonup> 'v) \<Rightarrow> 'a set \<Rightarrow> 'v option" where
  "agg_fold f v A = comm_monoid_set.F (opt_op f) None v A"

context
  fixes f :: "'v::pcpo \<rightarrow> 'v \<rightarrow> 'v"
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
begin

interpretation A: comm_monoid_set "opt_op f" None
  unfolding comm_monoid_set_def by (rule comm_monoid_opt_op[OF f])

lemma agg_fold_empty: "agg_fold f v {} = None"
  by (simp add: agg_fold_def)

lemma agg_fold_singleton: "agg_fold f v {a} = v a"
  by (simp add: agg_fold_def opt_op_def split: option.splits)

lemma agg_fold_nonempty: "agg_fold f v A \<noteq> None \<Longrightarrow> A \<noteq> {}"
  by (auto simp: agg_fold_empty)

lemma agg_fold_present: "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> v a \<noteq> None \<Longrightarrow> agg_fold f v A \<noteq> None"
  unfolding agg_fold_def by (subst A.remove) (auto simp: opt_op_def)

lemma agg_fold_absent: "(\<And>a. a \<in> A \<Longrightarrow> v a = None) \<Longrightarrow> agg_fold f v A = None"
  unfolding agg_fold_def by (rule A.neutral) simp

lemma agg_fold_cong: "A = B \<Longrightarrow> (\<And>a. a \<in> B \<Longrightarrow> v a = w a) \<Longrightarrow> agg_fold f v A = agg_fold f w B"
  unfolding agg_fold_def by (simp cong: A.cong)

text \<open>Folding over two images of one set of rows, identified alike, with the same entries.\<close>

lemma agg_fold_image_cong:
  assumes "\<And>y z. y \<in> Z \<Longrightarrow> z \<in> Z \<Longrightarrow> g y = g z \<longleftrightarrow> g' y = g' z"
    and "\<And>y. y \<in> Z \<Longrightarrow> v (g y) = w (g' y)"
  shows "agg_fold f v (g ` Z) = agg_fold f w (g' ` Z)"
  unfolding agg_fold_def
proof (rule A.reindex_bij_witness[where i = "\<lambda>b. g (SOME y. y \<in> Z \<and> g' y = b)"
      and j = "\<lambda>a. g' (SOME y. y \<in> Z \<and> g y = a)"])
  fix a assume "a \<in> g ` Z"
  then obtain y where y: "y \<in> Z" "g y = a" by blast
  let ?y = "SOME y. y \<in> Z \<and> g y = a"
  have y': "?y \<in> Z" "g ?y = a" using someI[of "\<lambda>y. y \<in> Z \<and> g y = a", OF conjI[OF y]] by simp_all
  let ?z = "SOME z. z \<in> Z \<and> g' z = g' ?y"
  have z: "?z \<in> Z" "g' ?z = g' ?y" using someI[of "\<lambda>z. z \<in> Z \<and> g' z = g' ?y" ?y] y'(1) by simp_all
  show "g ?z = a" using assms(1)[OF z(1) y'(1)] z(2) y'(2) by simp
  show "g' ?y \<in> g' ` Z" using y'(1) by blast
  show "w (g' ?y) = v a" using assms(2)[OF y'(1)] y'(2) by simp
next
  fix b assume "b \<in> g' ` Z"
  then obtain y where y: "y \<in> Z" "g' y = b" by blast
  let ?y = "SOME y. y \<in> Z \<and> g' y = b"
  have y': "?y \<in> Z" "g' ?y = b" using someI[of "\<lambda>y. y \<in> Z \<and> g' y = b", OF conjI[OF y]] by simp_all
  let ?z = "SOME z. z \<in> Z \<and> g z = g ?y"
  have z: "?z \<in> Z" "g ?z = g ?y" using someI[of "\<lambda>z. z \<in> Z \<and> g z = g ?y" ?y] y'(1) by simp_all
  show "g' ?z = b" using assms(1)[OF z(1) y'(1)] z(2) y'(2) by simp
  show "g ?y \<in> g ` Z" using y'(1) by blast
qed

end

context dataspace
begin

text \<open>The rows of a frame in the fiber of a key at an LOD.\<close>

definition afiber :: "('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "afiber F c k = {y \<in> pts S. frows F y \<and> rproj c y = k}"

text \<open>The aggregate decides no detail of its own (\<open>INCLUDE\<close> adds some); at a key of the frame
  it folds the inner entries at the keys of the fiber's rows.  Through the full mask it reads
  its grouping at the inner expression's minimal LOD.\<close>

definition aggregate ::
    "('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k semi_factor, 'f, 'r, 'k, 'v) expr \<Rightarrow> ('k semi_factor, 'f, 'r, 'k, 'v) expr"
  where "aggregate f E =
    \<lparr>emind = \<bottom>, edims = top_dims (emind E) (edims E),
     esem = \<lambda>F k. agg_fold f (esem E F) (rproj (emind E \<squnion> flod F) ` afiber F (flod F) k)\<rparr>"

lemma aggregate_simps:
  "emind (aggregate f E) = \<bottom>" "edims (aggregate f E) = top_dims (emind E) (edims E)"
  "esem (aggregate f E) F k = agg_fold f (esem E F) (rproj (emind E \<squnion> flod F) ` afiber F (flod F) k)"
  by (simp_all add: aggregate_def)

text \<open>What the aggregate needs: a commutative semigroup operation (continuity is not used yet),
  and keys of data rows compact, so that pegging the frame reaches the inner keys.  The inner
  expression may drop keys: the fold reads the entries present, and there is no entry where the
  whole fiber has none.  The dims law of the inner expression covers its entries, present or
  not, at every row of a fiber.\<close>

theorem lawful_aggregate:
  assumes E: "lawfulE E"
    and f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
    and data_compact: "\<And>y. y \<in> pts S \<Longrightarrow> compact (rkey\<cdot>y)"
  shows "lawfulE (aggregate f E)"
proof -
  interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S "emind E" "edims E" "esem E"
    by (fact E)
  let ?m = "emind E" and ?D = "top_dims (emind E) (edims E)"
  have kd: "\<bottom> \<squnion> X = X" for X :: "'k semi_factor" by (rule lattice_join_bot_left)
  have ne: "afiber F (flod F) k \<noteq> {}" if "esem (aggregate f E) F k \<noteq> None" for F k
    using agg_fold_nonempty[OF f] that by (auto simp: aggregate_simps)
  text \<open>Through the full mask: rows apart at the inner minimal LOD are grouped alike.\<close>
  have P: "rproj (flod F) y = rproj (flod F) z \<longleftrightarrow> rproj (flod F') y = rproj (flod F') z"
    if e: "dims_equivs ?D F x (flod F) (flod F')"
      and yz: "y \<in> insert x (mrows lattice_top F)" "z \<in> insert x (mrows lattice_top F)"
      and n: "rproj ?m y \<noteq> rproj ?m z" for F F' x y z
  proof -
    have "dims_equiv (?D lattice_top) lattice_top F x (flod F) (flod F')"
      by (rule dims_equivsD[OF e])
    then have "dims_equiv ?m lattice_top F x (flod F) (flod F')"
      by (rule dims_equiv_natd_le[OF top_dims_top])
    then have "relspace.equiv_mod (insert x (mrows lattice_top F)) (rproj ?m) (rproj (flod F)) (rproj (flod F'))"
      by (simp add: dims_equiv_def truncate_top)
    with yz n show ?thesis unfolding relspace.equiv_mod_def by blast
  qed
  text \<open>The inner dims hypothesis holds at every row of the frame.\<close>
  have inner: "dims_equivs (edims E) F y (?m \<squnion> flod F) (?m \<squnion> flod F')"
    if e: "dims_equivs ?D F x (flod F) (flod F')" and y: "y = x \<or> (y \<in> pts S \<and> frows F y)"
    for F F' x y
  proof (rule dims_equivsI)
    fix \<rho>
    have "dims_equiv (edims E \<rho>) \<rho> F x (flod F) (flod F')"
      by (rule dims_equiv_natd_le[OF top_dims_ge dims_equivsD[OF e]])
    then have x: "dims_equiv (edims E \<rho>) \<rho> F x (?m \<squnion> flod F) (?m \<squnion> flod F')"
      by (rule dims_equiv_sup[OF subset_refl]) (simp_all add: truncate_sup lattice_join_commute)
    have sub: "insert y (mrows \<rho> F) \<subseteq> insert x (mrows \<rho> F)" using y frows_mrows[of y F \<rho>] by blast
    show "dims_equiv (edims E \<rho>) \<rho> F y (?m \<squnion> flod F) (?m \<squnion> flod F')"
      by (rule dims_equiv_sub_row[OF sub x refl refl])
  qed
  have val: "esem E F (rproj (?m \<squnion> flod F) y) = esem E F' (rproj (?m \<squnion> flod F') y)"
    if a: "amb F = amb F'" "slice F = slice F'" "dims_equivs ?D F x (flod F) (flod F')"
      and y: "y \<in> pts S" "frows F y" for F F' x y
    by (rule E.dims_law[OF a(1,2) y inner[OF a(3)]]) (use y in blast)
  show ?thesis
  proof (rule lawfulI, simp_all only: aggregate_simps(1,2) kd)
    show "keyimg S F (flod F) k" if "esem (aggregate f E) F k \<noteq> None" for F k
      using ne[OF that] by (auto simp: afiber_def keyimg_def)
    show "esem (aggregate f E) (peg K F) K = esem (aggregate f E) F K" if cK: "compact K" for F K
    proof -
      have fib: "afiber (peg K F) (flod F) K = afiber F (flod F) K"
        by (auto simp: afiber_def frows_peg[OF cK] intro: proj_below)
      have v: "esem E (peg K F) \<kappa> = esem E F \<kappa>"
        if kin: "\<kappa> \<in> rproj (?m \<squnion> flod F) ` afiber F (flod F) K" for \<kappa>
      proof -
        obtain y where y: "y \<in> pts S" "rproj (flod F) y = K" and \<kappa>: "\<kappa> = rproj (?m \<squnion> flod F) y"
          using kin unfolding afiber_def by blast
        have "K = proj (flod F)\<cdot>\<kappa>" unfolding \<kappa> y(2)[symmetric] by (simp add: proj_le lattice_join_ge2)
        then have le: "K \<sqsubseteq> \<kappa>" by (simp add: proj_below)
        have c: "compact \<kappa>" unfolding \<kappa> by (rule compact_proj_compact[OF data_compact[OF y(1)]])
        show ?thesis by (rule E.peg_below[OF cK c le])
      qed
      show ?thesis unfolding aggregate_simps flod_peg fib by (rule agg_fold_cong[OF f refl v])
    qed
    show "esem (aggregate f E) F (rproj (flod F) x) = esem (aggregate f E) F' (rproj (flod F') x)"
      if a: "amb F = amb F'" "slice F = slice F'" "x \<in> pts S" "frows F x"
        "dims_equivs ?D F x (flod F) (flod F')" for F F' x
    proof -
      let ?L = "flod F" and ?L' = "flod F'"
      let ?Z = "afiber F ?L (rproj ?L x)" and ?Z' = "afiber F' ?L' (rproj ?L' x)"
      let ?g = "rproj (?m \<squnion> ?L)" and ?g' = "rproj (?m \<squnion> ?L')"
      have fr: "frows F' = frows F" by (rule frows_cong) (simp_all add: a(1,2))
      have Z: "y \<in> ?Z \<longleftrightarrow> y \<in> pts S \<and> frows F y \<and> rproj ?L y = rproj ?L x" for y
        by (simp add: afiber_def)
      have Z': "y \<in> ?Z' \<longleftrightarrow> y \<in> pts S \<and> frows F y \<and> rproj ?L' y = rproj ?L' x" for y
        by (simp add: afiber_def fr)
      have P': "rproj ?L y = rproj ?L z \<longleftrightarrow> rproj ?L' y = rproj ?L' z"
        if "y \<in> insert x (?Z \<union> ?Z')" "z \<in> insert x (?Z \<union> ?Z')" "rproj ?m y \<noteq> rproj ?m z" for y z
        by (rule P[OF a(5) _ _ that(3)]) (use that(1,2) in \<open>auto simp: Z Z' intro: frows_mrows\<close>)
      have val': "esem E F (?g y) = esem E F' (?g' y)" if "y \<in> insert x ?Z" for y
        by (rule val[OF a(1,2,5)]) (use that a(3,4) in \<open>auto simp: Z\<close>)
      show ?thesis
      proof (cases "\<exists>w\<in>?Z. rproj ?m w \<noteq> rproj ?m x")
        case True
        text \<open>Some row of the fiber is apart from \<open>x\<close>: then both fibers have the same rows.\<close>
        then obtain w where w: "w \<in> ?Z" "rproj ?m w \<noteq> rproj ?m x" by blast
        have wZ': "w \<in> ?Z'" using P'[of w x] w by (auto simp: Z Z')
        have ZZ: "?Z' = ?Z"
        proof (intro set_eqI iffI)
          fix z assume z: "z \<in> ?Z'"
          show "z \<in> ?Z"
          proof (cases "rproj ?m z = rproj ?m x")
            case False then show ?thesis using P'[of z x] z by (auto simp: Z Z')
          next
            case True
            then have "rproj ?m z \<noteq> rproj ?m w" using w(2) by simp
            then have "rproj ?L z = rproj ?L w" using P'[of z w] z wZ' by (auto simp: Z')
            then show ?thesis using z w(1) by (auto simp: Z Z')
          qed
        next
          fix z assume z: "z \<in> ?Z"
          show "z \<in> ?Z'"
          proof (cases "rproj ?m z = rproj ?m x")
            case False then show ?thesis using P'[of z x] z by (auto simp: Z Z')
          next
            case True
            then have "rproj ?m z \<noteq> rproj ?m w" using w(2) by simp
            then have "rproj ?L' z = rproj ?L' w" using P'[of z w] z w(1) by (auto simp: Z)
            then show ?thesis using z wZ' by (auto simp: Z Z')
          qed
        qed
        have "agg_fold f (esem E F) (?g ` ?Z) = agg_fold f (esem E F') (?g' ` ?Z)"
        proof (rule agg_fold_image_cong[OF f])
          show "?g y = ?g z \<longleftrightarrow> ?g' y = ?g' z" if "y \<in> ?Z" "z \<in> ?Z" for y z
          proof -
            have "rproj ?L y = rproj ?L z" using that by (simp add: Z)
            moreover have "y \<in> ?Z'" "z \<in> ?Z'" using that by (simp_all only: ZZ)
            then have "rproj ?L' y = rproj ?L' z" by (simp add: Z')
            ultimately show ?thesis by (simp add: rproj_sup_eq)
          qed
          show "esem E F (?g y) = esem E F' (?g' y)" if "y \<in> ?Z" for y
            by (rule val') (simp add: that)
        qed
        then show ?thesis by (simp only: aggregate_simps ZZ)
      next
        case False
        text \<open>All rows of the fiber agree with \<open>x\<close> at the inner minimal LOD: each fold reads
          the entry at the inner key of \<open>x\<close>.\<close>
        then have m: "rproj ?m z = rproj ?m x" if "z \<in> ?Z" for z using that by blast
        have m': "rproj ?m z = rproj ?m x" if "z \<in> ?Z'" for z
        proof (rule ccontr)
          assume n: "rproj ?m z \<noteq> rproj ?m x"
          then have "z \<in> ?Z" using P'[of z x] that by (auto simp: Z Z')
          with n m show False by blast
        qed
        have one: "agg_fold f (esem E G) (rproj (?m \<squnion> flod G) ` afiber G (flod G) (rproj (flod G) x))
                     = esem E G (rproj (?m \<squnion> flod G) x)"
          if mx: "\<And>z. z \<in> afiber G (flod G) (rproj (flod G) x) \<Longrightarrow> rproj ?m z = rproj ?m x"
            and xG: "frows G x"
          for G :: "('k semi_factor, 'f, 'r) frame"
        proof -
          let ?A = "afiber G (flod G) (rproj (flod G) x)"
          have gz: "rproj (?m \<squnion> flod G) z = rproj (?m \<squnion> flod G) x" if "z \<in> ?A" for z
            using mx[OF that] that by (simp add: afiber_def rproj_sup_eq)
          have xA: "x \<in> ?A" using a(3) xG by (simp add: afiber_def)
          have "rproj (?m \<squnion> flod G) ` ?A = {rproj (?m \<squnion> flod G) x}"
          proof (intro set_eqI iffI)
            fix \<kappa> assume "\<kappa> \<in> rproj (?m \<squnion> flod G) ` ?A"
            then show "\<kappa> \<in> {rproj (?m \<squnion> flod G) x}" using gz by blast
          next
            fix \<kappa> assume "\<kappa> \<in> {rproj (?m \<squnion> flod G) x}"
            then show "\<kappa> \<in> rproj (?m \<squnion> flod G) ` ?A" using xA by blast
          qed
          then show ?thesis by (simp add: agg_fold_singleton[OF f])
        qed
        have x': "frows F' x" using a(4) by (simp add: fr)
        have "agg_fold f (esem E F) (?g ` ?Z) = esem E F (?g x)" by (rule one[OF m a(4)])
        moreover have "agg_fold f (esem E F') (?g' ` ?Z') = esem E F' (?g' x)" by (rule one[OF m' x'])
        moreover have "esem E F (?g x) = esem E F' (?g' x)" by (rule val') simp
        ultimately show ?thesis unfolding aggregate_simps by simp
      qed
    qed
    show "esem (aggregate f E) F = esem (aggregate f E) F'"
      if "amb F = amb F'" "slice F = slice F'" "flod F = flod F'" for F F'
    proof -
      have e: "esem E F = esem E F'" by (rule E.eff_law) (simp_all add: that)
      have a: "afiber F = afiber F'"
        using frows_cong[OF that(1,2)] by (simp add: afiber_def fun_eq_iff)
      show ?thesis by (rule ext) (simp only: aggregate_simps e a that(3))
    qed
    show "compact (\<bottom> :: 'k semi_factor)" by simp
    show "compact ?D" by (rule compact_top_dims[OF E.mind_compact E.dims_compact])
    show "?D \<rho> \<sqsubseteq> ?D \<bottom>" for \<rho> by (rule top_dims_bot) (rule E.dims_bot)
  qed
qed

end

end
