ctor be my guest, theory Attr_Space imports HOLCF Bounded_Complete Top begin

default_sort cpo

definition preimage :: "('a \<rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set"
  where "preimage f y = {x. y \<sqsubseteq> f\<cdot>x}"

lemma preimage_antimono1: "y1 \<sqsubseteq> y2 \<Longrightarrow> preimage f y2 \<subseteq> preimage f y1"
  by (auto simp add: preimage_def intro: below_trans)

lemma adm_not_preimage: "compact y \<Longrightarrow> adm (\<lambda>x. x \<notin> preimage f y)"
  by (simp add: preimage_def)

inductive_set minimal_elements :: "'a set \<Rightarrow> 'a set" for A :: "'a set"
  where "x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> y = x) \<Longrightarrow> x \<in> minimal_elements A"

inductive_set up_closure :: "'a set \<Rightarrow> 'a set" for A :: "'a set"
  where "x \<in> A \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> y \<in> up_closure A"

notation up_closure (\<open>(\<open>notation=\<open>prefix \<up>\<close>\<close>\<up>_)\<close> [81]80)

lemma up_closure_iff: "\<up>X = {y. \<exists>x \<in> X. x \<sqsubseteq> y}"
  by (auto simp add: up_closure.simps)

locale proper_map =
  fixes f :: "'a::bifinite \<rightarrow> 'b::bifinite"
  assumes finite_generators:
    "compact y \<Longrightarrow> finite (minimal_elements (preimage f y))"
    and generating: "compact y \<Longrightarrow> preimage f y = \<up>(minimal_elements (preimage f y))"
begin

abbreviation "generators y \<equiv> minimal_elements (preimage f y)"


lemma generating_point:
"compact y \<Longrightarrow> y \<sqsubseteq> f\<cdot>x \<longleftrightarrow> (\<exists>x0 \<in> generators y. x0 \<sqsubseteq> x)"
  using generating preimage_def up_closure_iff by blast

lemma generator_aux: assumes "x \<in> generators y" shows "x' \<sqsubseteq> x \<Longrightarrow> x' \<noteq> x \<Longrightarrow> x' \<notin> preimage f y"
  using assms by (cases x rule: minimal_elements.cases) auto

lemma compact_generator:
  assumes y: "compact y" and x: "x \<in> generators y"
  shows "compact x"
proof (rule classical)
  assume noncompact: "\<not>compact x"
  obtain X where "chain X" "\<forall>i. compact (X i)" and x_lub: "x = (\<Squnion>i. X i)"
    by (rule obtain_compact_chain)
  then have "X i \<sqsubseteq> x" for i using is_ub_thelub[OF \<open>chain X\<close>] by simp
  moreover from noncompact \<open>\<forall>i. compact (X i)\<close> have "X i \<noteq> x" for i by auto
  ultimately have 1: "X i \<notin> preimage f y" for i by (rule generator_aux[OF x])
  have 2: "adm (\<lambda>x. x \<notin> preimage f y)" by (simp add: adm_not_preimage[OF y])
  from 2 \<open>chain X\<close> 1 have "(\<Squnion>i. X i) \<notin> preimage f y" by (rule admD)
  then have "x \<notin> preimage f y" by (simp add: x_lub)
  moreover from x have "x \<in> preimage f y" by (cases x)
  ultimately show ?thesis by contradiction
qed

abbreviation (input) "upper_un \<equiv> Rep_cfun upper_unit"

definition finite_upper_model :: "'a set \<Rightarrow> 'a upper_pd"
  where "finite_upper_model A = semilattice_set.F upper_add (upper_un ` A)"

lemma finite_upper_model_induct[case_names singleton union, consumes 2]:
  assumes A: "finite A" "A \<noteq> {}"
and singletonI: "\<And>x. x \<in> A \<Longrightarrow> P {x}\<sharp>"
and unionI: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> P (x \<union>\<sharp> y)"
shows "P (finite_upper_model A)"
proof -
  interpret semilattice_set upper_add ..
  have "A \<subseteq> A" ..
  from \<open>finite A\<close> \<open>A \<subseteq> A\<close> \<open>A \<noteq> {}\<close> show ?thesis
  proof (induction A rule: finite_subset_induct)
    case empty
    then show ?case by simp
  next
    case (insert a F)
    then show ?case
    proof (cases F)
      case emptyI
      then have "insert a F = {a}" by simp
      also have "finite_upper_model {a} = {a}\<sharp>"
        by (simp add: finite_upper_model_def)
      finally show ?thesis by (simp add: singletonI[OF \<open>a \<in> A\<close>])
    next
      case insertI
      then have "F \<noteq> {}" by simp
      then have 1: "P (finite_upper_model F)" by (rule insert.IH)
      from \<open>finite F\<close> \<open>F \<noteq> {}\<close> have "finite_upper_model (insert a F) = {a}\<sharp> \<union>\<sharp> finite_upper_model F"
        by (simp add: finite_upper_model_def)
      with 1 singletonI[OF \<open>a \<in> A\<close>] unionI show ?thesis by auto
    qed
  qed
qed

lemma finite_upper_model:
  assumes "finite A" and "A \<noteq> {}"
  shows "x \<in> \<up>A \<longleftrightarrow> finite_upper_model A \<sqsubseteq> {x}\<sharp>"
proof -
  interpret semilattice_set upper_add ..
  from assms show ?thesis
  proof (induction A rule: finite_ne_induct)
    case (singleton p)
    have "finite_upper_model {p} = {p}\<sharp>"
      by (simp add: finite_upper_model_def)
    then show ?case unfolding up_closure_iff by simp
  next
    case (insert p F)
    then have "finite (upper_un ` F)" "upper_un ` F \<noteq> {}" by simp_all
    moreover have "upper_un ` (insert p F) = insert {p}\<sharp> (upper_un ` F)" by auto
    ultimately have "finite_upper_model (insert p F) = {p}\<sharp> \<union>\<sharp> finite_upper_model F"
      unfolding finite_upper_model_def by simp
    then have "finite_upper_model (insert p F) \<sqsubseteq> {x}\<sharp> \<longleftrightarrow> p \<sqsubseteq> x \<or> finite_upper_model F \<sqsubseteq> {x}\<sharp>"
      by simp
    moreover have "x \<in> \<up>(insert p F) \<longleftrightarrow> p \<sqsubseteq> x \<or> x \<in> \<up>F" unfolding up_closure_iff
      by auto
    ultimately show ?case using insert.IH by simp
  qed
qed


lemma generators_finite_ne:
  assumes "preimage f y \<noteq> {}" "compact y"
  shows "finite (generators y)" "generators y \<noteq> {}"
proof -
  from assms(2) finite_generators show "finite (generators y)" by simp
  from assms generating have "\<up>(generators y) \<noteq> {}" by simp
  then show "generators y \<noteq> {}" by (auto elim: up_closure.cases)
qed

definition compact_upper_model :: "'b compact_basis \<Rightarrow> 'a upper_pd"
  where "compact_upper_model y = finite_upper_model (generators (Rep_compact_basis y))"

lemma compact_upper_model:
  assumes "preimage f (Rep_compact_basis y) \<noteq> {}"
  shows "x \<in> preimage f (Rep_compact_basis y) \<longleftrightarrow> compact_upper_model y \<sqsubseteq> {x}\<sharp>"
proof -
  define yy where "yy \<equiv> Rep_compact_basis y"
  from assms have "preimage f yy \<noteq> {}"  "compact yy" by (simp_all add: yy_def)
  from generators_finite_ne[OF this]
  have "x \<in> \<up>(generators yy) \<longleftrightarrow> compact_upper_model y \<sqsubseteq> {x}\<sharp>"
    by (simp add: compact_upper_model_def yy_def finite_upper_model)
  with generating show ?thesis by (simp add: yy_def)
qed

lemma compact_upper_model_mono:
  assumes ne: "preimage f (Rep_compact_basis y2) \<noteq> {}"
    and mono: "y1 \<sqsubseteq> y2"
  shows "compact_upper_model y1 \<sqsubseteq> compact_upper_model y2"
proof -
  define yy where "yy = Rep_compact_basis y1"
  define yy2 where "yy2 = Rep_compact_basis y2"
  from mono have mono': "yy \<sqsubseteq> yy2" by (simp add: yy_def yy2_def)
  from mono' have preimage_mono: "preimage f yy2 \<subseteq> preimage f yy" by (rule preimage_antimono1)
  have x_in: "x \<in> preimage f yy" if "x \<in> generators yy2" for x
    using that by (cases x) (auto intro: preimage_mono[THEN subsetD])
  have *: "preimage f yy2 \<noteq> {}" "compact yy2"
    by (simp_all add: ne yy2_def)
  from *(1) preimage_mono have "preimage f yy \<noteq> {}" by auto
  then have "x \<in> preimage f yy \<longleftrightarrow> compact_upper_model y1 \<sqsubseteq> {x}\<sharp>" for x
    unfolding yy_def by (rule compact_upper_model)
  with x_in have singl: "x \<in> generators yy2 \<Longrightarrow> compact_upper_model y1 \<sqsubseteq> {x}\<sharp>" for x
    by blast
  from generators_finite_ne[OF *]
  have "compact_upper_model y1 \<sqsubseteq> finite_upper_model (generators yy2)"
  by (induction rule: finite_upper_model_induct) (simp_all add: singl)
  then show ?thesis unfolding compact_upper_model_def yy2_def .
qed

definition "compact_upper_model' y \<equiv>
  if preimage f (Rep_compact_basis y) = {} then Top else down\<cdot>(compact_upper_model y)"

lemma compact_upper_model':
"x \<in> preimage f (Rep_compact_basis y) \<longleftrightarrow> (compact_upper_model' y) \<sqsubseteq> down\<cdot>{x}\<sharp>"
proof (cases "preimage f (Rep_compact_basis y) = {}")
  assume "preimage f (Rep_compact_basis y) = {}"
  then show ?thesis by (simp add: compact_upper_model'_def)
next
  assume *: "preimage f (Rep_compact_basis y) \<noteq> {}"
  from * have 1: "compact_upper_model' y = down\<cdot>(compact_upper_model y)"
    by (simp add: compact_upper_model'_def)
  from * have 2: "x \<in> preimage f (Rep_compact_basis y) \<longleftrightarrow> compact_upper_model y \<sqsubseteq> {x}\<sharp>"
    by (rule compact_upper_model)
  from 1 2 show ?thesis by simp
qed

lemma compact_upper_model'_mono:
  assumes "y1 \<sqsubseteq> y2"
  shows "compact_upper_model' y1 \<sqsubseteq> compact_upper_model' y2"
proof cases
  assume  "preimage f (Rep_compact_basis y2) = {}"
  then show ?thesis by (simp add: compact_upper_model'_def)
next
  assume 1: "preimage f (Rep_compact_basis y2) \<noteq> {}"
  then have 2: "preimage f (Rep_compact_basis y1) \<noteq> {}"
    using assms preimage_antimono1[of "Rep_compact_basis y1" "Rep_compact_basis y2"]
    by auto
  from 1 assms have 3: "compact_upper_model y1 \<sqsubseteq> compact_upper_model y2"
    by (rule compact_upper_model_mono)
  from 1 2 3 show ?thesis by (simp add: compact_upper_model'_def)
qed

definition "upper_model' \<equiv> compact_basis.extension compact_upper_model'"

lemma upper_model'_principal:
  "upper_model'\<cdot>(Rep_compact_basis y) = compact_upper_model' y"
  unfolding upper_model'_def
  by (fast intro: compact_upper_model'_mono compact_basis.extension_principal)


lemma upper_model':
"x \<in> preimage f y \<longleftrightarrow> upper_model'\<cdot>y \<sqsubseteq> down\<cdot>{x}\<sharp>"
proof (induct y rule: compact_basis.principal_induct)
  case 1
  then show ?case by (simp add: preimage_def)
next
  case (2 a)
  then show ?case by (simp add: upper_model'_principal compact_upper_model')
qed

lemma upper_model'_below:
"y \<sqsubseteq> f\<cdot>x  \<longleftrightarrow> upper_model'\<cdot>y \<sqsubseteq> down\<cdot>{x}\<sharp>"
  using upper_model'[unfolded preimage_def] by simp

lemma upper_model_empty:
  "preimage f y = {} \<longleftrightarrow> upper_model'\<cdot>y = Top"
proof -
  have "preimage f y = {} \<longleftrightarrow> (\<forall>x. x \<notin> preimage f y)" by simp
  also have "(\<forall>x. x \<notin> preimage f y) \<longleftrightarrow> upper_model'\<cdot>y = Top"
    unfolding upper_model'
  proof (rule iffI, cases "upper_model'\<cdot>y")
    fix p
    assume "\<forall>x. \<not>(upper_model'\<cdot>y \<sqsubseteq> down\<cdot>{x}\<sharp>)" "upper_model'\<cdot>y = down\<cdot>p"
    with upper_pd_has_point[of p] show "upper_model'\<cdot>y = Top" by simp
  qed auto
  finally show ?thesis .
qed

end

lemma minimal_elements_up:
"minimal_elements (\<up>X) = minimal_elements X"
  apply (rule set_eqI)
  apply (auto simp add: minimal_elements.simps up_closure_iff)
  using below_trans below_antisym by metis

lemma minimal_elements_Un:
"minimal_elements (A \<union> B) \<subseteq> minimal_elements A \<union> minimal_elements B"
  by (auto simp add: minimal_elements.simps)

lemma minimal_elements_subset: "minimal_elements A \<subseteq> A"
  by (auto elim: minimal_elements.cases)

lemma up_closure_mono: "A \<subseteq> B \<Longrightarrow> \<up>A \<subseteq> \<up>B"
  by (rule subsetI) (force simp add: up_closure_iff)

lemma up_closure_subset: "A \<subseteq> \<up>A" by (auto simp add: up_closure_iff)

lemma up_closure_idem: "\<up>(\<up>A) = \<up>A"
proof (intro subset_antisym)
  show "\<up>A \<subseteq> \<up>(\<up>A)" by (rule up_closure_subset)
  show "\<up>(\<up>A) \<subseteq> \<up>A"
    apply (rule subsetI)
    apply (simp add: up_closure_iff)
    by (blast dest: below_trans)
qed

lemma up_closure_empty[simp]: "\<up>{} = {}"
  by (auto simp add: up_closure_iff)

lemma up_closure_insert: "y \<in> \<up>(insert x F) \<longleftrightarrow> x \<sqsubseteq> y \<or> y \<in> \<up>F"
  unfolding up_closure_iff by blast

lemma minimal_elements_insert: "y \<in> minimal_elements F \<Longrightarrow> x \<sqsubseteq> y \<or> y \<in> minimal_elements (insert x F)"
  by (blast intro: minimal_elements.intros elim: minimal_elements.cases)

lemma up_closure_minimal:
"\<up>minimal_elements X = \<up>X" if "finite X"
proof (rule subset_antisym)
  have "minimal_elements X \<subseteq> X" by (rule minimal_elements_subset)
  then show "\<up>minimal_elements X \<subseteq> \<up>X" by (rule up_closure_mono)
next
  show "\<up>X \<subseteq> \<up>minimal_elements X"
    using that 
  proof (induction X)
    case empty
    then show ?case by simp
  next
    case (insert x F)
    show ?case 
    proof (cases "x \<in> \<up>F")
      case True
      from True have 1: "\<up>(insert x F) = \<up>F" 
        apply (intro set_eqI)
        apply (simp add: up_closure_insert)
        by (blast intro: up_closure.intros below_trans elim: up_closure.cases)
      from True have 2: "minimal_elements (insert x F) = minimal_elements F"
        apply (intro set_eqI)
        apply (simp add: minimal_elements.simps up_closure_iff)
        by (blast intro: below_trans below_antisym)
      from 1 2 insert.IH show ?thesis by simp
    next
      case False
      then have excl: "y \<sqsubseteq> x \<Longrightarrow> y \<notin> F" for y using up_closure.intros by blast
      then have xmin: "x \<in> minimal_elements (insert x F)"
        apply (intro minimal_elements.intros)
         apply simp
        using excl by blast
      show ?thesis
      proof (intro subsetI, simp only: up_closure_insert)
        fix y assume "x \<sqsubseteq> y \<or> y \<in> \<up>F"
        then consider "x \<sqsubseteq> y" | "y \<in> \<up>F" by iprover
        then show "y \<in> \<up>minimal_elements (insert x F)"
        proof (cases)
          case 1
          with xmin show ?thesis by (rule up_closure.intros) 
        next
          case 2
          with insert.IH have "y \<in> \<up>minimal_elements F" by auto
          then obtain y0 where "y0 \<sqsubseteq> y" "y0 \<in> minimal_elements F"
            by (cases y) iprover
          then consider "x \<sqsubseteq> y0" | "y0 \<in> minimal_elements (insert x F)"
            using minimal_elements_insert by blast
          then show ?thesis
            apply (cases)
            using xmin below_trans[of x y0 y] \<open>y0 \<sqsubseteq> y\<close> up_closure.intros apply blast
            using \<open>y0 \<sqsubseteq> y\<close> up_closure.intros apply blast
            .
        qed
      qed
    qed
  qed
qed

default_sort bifinite

definition "finite_up_closure A \<equiv> \<exists>F. finite F \<and> A = \<up>F"

theorem proper_mapI:
  assumes "\<And>y::'b::bifinite. compact y \<Longrightarrow> finite_up_closure (preimage f y)"
  shows "proper_map f"
proof
  fix y::'b assume "compact y"
  from assms[OF this] obtain F where F: "finite F" and preimage: "preimage f y = \<up>F"
    unfolding finite_up_closure_def
    by fast
  from preimage have 1: "minimal_elements (preimage f y) = minimal_elements F"
    using minimal_elements_up by simp
  also have "\<up>minimal_elements F = \<up>F" using F by (rule up_closure_minimal)
  also note preimage[symmetric]
  finally show "preimage f y = \<up>minimal_elements (preimage f y)" ..
  from F minimal_elements_subset show "finite (minimal_elements (preimage f y))"
    unfolding 1 by (rule rev_finite_subset)
qed

lemma (in proper_map) finite_up_closure: "compact y \<Longrightarrow> finite_up_closure (preimage f y)"
  unfolding finite_up_closure_def
  using finite_generators generating by fast

lemma proper_map_comp:
  assumes f: "proper_map (f::'b\<rightarrow>'c)" and g: "proper_map (g::'a\<rightarrow>'b)"
  shows "proper_map (f oo g)"
proof (rule proper_mapI)
  interpret f: proper_map f by fact
  interpret g: proper_map g by fact
  fix y :: 'c assume "compact y"
  define Z where "Z = f.generators y"
  from \<open>compact y\<close> have 1: "y \<sqsubseteq> f\<cdot>z \<longleftrightarrow> (\<exists>z0 \<in> Z. z0 \<sqsubseteq> z)" for z
    unfolding Z_def by (rule f.generating_point)
  from \<open>compact y\<close> have 2: "z0 \<in> Z \<Longrightarrow> compact z0" for z0
    unfolding Z_def by (rule f.compact_generator)
  from 1 have 3: "y \<sqsubseteq> f\<cdot>(g\<cdot>x) \<longleftrightarrow> (\<exists>z0 \<in> Z. z0 \<sqsubseteq> g\<cdot>x)" for x .
  define X where "X z = g.generators z" for z
  from 2 3 have 4: "y \<sqsubseteq> f\<cdot>(g\<cdot>x) \<longleftrightarrow> (\<exists>z0 \<in> Z. \<exists>x0 \<in> X z0. x0 \<sqsubseteq> x)" for x
    unfolding X_def
    using g.generating_point by blast
  then have "x \<in> preimage (f oo g) y \<longleftrightarrow> x \<in> \<up>(\<Union>z0 \<in> Z. X z0)" for x
    by (auto simp add: preimage_def up_closure_iff)
  then have preimage: "preimage (f oo g) y = \<up>\<Union>(X ` Z)" by (rule set_eqI)
  have "finite Z" unfolding Z_def using \<open>compact y\<close> by (rule f.finite_generators)
  moreover have "z \<in> Z \<Longrightarrow> finite (X z)" for z
    unfolding X_def using 2[THEN g.finite_generators] .
  ultimately have f1: "finite (\<Union>(X ` Z))" by auto
  from f1 preimage show "finite_up_closure (preimage (f oo g) y)"
    unfolding finite_up_closure_def
    by blast
qed

lemma up_closure_singleton[simp]: "\<up>{x} = {z. x \<sqsubseteq> z}"
  by (simp add: up_closure_iff)

lemma finite_up_closure_UNIV_I[simp]:
  "finite_up_closure (UNIV::'a::pcpo set)"
  unfolding finite_up_closure_def
  by (rule exI [of _ "{\<bottom>}"]) simp

lemma finite_up_closure_principalI[simp]:
  "finite_up_closure {x. y \<sqsubseteq> x}"
  unfolding finite_up_closure_def
  by (rule exI[of _ "{y}"]) simp

lemma finite_up_closure_emptyI[simp]:
  "finite_up_closure {}"
  unfolding finite_up_closure_def
  by (rule exI[of _ "{}"]) simp

named_theorems proper_map_rules

theorem proper_map_const[proper_map_rules]: "proper_map (\<Lambda> x. c)" (is "proper_map ?f")
proof (rule proper_mapI)
  fix y::'b assume "compact y"
  have "preimage ?f y = (if y \<sqsubseteq> c then UNIV else {})"
    unfolding preimage_def by simp
  then show "finite_up_closure (preimage ?f y)" by simp
qed

corollary proper_map_bot[proper_map_rules]: "proper_map \<bottom>"
  unfolding LAM_strict[symmetric]
  by (rule proper_map_const)

theorem proper_map_ID[proper_map_rules]: "proper_map ID"
proof (rule proper_mapI)
  fix y :: 'b
  have *: "preimage ID y = {x. y \<sqsubseteq> x}" by (simp add: preimage_def)
  then show "finite_up_closure (preimage ID y)" by simp
qed

text \<open>Step functions (@{const stepfn}) live in \<open>Definitions\<close>.\<close>


lemma proper_map_app[proper_map_rules]: assumes "compact c" shows "proper_map (\<Lambda> f. f\<cdot>c)"
proof (rule proper_mapI)
  fix y :: 'b assume "compact y"
  have "preimage (\<Lambda> f. f\<cdot>c) y = {f. stepfn c y \<sqsubseteq> f}"
    unfolding preimage_def
    by (simp add: stepfn_below_iff[OF assms])
  then show "finite_up_closure (preimage (\<Lambda> f. f\<cdot>c) y)"
    by simp
qed

theorem compact_proper_map[proper_map_rules]: assumes "compact f" shows "proper_map f"
proof (rule proper_mapI)
  from bifinite approx_chain_cfun_map[THEN approx_chain.compact_eq_approx]
    \<open>compact f\<close>
  obtain a :: "nat \<Rightarrow> 'a \<rightarrow> 'a"
    and b :: "nat \<Rightarrow> 'b \<rightarrow> 'b"
    and i :: nat where "approx_chain a" "approx_chain b" and f: "cfun_map\<cdot>(a i)\<cdot>(b i)\<cdot>f = f"
    by metis
  define da where "da \<equiv> a i"
  then interpret da: finite_deflation da
    using \<open>approx_chain a\<close>[THEN approx_chain.finite_deflation_approx]
    by simp
  define db where "db \<equiv> b i"
  then interpret db: finite_deflation db
    using \<open>approx_chain b\<close>[THEN approx_chain.finite_deflation_approx]
    by simp
  from f have "cfun_map\<cdot>da\<cdot>db\<cdot>f\<cdot>x = f\<cdot>x" for x by (simp add: da_def db_def)
  then have app: "db\<cdot>(f\<cdot>(da\<cdot>x)) = f\<cdot>x" for x using cfun_map_beta by simp
  have f_defl: "f\<cdot>(da\<cdot>x) = f\<cdot>x" for x
  proof (rule below_antisym)
    have "da\<cdot>x \<sqsubseteq> x" by (rule da.below)
    then show "f\<cdot>(da\<cdot>x) \<sqsubseteq> f\<cdot>x" by (rule monofun_cfun_arg)
    show "f\<cdot>x \<sqsubseteq> f\<cdot>(da\<cdot>x)" by (rule db.below[of "f\<cdot>(da\<cdot>x)", unfolded app])
  qed

  fix y
  have preimage_defl: "preimage f y = \<up>{x \<in> range (\<lambda>x. da\<cdot>x). y \<sqsubseteq> f\<cdot>x}"
    unfolding preimage_def up_closure_iff
  proof (intro set_eqI, clarsimp, intro iffI)
    fix x assume "y \<sqsubseteq> f\<cdot>x"
    then have "y \<sqsubseteq> f\<cdot>(da\<cdot>x) \<and> da\<cdot>x \<sqsubseteq> x" by (simp add: f_defl da.below)
    then show "\<exists>x2. y \<sqsubseteq> f\<cdot>(da\<cdot>x2) \<and> da\<cdot>x2 \<sqsubseteq> x" ..
  next
    fix x assume "\<exists>x2. y \<sqsubseteq> f\<cdot>(da\<cdot>x2) \<and> da\<cdot>x2 \<sqsubseteq> x"
    then show "y \<sqsubseteq> f\<cdot>x" using monofun_cfun_arg below_trans by blast
  qed
  moreover have "finite {x \<in> range (\<lambda>x. da\<cdot>x). y \<sqsubseteq> f\<cdot>x}"
    using da.finite_range by force
  ultimately show "finite_up_closure (preimage f y)"
    unfolding finite_up_closure_def by blast
qed

lemma projection_preimage:
  assumes "ep_pair e p"
  shows "y \<sqsubseteq> p\<cdot>x \<longleftrightarrow> e\<cdot>y \<sqsubseteq> x"
proof
  interpret ep_pair e p by fact
  {
    assume "y \<sqsubseteq> p\<cdot>x" 
    then have "e\<cdot>y \<sqsubseteq> e\<cdot>(p\<cdot>x)" by (rule monofun_cfun_arg)
    then show "e\<cdot>y \<sqsubseteq> x" using e_p_below below_trans by blast
  }
  {
    assume "e\<cdot>y \<sqsubseteq> x"
    then have "p\<cdot>(e\<cdot>y) \<sqsubseteq> p\<cdot>x" by (rule monofun_cfun_arg)
    then show "y \<sqsubseteq> p\<cdot>x" by simp
  }
qed

theorem projection_proper_map[proper_map_rules]:
  assumes "ep_pair e (p :: 'a \<rightarrow> 'b)"
  shows "proper_map p"
proof (rule proper_mapI)
  fix y ::'b
  have "preimage p y = {x. e\<cdot>y \<sqsubseteq> x}"
    unfolding preimage_def
    using projection_preimage[OF assms] by blast
  then show "finite_up_closure (preimage p y)" by simp
qed

corollary proper_map_iso[proper_map_rules]:
  assumes "\<And>x. f\<cdot>(g\<cdot>x) = x" "\<And>x. g\<cdot>(f\<cdot>x) = x"
  shows "proper_map f"
proof -
  from assms have "ep_pair g f" by (simp add: ep_pair_def)
  then show ?thesis by (rule projection_proper_map)
qed

theorem sinl_proper_map[proper_map_rules]:
  "proper_map sinl"
proof (rule proper_mapI)
  fix y :: "'a \<oplus> 'b"
  show "finite_up_closure (preimage sinl y)"
    by (cases y) (auto simp add: preimage_def)
qed

theorem sinr_proper_map[proper_map_rules]:
  "proper_map sinr"
proof (rule proper_mapI)
  fix y :: "'b \<oplus> 'a"
  show "finite_up_closure (preimage sinr y)"
    by (cases y) (auto simp add: preimage_def)
qed

lemma finite_up_closure_setimage:
  assumes A: "finite_up_closure A"
    and f_unbounded: "\<And>x y. x \<in> A \<Longrightarrow> f\<cdot>x \<sqsubseteq> y \<Longrightarrow> (\<exists>z. x \<sqsubseteq> z \<and> y = f\<cdot>z)"
  shows "finite_up_closure {f\<cdot>x | x. x \<in> A}"
proof -
  from A[unfolded finite_up_closure_def]
  obtain F where "finite F" "A = \<up>F" by blast
  from \<open>A = \<up>F\<close> have f2a: "x \<in> F \<Longrightarrow> x \<in> A" for x using up_closure_subset by blast
  have "{f\<cdot>x | x. x \<in> A} = \<up>{f\<cdot>x | x. x \<in> F}"
  proof (intro subset_antisym subsetI; clarsimp)
    fix x assume "x \<in> A"
    with \<open>A = \<up>F\<close> up_closure.cases obtain x0 where x0: "x0 \<in> F" "x0 \<sqsubseteq> x"
      by metis
    from x0(1) have "f\<cdot>x0 \<in> {f\<cdot>x | x. x \<in> F}" by auto
    moreover from x0(2) have "f\<cdot>x0 \<sqsubseteq> f\<cdot>x" by (rule monofun_cfun_arg)
    ultimately show "f\<cdot>x \<in> \<up>{f\<cdot>x | x. x \<in> F}" by (blast intro: up_closure.intros)
  next
    fix y assume "y \<in> \<up>{f\<cdot>x | x. x \<in> F}"
    then obtain x0 where "x0 \<in> F" "f\<cdot>x0 \<sqsubseteq> y" by (cases y) auto
    with f2a[THEN f_unbounded] obtain z where "x0 \<sqsubseteq> z" "y = f\<cdot>z" by blast
    from \<open>x0 \<sqsubseteq> z\<close> \<open>x0 \<in> F\<close> \<open>A = \<up>F\<close> have "z \<in> A" by (blast intro: up_closure.intros)
    with \<open>y = f\<cdot>z\<close> show "\<exists>z. y = f\<cdot>z \<and> z \<in> A" by blast
  qed
  moreover from \<open>finite F\<close> have "finite {f\<cdot>x | x. x \<in> F}" by force
  ultimately show ?thesis unfolding finite_up_closure_def by blast
qed

lemma finite_up_closure_Un:
"finite_up_closure A \<Longrightarrow> finite_up_closure B \<Longrightarrow> finite_up_closure (A \<union> B)"
  unfolding finite_up_closure_def up_closure_iff by auto


theorem sscase_proper_map:
  assumes strict: "f\<cdot>\<bottom> = \<bottom>" "g\<cdot>\<bottom> = \<bottom>"
  assumes proper: "proper_map (f :: 'a \<rightarrow> 'c)" "proper_map (g :: 'b \<rightarrow> 'c)"
  shows "proper_map (sscase\<cdot>f\<cdot>g)"
proof (rule proper_mapI)
  interpret f: proper_map f by fact
  interpret g: proper_map g by fact

  fix y :: 'c assume "compact y"
  show "finite_up_closure (preimage (sscase\<cdot>f\<cdot>g) y)"
  proof (cases)
    assume "y = \<bottom>"
    then have "preimage (sscase\<cdot>f\<cdot>g) y = UNIV" by (simp add: preimage_def)
    then show ?thesis by simp
  next
    assume y: "y \<noteq> \<bottom>"
    from y strict(1) have strict_a: "a \<in> preimage f y \<Longrightarrow> a \<noteq> \<bottom>" for a
      unfolding preimage_def by fastforce
    from y strict(2) have strict_b: "b \<in> preimage g y \<Longrightarrow> b \<noteq> \<bottom>" for b
      unfolding preimage_def by fastforce
    {
      fix x assume "x \<in> preimage (sscase\<cdot>f\<cdot>g) y"
      then have le: "y \<sqsubseteq> sscase\<cdot>f\<cdot>g\<cdot>x" by (simp add: preimage_def)
      with y have x: "x \<noteq> \<bottom>" by fastforce
      {
        fix a assume a: "a \<noteq> \<bottom>" "x = sinl\<cdot>a"
        with a have "sscase\<cdot>f\<cdot>g\<cdot>x = f\<cdot>a" by simp
        with le have "a \<in> preimage f y"
          by (simp add: preimage_def)
      }
      note 1 = this
      {
        fix b assume b: "b \<noteq> \<bottom>" "x = sinr\<cdot>b"
        with b have "sscase\<cdot>f\<cdot>g\<cdot>x = g\<cdot>b" by simp
        with le have "b \<in> preimage g y"
          by (simp add: preimage_def)
      }
      note 2 = this
      have "x \<in> {sinl\<cdot>a | a. a \<in> preimage f y} \<union>
        {sinr\<cdot>b | b. b \<in> preimage g y}"
        by (cases x) (simp_all add: x 1 2)
    }
    note fwd = this
    {
      fix x :: "'a \<oplus> 'b" and a assume x: "x = sinl\<cdot>a" and a: "a \<in> preimage f y"
      with strict_a x have "sscase\<cdot>f\<cdot>g\<cdot>x = f\<cdot>a" by simp
      with a have "x \<in> preimage (sscase\<cdot>f\<cdot>g) y" by (simp add: preimage_def)
    }
    note bwda = this
    {
      fix x :: "'a \<oplus> 'b" and b assume x: "x = sinr\<cdot>b" and b: "b \<in> preimage g y"
      with strict_b x have "sscase\<cdot>f\<cdot>g\<cdot>x = g\<cdot>b" by simp
      with b have "x \<in> preimage (sscase\<cdot>f\<cdot>g) y" by (simp add: preimage_def)
    }
    note bwdb = this
    from fwd bwda bwdb have Un: "preimage (sscase\<cdot>f\<cdot>g) y =
      {sinl\<cdot>a | a. a \<in> preimage f y} \<union> {sinr\<cdot>b | b. b \<in> preimage g y}"
      by blast
    from f.finite_up_closure[OF \<open>compact y\<close>]
    have fca: "finite_up_closure {sinl\<cdot>a | a. a \<in> preimage f y}"
    proof (rule finite_up_closure_setimage)
      fix a assume "a \<in> preimage f y"
      then have "a \<noteq> \<bottom>" by (rule strict_a)
      then show "sinl\<cdot>a \<sqsubseteq> x \<Longrightarrow> \<exists>a'. a \<sqsubseteq> a' \<and> x = sinl\<cdot>a'" for x
        by (cases x) auto
    qed
    from g.finite_up_closure[OF \<open>compact y\<close>]
    have fcb: "finite_up_closure {sinr\<cdot>b | b. b \<in> preimage g y}"
    proof (rule finite_up_closure_setimage)
      fix b assume "b \<in> preimage g y"
      then have "b \<noteq> \<bottom>" by (rule strict_b)
      then show "sinr\<cdot>b \<sqsubseteq> x \<Longrightarrow> \<exists>b'. b \<sqsubseteq> b' \<and> x = sinr\<cdot>b'" for x
        by (cases x) auto
    qed
    from finite_up_closure_Un[OF fca fcb] Un
    show "finite_up_closure (preimage (sscase\<cdot>f\<cdot>g) y)"
      by presburger
  qed
qed

corollary sleft_proper_map[proper_map_rules]:
  "proper_map (sscase\<cdot>ID\<cdot>\<bottom>)"
  by (rule sscase_proper_map) (simp_all add: proper_map_bot proper_map_ID)

corollary sright_proper_map[proper_map_rules]:
  "proper_map (sscase\<cdot>\<bottom>\<cdot>ID)"
  by (rule sscase_proper_map) (simp_all add: proper_map_bot proper_map_ID)

theorem proper_map_LAM[proper_map_rules]:
  assumes cont: "cont g"
  assumes proper: "proper_map f" "proper_map (\<Lambda> x. g x)"
  shows "proper_map (\<Lambda> x. f\<cdot>(g x))"
proof -
  have "(\<Lambda> x. f\<cdot>(g x)) = f oo (\<Lambda> x. g x)"
    by (rule cfun_eqI) (simp add: cont)
  with proper_map_comp[OF proper] show ?thesis by presburger
qed

theorem proper_map_LAM_ID[proper_map_rules]:
  "proper_map (\<Lambda> x. x)"
  by (simp add: proper_map_ID ID_def[symmetric])

theorem proper_map_finite: "proper_map (f :: 'a::{finite,bifinite} \<rightarrow> 'b)"
proof (rule proper_mapI)
  have "preimage f y = \<up>preimage f y" for y
    unfolding preimage_def up_closure_iff
    by (auto intro: below_trans monofun_cfun_arg)
  then show "finite_up_closure (preimage f y)" for y
    unfolding finite_up_closure_def by auto
qed

section \<open>Attribute space\<close>
type_synonym ('a, 'b) attrs = "('a \<rightarrow> 'b) \<Rightarrow> 'b"


definition models :: "('a, 'b) attrs \<Rightarrow> 'a \<Rightarrow> bool"
  where "models a q \<equiv> \<forall>f \<in> Collect proper_map. a f \<sqsubseteq> f\<cdot>q"

lemma models_antimono: "a1 \<sqsubseteq> a2 \<Longrightarrow> models a2 q \<Longrightarrow> models a1 q"
  unfolding models_def below_fun_def by (auto intro: below_trans)

abbreviation attr_model where "attr_model a f \<equiv> proper_map.upper_model' f\<cdot>(a f)"

definition modelset :: "('a, 'b) attrs \<Rightarrow> ('a)\<sharp> top"
  where "modelset a \<equiv> \<Squnion>f \<in> Collect proper_map. attr_model a f"

lemma modelset_lub:
  "(attr_model a) ` (Collect proper_map) <<| modelset a"
  unfolding modelset_def
  by (rule top_bounded_lub) (auto intro: proper_map_bot)

lemma modelset:
  "models a q \<longleftrightarrow> modelset a \<sqsubseteq> down\<cdot>{q}\<sharp>"
proof -
  from modelset_lub
  thm lub_below_iff_b
  have "modelset a \<sqsubseteq> down\<cdot>{q}\<sharp> \<longleftrightarrow> (\<forall>f \<in> Collect proper_map. attr_model a f \<sqsubseteq> down\<cdot>{q}\<sharp>)" for q
    using lub_below_iff_b by blast
  with proper_map.upper_model'_below show ?thesis 
    unfolding models_def
    by blast
qed

lemma lub_below_lub:
  assumes "f1 ` A <<| a1" "f2 ` A <<| a2"
  "\<forall>x \<in> A. f1 x \<sqsubseteq> f2 x"
shows "a1 \<sqsubseteq> a2"
  unfolding is_lub_below_iff[OF assms(1)]
  using assms(2)[THEN is_lubD1] assms(3) 
  by (auto intro: below_trans intro: is_ubI dest: is_ubD)

lemma modelset_mono:
  assumes below: "a1 \<sqsubseteq> a2"
  shows "modelset a1 \<sqsubseteq> modelset a2"
proof -
  have ms1: "(attr_model a1) ` (Collect proper_map) <<| modelset a1"
    by (rule modelset_lub)
  have ms2: "(attr_model a2) ` (Collect proper_map) <<| modelset a2"
    by (rule modelset_lub)
  from assms[unfolded below_fun_def]
  have below_all: "\<forall>f \<in> Collect proper_map. attr_model a1 f \<sqsubseteq> attr_model a2 f"
    by (blast intro: monofun_cfun_arg)
  from ms1 ms2 below_all show ?thesis by (rule lub_below_lub)
qed

lemma upper_model_ex_iff:
"(\<exists>q. a \<sqsubseteq> down\<cdot>{q}\<sharp>) \<longleftrightarrow> a \<noteq> Top"
  by (cases a) (auto simp add: upper_pd_has_point)

lemma modelset_chain:
  fixes A :: "nat \<Rightarrow> ('a, 'b) attrs"
  assumes chain: "chain A"
    and ex: "\<forall>i. \<exists>q. models (A i) q"
  shows "\<exists>q. models (\<Squnion>i. A i) q"
proof -
  from chain[THEN chainE] ex have "\<And>i. modelset (A i) \<sqsubseteq> modelset (A (Suc i))"
    by (blast intro: modelset_mono)
  then have chm: "chain (\<lambda>i. modelset (A i))" by (rule chainI)
  from ex[unfolded modelset] have nontop: "modelset (A i) \<noteq> Top" for i
    by (simp add: upper_model_ex_iff)
  have "(\<Squnion>i. modelset (A i)) \<noteq> Top"
    using chm apply (cases rule: top_chain_cases)
    by (auto simp add: nontop)
  then obtain a' where "(\<Squnion>i. modelset (A i)) = down\<cdot>a'"
    by (cases "(\<Squnion>i. modelset (A i))") auto
  then obtain q where "(\<Squnion>i. modelset (A i)) \<sqsubseteq> down\<cdot>{q}\<sharp>" 
     using upper_pd_has_point by auto
  with lub_below_iff[OF chm] modelset have "\<And>i. models (A i) q" by blast
  then have "models (\<Squnion>i. A i) q"
    unfolding models_def using lub_below_iff[OF chain]
    by (simp add: ch2ch_fun chain lub_below_iff lub_fun)
  then show ?thesis ..
qed

corollary models_adm: "adm (\<lambda>a. (\<exists>q. models a q))"
  by (intro admI modelset_chain)

lemma models_bot: "models \<bottom> q" unfolding models_def by simp

pcpodef ('a::bifinite, 'b::bifinite) attr_space = "{a :: ('a, 'b) attrs. \<exists>q. models a q}"
  by (auto simp add: models_adm models_bot)

end