theory Split_Semantics
  imports Expr_Combinators Aggregate Split_Content
begin

default_sort type

section \<open>Semantics over split datasets\<close>

text \<open>The rigid semantics reads a dataset's definite rows, as a lower powerdomain.  The
  \<^emph>\<open>extended\<close> semantics reads a split dataset, definite rows and possible keys, and is defined
  combinator by combinator.  Its law is soundness against the rigid one: what it says is below
  what the rigid semantics says on the definite rows of every compact dataset above it.  It need
  not be exact there.\<close>

subsection \<open>Rows of compact split datasets\<close>

lemma lower_mem_Abs_pd_basis:
  assumes "finite S" "S \<noteq> {}"
  shows "x \<in>\<flat> lower_principal (Abs_pd_basis S) \<longleftrightarrow> (\<exists>s\<in>S. x \<sqsubseteq> Rep_compact_basis s)"
  using assms
proof (induct S rule: finite_ne_induct)
  case (singleton a)
  show ?case
    unfolding Abs_pd_basis_singleton lower_unit_Rep_compact_basis [symmetric] lower_mem_principal by simp
next
  case (insert a S)
  have eq: "Abs_pd_basis (insert a S) = PDPlus (PDUnit a) (Abs_pd_basis S)"
    unfolding PDPlus_def Rep_PDUnit using insert by (simp add: Abs_pd_basis_inverse pd_basis_def)
  show ?case
    unfolding eq lower_plus_principal [symmetric] lower_unit_Rep_compact_basis [symmetric] lower_mem_union lower_mem_principal
    using insert by simp
qed

lemma split_rows_mem_principal:
  "split_rows\<cdot>(split_principal t) = up\<cdot>data \<Longrightarrow> x \<in>\<flat> data \<longleftrightarrow> (\<exists>s\<in>srows t. x \<sqsubseteq> Rep_compact_basis s)"
proof (cases "srows t = {}")
  case False
  assume "split_rows\<cdot>(split_principal t) = up\<cdot>data"
  then have "data = lower_principal (Abs_pd_basis (srows t))" using False by (simp add: srows_lower_def)
  then show ?thesis by (simp add: lower_mem_Abs_pd_basis [OF finite_srows False])
qed (simp add: srows_lower_def)

lemma split_definite_rows_mem: "split_definite x xs \<Longrightarrow> split_rows\<cdot>xs = up\<cdot>data \<Longrightarrow> x \<in>\<flat> data"
  unfolding split_definite_def lower_mem_equiv
  by (drule monofun_cfun_arg [of _ _ split_rows]) simp

text \<open>The maximal rows of a compact dataset are among its generators.\<close>

lemma split_maximal_row_generator:
  assumes d: "split_rows\<cdot>(split_principal t) = up\<cdot>data" and m: "x \<in> lower_maximal data"
  shows "\<exists>s\<in>srows t. x = Rep_compact_basis s"
proof -
  have "x \<in>\<flat> data" using m by (simp add: lower_maximal_def)
  then obtain s where s: "s \<in> srows t" "x \<sqsubseteq> Rep_compact_basis s" using split_rows_mem_principal [OF d] by blast
  have "Rep_compact_basis s \<in>\<flat> data" using split_rows_mem_principal [OF d] s(1) by blast
  then have "Rep_compact_basis s = x" using m s(2) by (simp add: lower_maximal_def)
  then show ?thesis using s(1) by blast
qed

text \<open>Possibility is antitone: a key possible in a dataset is possible below it.\<close>

lemma split_possible_below: "split_possible k ys \<Longrightarrow> xs \<sqsubseteq> ys \<Longrightarrow> split_possible k xs"
  unfolding split_possible_keys by (erule below_trans [rotated], erule monofun_cfun_arg)


subsection \<open>Deciding at a finite stage\<close>

text \<open>A compact definite row of the lub of a chain is definite at some stage, and definite rows
  are closed downwards.  A continuous function with a compact value at a row takes that value at a
  compact row below.\<close>

lemma split_definite_below: "split_definite x D \<Longrightarrow> x' \<sqsubseteq> x \<Longrightarrow> split_definite x' D"
  unfolding split_definite_def by (erule below_trans [rotated]) simp

lemma split_definite_lub_compact:
  assumes Y: "chain Y" and x: "compact x" and d: "split_definite x (\<Squnion>i. Y i)"
  obtains i where "split_definite x (Y i)"
  using d compact_below_lub_iff [OF compact_split_open_unit [OF x] Y] unfolding split_definite_def by blast

lemma compact_approx_value:
  fixes f :: "'a::bifinite \<rightarrow> 'b::cpo"
  assumes c: "compact (f\<cdot>y)"
  obtains y' where "compact y'" "y' \<sqsubseteq> y" "f\<cdot>y' = f\<cdot>y"
proof -
  obtain a :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where a: "approx_chain a" using bifinite by blast
  interpret approx_chain a by (fact a)
  have ch: "chain (\<lambda>i. f\<cdot>(a i\<cdot>y))" by (intro ch2ch_Rep_cfunR ch2ch_Rep_cfunL chain_approx)
  have "f\<cdot>y = f\<cdot>((\<Squnion>i. a i)\<cdot>y)" by (simp add: lub_approx)
  also have "\<dots> = f\<cdot>(\<Squnion>i. a i\<cdot>y)" by (simp only: contlub_cfun_fun [OF chain_approx])
  also have "\<dots> = (\<Squnion>i. f\<cdot>(a i\<cdot>y))" by (rule contlub_cfun_arg) (intro ch2ch_Rep_cfunL chain_approx)
  finally have "f\<cdot>y = (\<Squnion>i. f\<cdot>(a i\<cdot>y))" .
  then obtain i where i: "f\<cdot>y \<sqsubseteq> f\<cdot>(a i\<cdot>y)" using compact_below_lub_iff [OF c ch] by auto
  have le: "a i\<cdot>y \<sqsubseteq> y" by (rule deflation.below [OF finite_deflation_imp_deflation [OF finite_deflation_approx]])
  have "f\<cdot>(a i\<cdot>y) = f\<cdot>y" by (rule below_antisym [OF monofun_cfun_arg [OF le] i])
  then show ?thesis using that le finite_deflation.compact [OF finite_deflation_approx] by blast
qed

text \<open>A key part is \<^emph>\<open>possible\<close> at an LOD where the possible keys, projected there, allow it.
  Possibility of a key gives possibility of its part; it is antitone in the dataset and survives
  to the lub of a chain, so impossibility is decided at a finite stage.\<close>

definition split_possible_at :: "'k::{bifinite, distributive_cpo} semi_factor \<Rightarrow> 'k \<Rightarrow> ('r::bifinite, 'k) split_pd \<Rightarrow> bool" where
  "split_possible_at c \<kappa> D \<longleftrightarrow> cmap_top\<cdot>(upper_map\<cdot>(proj c))\<cdot>(split_keys\<cdot>D) \<sqsubseteq> down\<cdot>{\<kappa>}\<sharp>"

lemma split_possible_atI: "split_possible u D \<Longrightarrow> split_possible_at c (proj c\<cdot>u) D"
  unfolding split_possible_at_def split_possible_keys
  by (drule monofun_cfun_arg [of _ _ "cmap_top\<cdot>(upper_map\<cdot>(proj c))"]) simp

lemma split_possible_at_below: "split_possible_at c \<kappa> D' \<Longrightarrow> D \<sqsubseteq> D' \<Longrightarrow> split_possible_at c \<kappa> D"
  unfolding split_possible_at_def by (erule below_trans [rotated]) (intro monofun_cfun_arg)

lemma split_possible_at_lub:
  assumes Y: "chain Y" and p: "\<And>i. split_possible_at c \<kappa> (Y i)"
  shows "split_possible_at c \<kappa> (\<Squnion>i. Y i)"
  unfolding split_possible_at_def contlub_cfun_arg [OF Y] contlub_cfun_arg [OF ch2ch_Rep_cfunR [OF Y]]
  by (rule lub_below) (simp_all add: Y p [unfolded split_possible_at_def])

subsection \<open>Expressions with an extended semantics\<close>

text \<open>An extended expression is an expression with a semantics over split datasets as well.\<close>

record ('k::"domain", 'f::type, 'r::"{bifinite, distributive_cpo}", 'v::bifinite) expr_ext = "('k, 'f, 'r, 'v) expr" +
  sem_ext :: "('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd"

hide_const (open) expr_ext.truncate

text \<open>An expression extended by a semantics over split datasets.\<close>

definition with_ext :: "('k::domain, 'f, 'r::{bifinite, distributive_cpo}, 'v::bifinite) expr \<Rightarrow>
    (('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "with_ext E s = expr.extend E (expr_ext.fields s)"

lemma with_ext_simps [simp]:
  "emind (with_ext E s) = emind E" "eguards (with_ext E s) = eguards E" "evalues (with_ext E s) = evalues E"
  
  "esem (with_ext E s) = esem E" "csem (with_ext E s) = csem E" "sem_ext (with_ext E s) = s"
  by (simp_all add: with_ext_def expr.defs expr_ext.defs)


locale split_dataspace = dataspace slicing + split_keyed
  for slicing :: "('f, 'k::{domain, lod_domain}) slicer_ops"
begin

text \<open>\<^emph>\<open>Soundness\<close>: below a compact dataset whose definite rows are \<open>data\<close>, a conforming
  dataset, conforming moreover relative to the expression's value entries, the extended semantics is below the rigid semantics
  of \<open>data\<close>, at every key of the key LOD.  Compact datasets with definite rows are where the rigid
  semantics is meant: it reads no possible keys, and its datasets cannot be empty.  An
  \<^emph>\<open>extended-lawful\<close> expression is moreover semilawful.\<close>

definition ext_sound :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> bool" where
  "ext_sound X \<longleftrightarrow> (\<forall>D D' data F k. D \<sqsubseteq> D' \<longrightarrow> compact D' \<longrightarrow> split_rows\<cdot>D' = up\<cdot>data \<longrightarrow> conforms data \<longrightarrow>
     fconf (evalues X) data F \<longrightarrow> proj (kd X F)\<cdot>k = k \<longrightarrow>
     sem_ext X D F k \<sqsubseteq> esem X data F k)"

lemma ext_soundI:
  "(\<And>D D' data F k. D \<sqsubseteq> D' \<Longrightarrow> compact D' \<Longrightarrow> split_rows\<cdot>D' = up\<cdot>data \<Longrightarrow> conforms data \<Longrightarrow>
     fconf (evalues X) data F \<Longrightarrow> proj (kd X F)\<cdot>k = k \<Longrightarrow>
     sem_ext X D F k \<sqsubseteq> esem X data F k) \<Longrightarrow> ext_sound X"
  unfolding ext_sound_def by blast

lemma ext_soundD:
  "ext_sound X \<Longrightarrow> D \<sqsubseteq> D' \<Longrightarrow> compact D' \<Longrightarrow> split_rows\<cdot>D' = up\<cdot>data \<Longrightarrow> conforms data \<Longrightarrow>
     fconf (evalues X) data F \<Longrightarrow> proj (kd X F)\<cdot>k = k \<Longrightarrow>
     sem_ext X D F k \<sqsubseteq> esem X data F k"
  unfolding ext_sound_def by blast

lemma semilawful_with_ext [simp]: "semilawful (with_ext E s) \<longleftrightarrow> semilawful E"
  by (simp add: semilawful_def cstrict_def)

definition ext_lawful :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> bool" where
  "ext_lawful X \<longleftrightarrow> semilawful X \<and> ext_sound X"

text \<open>A frame is \<^emph>\<open>LOD-bounded\<close> when its LOD is small.\<close>

definition lod_bounded :: "('k semi_factor, 'f, 'r) frame \<Rightarrow> bool" where
  "lod_bounded F \<longleftrightarrow> lod_small (flod F)"

lemma lod_bounded_frestrict [simp]: "lod_bounded (frestrict \<gamma> F) \<longleftrightarrow> lod_bounded F"
  by (simp add: lod_bounded_def)

lemma lod_bounded_ffor: "lod_bounded F \<Longrightarrow> lod_bounded (ffor \<tau> G F)"
  unfolding lod_bounded_def flod_ffor by (erule lod_small_below) (rule lattice_meet_le2)

lemma lod_bounded_finclude: "lod_bounded F \<Longrightarrow> lod_small M \<Longrightarrow> lod_bounded (finclude M F)"
  unfolding lod_bounded_def flod_finclude by (rule lod_small_sup)

text \<open>\<^emph>\<open>Monotonicity below conforming datasets\<close>: the extended semantics grows along datasets
  below a split dataset with conforming definite rows.  Their compact approximants need not
  conform, so this is what lets a semantics be extended from the compact datasets.\<close>

definition ext_mono :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> bool" where
  "ext_mono X \<longleftrightarrow> (\<forall>D D' C F k. lod_bounded F \<longrightarrow> conforming_rows (split_rows\<cdot>C) \<longrightarrow> D \<sqsubseteq> D' \<longrightarrow> D' \<sqsubseteq> C \<longrightarrow>
     sem_ext X D F k \<sqsubseteq> sem_ext X D' F k)"

lemma ext_monoI:
  "(\<And>D D' C F k. lod_bounded F \<Longrightarrow> conforming_rows (split_rows\<cdot>C) \<Longrightarrow> D \<sqsubseteq> D' \<Longrightarrow> D' \<sqsubseteq> C \<Longrightarrow>
     sem_ext X D F k \<sqsubseteq> sem_ext X D' F k) \<Longrightarrow> ext_mono X"
  unfolding ext_mono_def by blast

lemma ext_monoD:
  "ext_mono X \<Longrightarrow> lod_bounded F \<Longrightarrow> conforming_rows (split_rows\<cdot>C) \<Longrightarrow> D \<sqsubseteq> D' \<Longrightarrow> D' \<sqsubseteq> C \<Longrightarrow>
     sem_ext X D F k \<sqsubseteq> sem_ext X D' F k"
  unfolding ext_mono_def by blast

text \<open>\<^emph>\<open>Continuity\<close> below conforming datasets, at LOD-bounded frames: along a chain below a split
  dataset with conforming definite rows the extended semantics has the value at the lub as its
  lub.  This includes monotonicity below conforming datasets, and like @{thm contI2} it follows
  from that and the bound at the lub.  Chains of conforming datasets are such chains, and on the
  conforming split datasets the extended semantics is a continuous function.\<close>

definition ext_cont :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> bool" where
  "ext_cont X \<longleftrightarrow> (\<forall>Y C F k. lod_bounded F \<longrightarrow> chain Y \<longrightarrow> conforming_rows (split_rows\<cdot>C) \<longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> C \<longrightarrow>
     range (\<lambda>i. sem_ext X (Y i) F k) <<| sem_ext X (\<Squnion>i. Y i) F k)"

lemma ext_contD:
  "ext_cont X \<Longrightarrow> lod_bounded F \<Longrightarrow> chain Y \<Longrightarrow> conforming_rows (split_rows\<cdot>C) \<Longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> C \<Longrightarrow>
     range (\<lambda>i. sem_ext X (Y i) F k) <<| sem_ext X (\<Squnion>i. Y i) F k"
  unfolding ext_cont_def by blast

theorem ext_cont_mono: "ext_cont X \<Longrightarrow> ext_mono X"
proof (rule ext_monoI)
  fix D D' C :: "('r, 'k) split_pd" and F k
  assume c: "ext_cont X" and F: "lod_bounded F" and cC: "conforming_rows (split_rows\<cdot>C)" and le: "D \<sqsubseteq> D'" and le': "D' \<sqsubseteq> C"
  let ?Y = "\<lambda>i::nat. if i = 0 then D else D'"
  have Y: "chain ?Y" by (rule chainI) (simp add: le)
  have l: "(\<Squnion>i. ?Y i) = D'"
    by (rule lub_eqI, rule is_lubI) (auto simp: is_ub_def le dest: ub_rangeD [of _ 1])
  have "range (\<lambda>i. sem_ext X (?Y i) F k) <<| sem_ext X D' F k"
    using ext_contD [OF c F Y cC, of k] le' unfolding l by simp
  then show "sem_ext X D F k \<sqsubseteq> sem_ext X D' F k" using is_lubD1 [THEN ub_rangeD, of _ _ 0] by fastforce
qed

lemma ext_cont_below:
  assumes LC: "(\<Squnion>i. Y i) \<sqsubseteq> C" and Y: "chain (Y :: nat \<Rightarrow> ('r, 'k) split_pd)"
  shows "Y i \<sqsubseteq> C"
  using is_ub_thelub [OF Y, of i] LC by (rule below_trans)

lemma ext_cont_chain:
  "ext_cont X \<Longrightarrow> lod_bounded F \<Longrightarrow> chain Y \<Longrightarrow> conforming_rows (split_rows\<cdot>C) \<Longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> C \<Longrightarrow>
     chain (\<lambda>i. sem_ext X (Y i) F k)"
  by (rule chainI, rule ext_monoD [OF ext_cont_mono], assumption+, erule chainE, rule ext_cont_below) assumption+

lemma ext_cont_lub:
  "ext_cont X \<Longrightarrow> lod_bounded F \<Longrightarrow> chain Y \<Longrightarrow> conforming_rows (split_rows\<cdot>C) \<Longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> C \<Longrightarrow>
     sem_ext X (\<Squnion>i. Y i) F k = (\<Squnion>i. sem_ext X (Y i) F k)"
  by (rule lub_eqI [symmetric]) (rule ext_contD)

lemma conforming_rows_lub:
  "chain Y \<Longrightarrow> (\<And>i. conforming_rows (split_rows\<cdot>(Y i))) \<Longrightarrow> conforming_rows (split_rows\<cdot>(\<Squnion>i. Y i))"
  unfolding contlub_cfun_arg by (rule admD [OF adm_conforming_rows ch2ch_Rep_cfunR]) simp_all

lemma ext_contI2:
  assumes m: "ext_mono X"
    and l: "\<And>(Y :: nat \<Rightarrow> ('r, 'k) split_pd) C F k. lod_bounded F \<Longrightarrow> chain Y \<Longrightarrow> conforming_rows (split_rows\<cdot>C) \<Longrightarrow>
      (\<Squnion>i. Y i) \<sqsubseteq> C \<Longrightarrow> sem_ext X (\<Squnion>i. Y i) F k \<sqsubseteq> (\<Squnion>i. sem_ext X (Y i) F k)"
  shows "ext_cont X"
  unfolding ext_cont_def
proof (intro allI impI)
  fix Y :: "nat \<Rightarrow> ('r, 'k) split_pd" and C F k
  assume F: "lod_bounded F" and Y: "chain Y" and cC: "conforming_rows (split_rows\<cdot>C)" and LC: "(\<Squnion>i. Y i) \<sqsubseteq> C"
  have cY: "chain (\<lambda>i. sem_ext X (Y i) F k)"
    by (rule chainI) (rule ext_monoD [OF m F cC chainE [OF Y] ext_cont_below [OF LC Y]])
  have ub: "sem_ext X (Y i) F k \<sqsubseteq> sem_ext X (\<Squnion>i. Y i) F k" for i by (rule ext_monoD [OF m F cC is_ub_thelub [OF Y] LC])
  have "(\<Squnion>i. sem_ext X (Y i) F k) = sem_ext X (\<Squnion>i. Y i) F k"
    by (rule below_antisym [OF lub_below [OF cY ub] l [OF F Y cC LC]])
  then show "range (\<lambda>i. sem_ext X (Y i) F k) <<| sem_ext X (\<Squnion>i. Y i) F k"
    using cpo_lubI [OF cY] by simp
qed

lemma cont_sem_ext_conf:
  assumes c: "ext_cont X" and F: "lod_bounded F"
  shows "cont (\<lambda>D :: ('r, 'k) conf_split. sem_ext X (Rep_conf_split D) F k)"
proof (rule contI)
  fix Y :: "nat \<Rightarrow> ('r, 'k) conf_split" assume Y: "chain Y"
  have R: "chain (\<lambda>i. Rep_conf_split (Y i))" by (rule ch2ch_cont [OF cont_Rep_conf_split [OF cont_id] Y])
  have l: "Rep_conf_split (\<Squnion>i. Y i) = (\<Squnion>i. Rep_conf_split (Y i))" by (rule cont2contlubE [OF cont_Rep_conf_split [OF cont_id] Y])
  have conf: "conforming_rows (split_rows\<cdot>(\<Squnion>i. Rep_conf_split (Y i)))"
    using Rep_conf_split [of "\<Squnion>i. Y i"] unfolding l by simp
  show "range (\<lambda>i. sem_ext X (Rep_conf_split (Y i)) F k) <<| sem_ext X (Rep_conf_split (\<Squnion>i. Y i)) F k"
    unfolding l by (rule ext_contD [OF c F R conf below_refl])
qed

definition ext_fun :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('r, 'k) conf_split \<rightarrow> 'v option_pd" where
  "ext_fun X F k = (\<Lambda> D. sem_ext X (Rep_conf_split D) F k)"

lemma ext_fun_apply: "ext_cont X \<Longrightarrow> lod_bounded F \<Longrightarrow> ext_fun X F k\<cdot>D = sem_ext X (Rep_conf_split D) F k"
  unfolding ext_fun_def by (rule beta_cfun [OF cont_sem_ext_conf])


subsection \<open>Keys\<close>

text \<open>The selection test at a key part \<open>\<kappa>\<close> of an LOD \<open>s\<close>, for a row test \<open>g\<close> and a key test
  \<open>h\<close>: true where some definite row at \<open>\<kappa>\<close> passes both and \<open>\<kappa>\<close> is maximal at \<open>s\<close>, so that the
  row stays at \<open>\<kappa>\<close> when refined; false where the key test refutes \<open>\<kappa>\<close>, being false on every
  possible key that may end up there (in particular where there is none); undecided otherwise.  The
  row test can only decide for, the key test against: more rows may come, but only with possible
  keys.  A definite row at a partial key part decides nothing: it may still move up.\<close>

definition select_test :: "'k semi_factor \<Rightarrow> 'k \<Rightarrow> ('r \<rightarrow> tr) \<Rightarrow> ('k \<rightarrow> tr) \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> tr" where
  "select_test s \<kappa> g h D = (if maximal_at s \<kappa> \<and> (\<exists>y. split_definite y D \<and> rproj s y = \<kappa> \<and> g\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)
     then TT else if split_refuted s \<kappa> h D then FF else \<bottom>)"

lemma select_test_TT:
  "maximal_at s \<kappa> \<Longrightarrow> split_definite y D \<Longrightarrow> rproj s y = \<kappa> \<Longrightarrow> g\<cdot>y = TT \<Longrightarrow> h\<cdot>(row_key\<cdot>y) = TT \<Longrightarrow>
     select_test s \<kappa> g h D = TT"
  unfolding select_test_def by auto

lemma select_test_bot:
  "\<not> (maximal_at s \<kappa> \<and> (\<exists>y. split_definite y D \<and> rproj s y = \<kappa> \<and> g\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)) \<Longrightarrow>
     \<not> split_refuted s \<kappa> h D \<Longrightarrow> select_test s \<kappa> g h D = \<bottom>"
  unfolding select_test_def by (simp only: if_False if_not_P)

lemma select_test_FF:
  "\<not> (maximal_at s \<kappa> \<and> (\<exists>y. split_definite y D \<and> rproj s y = \<kappa> \<and> g\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)) \<Longrightarrow>
     split_refuted s \<kappa> h D \<Longrightarrow> select_test s \<kappa> g h D = FF"
  unfolding select_test_def by (simp only: if_False if_P)

text \<open>The key at an LOD \<open>c\<close> is the selection test at its part, multiplied by the part: present where
  a definite row has it and it is maximal, absent where it is impossible, and otherwise present with
  that key or absent.\<close>

abbreviation key_at_sem :: "'k semi_factor \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> 'k \<Rightarrow> 'k option_pd" where
  "key_at_sem c D k \<equiv> select_test c (proj c\<cdot>k) (\<Lambda> _. TT) (\<Lambda> _. TT) D \<odot> Present\<cdot>(proj c\<cdot>k)"

definition key_at_ext :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'k) expr_ext" where
  "key_at_ext c = with_ext (key_at c) (\<lambda>D F k. key_at_sem c D k)"

lemma key_at_ext_simps [simp]:
  "semilawful (key_at_ext c) \<longleftrightarrow> semilawful (key_at c)"
  "emind (key_at_ext c) = emind (key_at c)" "eguards (key_at_ext c) = eguards (key_at c)" "evalues (key_at_ext c) = evalues (key_at c)"
  "esem (key_at_ext c) = esem (key_at c)" "csem (key_at_ext c) = csem (key_at c)"
  "sem_ext (key_at_ext c) D F k = key_at_sem c D k"
  by (simp_all add: key_at_ext_def)

text \<open>Below a compact dataset, a definite row at a key maximal at \<open>c\<close> lies below a data point with
  that key, and a key no possible key projects to has no data point.\<close>

lemma definite_maximal_point:
  assumes DD: "D \<sqsubseteq> D'" and d: "split_rows\<cdot>D' = up\<cdot>data" and y: "split_definite y D"
    and mx: "maximal_at c (rproj c y)"
  obtains m where "m \<in> lower_maximal data" "y \<sqsubseteq> m" "rproj c m = rproj c y"
proof -
  have "y \<in>\<flat> data" by (rule split_definite_rows_mem [OF split_definite_mono [OF y DD] d])
  then obtain m where m: "m \<in> lower_maximal data" "y \<sqsubseteq> m" by (rule lower_mem_maximal_above)
  have "rproj c y \<sqsubseteq> rproj c m" by (intro monofun_cfun_arg m(2))
  then have "rproj c m = rproj c y" by (rule maximal_at_eq [OF mx proj_idem])
  with m that show ?thesis by blast
qed

lemma impossible_no_point:
  assumes DD: "D \<sqsubseteq> D'" and cD: "compact D'" and d: "split_rows\<cdot>D' = up\<cdot>data"
    and m: "m \<in> lower_maximal data"
  shows "split_possible (row_key\<cdot>m) D"
proof -
  obtain t where t: "D' = split_principal t" using split_pd.compact_imp_principal [OF cD] by blast
  obtain s where s: "s \<in> srows t" "m = Rep_compact_basis s"
    using split_maximal_row_generator [OF d [unfolded t] m] by blast
  obtain u where u: "u \<in> skeys t" "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>m"
    using split_basis_consistentD [OF s(1)] unfolding s(2) by blast
  have "split_possible (Rep_compact_basis u) D'" unfolding t using u(1) by (auto simp: split_possible_principal)
  then have "split_possible (row_key\<cdot>m) D'" by (rule split_possible_up [OF _ u(2)])
  then show ?thesis by (rule split_possible_below [OF _ DD])
qed

lemma impossible_at_no_point:
  assumes DD: "D \<sqsubseteq> D'" and cD: "compact D'" and d: "split_rows\<cdot>D' = up\<cdot>data"
    and m: "m \<in> lower_maximal data" and n: "\<not> split_possible_at c \<kappa> D"
  shows "rproj c m \<noteq> \<kappa>"
  using split_possible_atI [OF impossible_no_point [OF DD cD d m], of c] n by auto

text \<open>The selection test is below the rigid test on the data points at the key part.\<close>

lemma select_test_sound:
  assumes DD: "D \<sqsubseteq> D'" and cD: "compact D'" and d: "split_rows\<cdot>D' = up\<cdot>data"
  shows "select_test s \<kappa> g h D \<sqsubseteq> (\<exists>\<^sub>K m\<in>{m \<in> lower_maximal data. rproj s m = \<kappa>}. pand\<cdot>(g\<cdot>m)\<cdot>(h\<cdot>(row_key\<cdot>m)))"
proof (cases "maximal_at s \<kappa> \<and> (\<exists>y. split_definite y D \<and> rproj s y = \<kappa> \<and> g\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)")
  case True
  then obtain y where mx: "maximal_at s \<kappa>" and y: "split_definite y D" "rproj s y = \<kappa>"
    and gy: "g\<cdot>y = TT" and hy: "h\<cdot>(row_key\<cdot>y) = TT" by blast
  have mx': "maximal_at s (rproj s y)" using mx y(2) by simp
  obtain m where m: "m \<in> lower_maximal data" "y \<sqsubseteq> m" "rproj s m = rproj s y"
    using definite_maximal_point [OF DD d y(1) mx'] by blast
  have "TT \<sqsubseteq> g\<cdot>m" unfolding gy [symmetric] by (rule monofun_cfun_arg [OF m(2)])
  moreover have "TT \<sqsubseteq> h\<cdot>(row_key\<cdot>m)" unfolding hy [symmetric] by (intro monofun_cfun_arg m(2))
  ultimately have "pand\<cdot>(g\<cdot>m)\<cdot>(h\<cdot>(row_key\<cdot>m)) = TT" by (simp add: pand_TT_iff)
  then have "(\<exists>\<^sub>K m\<in>{m \<in> lower_maximal data. rproj s m = \<kappa>}. pand\<cdot>(g\<cdot>m)\<cdot>(h\<cdot>(row_key\<cdot>m))) = TT"
    unfolding kleene_bex_TT_iff using m(1,3) y(2) by auto
  then show ?thesis by (simp add: select_test_TT [OF mx y gy hy])
next
  case nT: False
  show ?thesis
  proof (cases "split_refuted s \<kappa> h D")
    case False
    show ?thesis by (simp only: select_test_bot [OF nT False] minimal)
  next
    case r: True
    have "(\<exists>\<^sub>K m\<in>{m \<in> lower_maximal data. rproj s m = \<kappa>}. pand\<cdot>(g\<cdot>m)\<cdot>(h\<cdot>(row_key\<cdot>m))) =
        (\<exists>\<^sub>K m\<in>{m \<in> lower_maximal data. rproj s m = \<kappa>}. FF)"
    proof (rule kleene_bex_cong [OF refl])
      fix m assume "m \<in> {m \<in> lower_maximal data. rproj s m = \<kappa>}"
      then have m: "m \<in> lower_maximal data" and mk: "rproj s m = \<kappa>" by simp_all
      have "h\<cdot>(row_key\<cdot>m) = FF"
        by (rule split_refuted_possible [OF r impossible_no_point [OF DD cD d m]]) (simp add: mk)
      then show "pand\<cdot>(g\<cdot>m)\<cdot>(h\<cdot>(row_key\<cdot>m)) = FF" by (simp add: pand_FF_iff)
    qed
    then show ?thesis by (simp add: select_test_FF [OF nT r])
  qed
qed

lemma kleene_bex_const_TT: "(\<exists>\<^sub>K m\<in>S. TT) = (if S = {} then FF else TT)"
  by (cases "S = {}") (auto simp: kleene_bex_TT_iff)

theorem ext_sound_key_at: "ext_sound (key_at_ext c)"
proof (rule ext_soundI, simp only: key_at_ext_simps)
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and d: "split_rows\<cdot>D' = up\<cdot>data"
  have fib: "fiber data c c F k = {m \<in> lower_maximal data. rproj c m = proj c\<cdot>k}"
    by (simp add: fiber_def join_meet_self)
  have esem: "esem (key_at c) data F k =
      (\<exists>\<^sub>K m\<in>fiber data c c F k. pand\<cdot>((\<Lambda> _. TT)\<cdot>m)\<cdot>((\<Lambda> _. TT)\<cdot>(row_key\<cdot>m))) \<odot> Present\<cdot>(proj c\<cdot>k)"
    by (cases "fiber data c c F k = {}") (simp_all add: kleene_bex_const_TT)
  show "key_at_sem c D k \<sqsubseteq> esem (key_at c) data F k"
    unfolding esem fib by (intro monofun_cfun_fun monofun_cfun_arg select_test_sound [OF DD cD d])
qed

theorem ext_lawful_key_at: "ext_lawful (key_at_ext c)"
  unfolding ext_lawful_def by (simp add: semilawful_key_at ext_sound_key_at)


subsection \<open>Table columns\<close>

text \<open>A column is the selection test at its key part, multiplied by the column function of the
  join of the sections of the definite rows selected there: those at the key part, where it is
  maximal.  In a conforming dataset above, the rows at a maximal key carry one section, above all of
  them.  At a partial key nothing is selected: a row there may move up, and another row may come to
  the key with an unrelated section.\<close>

definition col_sections :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "col_sections c a D k = {y \<downharpoonright> c | y. split_definite y D \<and> rproj a y = proj a\<cdot>k}"

definition col_value :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> 'k \<Rightarrow> 'r" where
  "col_value c a D k = (if maximal_at a (proj a\<cdot>k) then lub (col_sections c a D k) else \<bottom>)"

abbreviation column_sem :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r \<rightarrow> 'w::bifinite) \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> 'k \<Rightarrow> 'w option_pd" where
  "column_sem c a v D k \<equiv> select_test a (proj a\<cdot>k) (\<Lambda> _. TT) (\<Lambda> _. TT) D \<odot> Present\<cdot>(v\<cdot>(col_value c a D k))"

lemma lub_empty: "lub {} = (\<bottom> :: 'a::pcpo)"
  by (rule lub_eqI) (simp add: is_lub_def)

definition column_ext :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r \<rightarrow> 'w::bifinite) \<Rightarrow> ('k, 'f, 'r, 'w) expr_ext" where
  "column_ext c a v = with_ext (column c a v) (\<lambda>D F k. column_sem c a v D k)"

lemma column_ext_simps [simp]:
  "semilawful (column_ext c a v) \<longleftrightarrow> semilawful (column c a v)"
  "emind (column_ext c a v) = emind (column c a v)" "eguards (column_ext c a v) = eguards (column c a v)"
  "evalues (column_ext c a v) = evalues (column c a v)"
  "esem (column_ext c a v) = esem (column c a v)" "csem (column_ext c a v) = csem (column c a v)"
  "sem_ext (column_ext c a v) D F k = column_sem c a v D k"
  by (simp_all add: column_ext_def)

theorem ext_sound_column: "ext_sound (column_ext c a v)"
proof (rule ext_soundI, simp only: column_ext_simps)
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and d: "split_rows\<cdot>D' = up\<cdot>data"
    and conf: "fconf (evalues (column c a v)) data F"
  let ?e = "mk_value (sel a a) c a"
  have cf: "entry_conf ?e data F" using conf by (simp add: fconf_def)
  have fib: "fiber data a a F k = {m \<in> lower_maximal data. rproj a m = proj a\<cdot>k}"
    by (simp add: fiber_def join_meet_self)
  let ?t = "select_test a (proj a\<cdot>k) (\<Lambda> _. TT) (\<Lambda> _. TT) D"
  have t: "?t \<sqsubseteq> (\<exists>\<^sub>K m\<in>fiber data a a F k. TT)"
    using select_test_sound [OF DD cD d, of a "proj a\<cdot>k" "\<Lambda> _. TT" "\<Lambda> _. TT"] unfolding fib by simp
  show "column_sem c a v D k \<sqsubseteq> esem (column c a v) data F k"
  proof (cases "fiber data a a F k = {}")
    case True
    have "?t \<odot> Present\<cdot>(v\<cdot>(col_value c a D k)) \<sqsubseteq> FF \<odot> Present\<cdot>(v\<cdot>(col_value c a D k))"
      by (intro monofun_cfun_fun monofun_cfun_arg) (use t True in simp)
    then show ?thesis using True by simp
  next
    case False
    then obtain m where m: "m \<in> fiber data a a F k" by blast
    have "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k = (\<lambda>_. v\<cdot>(m \<downharpoonright> c)) ` fiber data a a F k"
      by (rule image_cong [OF refl]) (simp add: column_fiber_section [OF cf m])
    then have V: "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k = {v\<cdot>(m \<downharpoonright> c)}"
      using m by (auto simp: image_constant_conv)
    have esem: "esem (column c a v) data F k = TT \<odot> Present\<cdot>(v\<cdot>(m \<downharpoonright> c))" using False by (simp add: V)
    have tT: "?t \<sqsubseteq> TT" using t False by (simp add: kleene_bex_const_TT)
    have cv: "col_value c a D k \<sqsubseteq> m \<downharpoonright> c"
    proof (cases "maximal_at a (proj a\<cdot>k) \<and> col_sections c a D k \<noteq> {}")
      case True
      then have mx: "maximal_at a (proj a\<cdot>k)" and ne: "col_sections c a D k \<noteq> {}" by simp_all
      have ub: "col_sections c a D k <| m \<downharpoonright> c"
      proof (rule is_ubI)
        fix z assume "z \<in> col_sections c a D k"
        then obtain y where y: "split_definite y D" "rproj a y = proj a\<cdot>k" "z = y \<downharpoonright> c"
          by (auto simp: col_sections_def)
        have "maximal_at a (rproj a y)" using mx y(2) by simp
        then obtain m' where m': "m' \<in> lower_maximal data" "y \<sqsubseteq> m'" "rproj a m' = rproj a y"
          using definite_maximal_point [OF DD d y(1)] by blast
        have m'F: "m' \<in> fiber data a a F k" using fib m'(1,3) y(2) by simp
        have "y \<downharpoonright> c \<sqsubseteq> m' \<downharpoonright> c" by (intro monofun_cfun_arg m'(2))
        also have "\<dots> = m \<downharpoonright> c" by (rule column_fiber_section [OF cf m m'F])
        finally show "z \<sqsubseteq> m \<downharpoonright> c" by (simp only: y(3))
      qed
      show ?thesis unfolding col_value_def by (simp only: if_P [OF mx]) (rule lub_belowI [OF ne ub])
    next
      case False
      then show ?thesis unfolding col_value_def by (auto simp: lub_empty)
    qed
    show ?thesis unfolding esem
      by (rule monofun_cfun [OF monofun_cfun_arg [OF tT] monofun_cfun_arg [OF monofun_cfun_arg [OF cv]]])
  qed
qed

theorem ext_lawful_column:
  "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>)) \<Longrightarrow> ext_lawful (column_ext c a v)"
  unfolding ext_lawful_def by (simp add: semilawful_column ext_sound_column)


subsection \<open>Constants and maps\<close>

definition const_ext :: "'v::bifinite \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "const_ext v = with_ext (const_expr v) (\<lambda>D F k. Present\<cdot>v)"

lemma const_ext_simps [simp]:
  "semilawful (const_ext v) \<longleftrightarrow> semilawful (const_expr v)"
  "emind (const_ext v) = emind (const_expr v)" "eguards (const_ext v) = eguards (const_expr v)" "evalues (const_ext v) = evalues (const_expr v)"
  "esem (const_ext v) = esem (const_expr v)" "csem (const_ext v) = csem (const_expr v)"
  "sem_ext (const_ext v) D F k = Present\<cdot>v"
  by (simp_all add: const_ext_def)

theorem ext_lawful_const: "ext_lawful (const_ext v)"
  unfolding ext_lawful_def by (auto simp: semilawful_const_expr intro: ext_soundI)

definition smap_ext :: "('v::bifinite \<rightarrow> 'w::bifinite) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext \<Rightarrow> ('k, 'f, 'r, 'w) expr_ext" where
  "smap_ext g X = with_ext (smap g X) (\<lambda>D F k. map_option_pd g\<cdot>(sem_ext X D F k))"

lemma smap_ext_simps [simp]:
  "semilawful (smap_ext g X) \<longleftrightarrow> semilawful (smap g X)"
  "emind (smap_ext g X) = emind (smap g X)" "eguards (smap_ext g X) = eguards (smap g X)" "evalues (smap_ext g X) = evalues (smap g X)"
  "esem (smap_ext g X) = esem (smap g X)" "csem (smap_ext g X) = csem (smap g X)"
  "sem_ext (smap_ext g X) D F k = map_option_pd g\<cdot>(sem_ext X D F k)"
  by (simp_all add: smap_ext_def)

theorem ext_sound_smap: "ext_sound X \<Longrightarrow> ext_sound (smap_ext g X)"
  by (rule ext_soundI) (simp add: monofun_cfun_arg ext_soundD)

theorem ext_lawful_smap: "ext_lawful X \<Longrightarrow> ext_lawful (smap_ext g X)"
  unfolding ext_lawful_def by (simp add: semilawful_smap ext_sound_smap)

abbreviation value_at_ext :: "'k semi_factor \<Rightarrow> ('k \<rightarrow> 'v::bifinite) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "value_at_ext c g \<equiv> smap_ext g (key_at_ext c)"


subsection \<open>Frame transformers\<close>

definition restrict_ext :: "'r guard \<Rightarrow> ('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "restrict_ext \<gamma> X = with_ext (restrict \<gamma> X) (\<lambda>D F. sem_ext X D (frestrict \<gamma> F))"

lemma restrict_ext_simps [simp]:
  "semilawful (restrict_ext \<gamma> X) \<longleftrightarrow> semilawful (restrict \<gamma> X)"
  "emind (restrict_ext \<gamma> X) = emind (restrict \<gamma> X)" "eguards (restrict_ext \<gamma> X) = eguards (restrict \<gamma> X)" "evalues (restrict_ext \<gamma> X) = evalues (restrict \<gamma> X)"
  "esem (restrict_ext \<gamma> X) = esem (restrict \<gamma> X)" "csem (restrict_ext \<gamma> X) = csem (restrict \<gamma> X)"
  "sem_ext (restrict_ext \<gamma> X) D F = sem_ext X D (frestrict \<gamma> F)"
  by (simp_all add: restrict_ext_def)

theorem ext_sound_restrict: "ext_sound X \<Longrightarrow> ext_sound (restrict_ext \<gamma> X)"
  by (rule ext_soundI) (simp add: ext_soundD fconf_frestrict)

theorem ext_lawful_restrict: "ext_lawful X \<Longrightarrow> ext_lawful (restrict_ext \<gamma> X)"
  unfolding ext_lawful_def by (simp add: semilawful_restrict ext_sound_restrict)

definition filtfor_ext :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "filtfor_ext \<tau> G X = with_ext (filtfor \<tau> G X) (\<lambda>D F k. sem_ext X D (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k))"

lemma filtfor_ext_simps [simp]:
  "semilawful (filtfor_ext \<tau> G X) \<longleftrightarrow> semilawful (filtfor \<tau> G X)"
  "emind (filtfor_ext \<tau> G X) = emind (filtfor \<tau> G X)" "eguards (filtfor_ext \<tau> G X) = eguards (filtfor \<tau> G X)" "evalues (filtfor_ext \<tau> G X) = evalues (filtfor \<tau> G X)"
  "esem (filtfor_ext \<tau> G X) = esem (filtfor \<tau> G X)" "csem (filtfor_ext \<tau> G X) = csem (filtfor \<tau> G X)"
  "sem_ext (filtfor_ext \<tau> G X) D F k = sem_ext X D (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k)"
  by (simp_all add: filtfor_ext_def)

theorem ext_sound_filtfor: "ext_sound X \<Longrightarrow> ext_sound (filtfor_ext \<tau> G X)"
proof (rule ext_soundI, simp only: filtfor_ext_simps filtfor_simps)
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume X: "ext_sound X" and DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_rows\<cdot>D' = up\<cdot>data" and cf: "conforms data"
    and d: "fconf (map (for_value \<tau>) (evalues X)) data F"
  have d': "fconf (evalues X) data (ffor \<tau> G F)" using d by (simp only: fconf_filtfor [of _ _ _ _ G])
  show "sem_ext X D (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k)
      \<sqsubseteq> esem X data (ffor \<tau> G F) (proj (emind X \<squnion> flod (ffor \<tau> G F))\<cdot>k)"
    by (rule ext_soundD [OF X DD cD nD cf d' proj_idem])
qed

theorem ext_lawful_filtfor: "ext_lawful X \<Longrightarrow> ext_lawful (filtfor_ext \<tau> G X)"
  unfolding ext_lawful_def by (simp add: semilawful_filtfor ext_sound_filtfor)

text \<open>Including dimensions raises the frame LOD; the key LOD of a semilawful inner expression in
  the raised frame covers the outer one.\<close>

lemma include_dims_kd_below:
  assumes ES: "semilawful E"
  shows "kd (include_dims M E) F \<sqsubseteq> kd E (finclude M F)"
proof -
  let ?n = "fold (\<squnion>) (map (\<lambda>S. lower_part (include_sel M S)) (esels E)) \<bottom>"
  have le: "?n \<sqsubseteq> emind E \<squnion> M"
  proof (rule fold_join_least)
    fix x assume "x \<in> set (map (\<lambda>S. lower_part (include_sel M S)) (esels E))"
    then obtain S where S: "S \<in> set (esels E)" and x: "x = lower_part (include_sel M S)" by auto
    show "x \<sqsubseteq> emind E \<squnion> M" unfolding x include_sel_simps
      by (rule lattice_join_mono [OF lower_below_mind [OF ES S] truncate_below])
  qed simp
  have "?n \<squnion> flod F \<sqsubseteq> (emind E \<squnion> M) \<squnion> flod F" by (rule lattice_join_mono [OF le below_refl])
  also have "\<dots> = emind E \<squnion> flod (finclude M F)" unfolding flod_finclude by (simp only: lattice_join_ac)
  finally show ?thesis by simp
qed

definition include_dims_ext :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "include_dims_ext M X = with_ext (include_dims M X) (\<lambda>D F. sem_ext X D (finclude M F))"

lemma include_dims_ext_simps [simp]:
  "semilawful (include_dims_ext M X) \<longleftrightarrow> semilawful (include_dims M X)"
  "emind (include_dims_ext M X) = emind (include_dims M X)" "eguards (include_dims_ext M X) = eguards (include_dims M X)" "evalues (include_dims_ext M X) = evalues (include_dims M X)"
  "esem (include_dims_ext M X) = esem (include_dims M X)" "csem (include_dims_ext M X) = csem (include_dims M X)"
  "sem_ext (include_dims_ext M X) D F = sem_ext X D (finclude M F)"
  by (simp_all add: include_dims_ext_def)

theorem ext_sound_include_dims:
  assumes ES: "semilawful X" and X: "ext_sound X"
  shows "ext_sound (include_dims_ext M X)"
proof (rule ext_soundI, simp only: include_dims_ext_simps include_dims_simps(3,4))
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_rows\<cdot>D' = up\<cdot>data" and cf: "conforms data"
    and d: "fconf (map (include_entry M) (evalues X)) data F"
    and k: "proj (kd (include_dims M X) F)\<cdot>k = k"
  have d': "fconf (evalues X) data (finclude M F)" using d by (simp only: fconf_include)
  have k': "proj (kd X (finclude M F))\<cdot>k = k" by (rule proj_fix_mono [OF include_dims_kd_below [OF ES] k])
  show "sem_ext X D (finclude M F) k \<sqsubseteq> esem X data (finclude M F) k"
    by (rule ext_soundD [OF X DD cD nD cf d' k'])
qed

theorem ext_lawful_include_dims: "ext_lawful X \<Longrightarrow> ext_lawful (include_dims_ext M X)"
  unfolding ext_lawful_def by (simp add: semilawful_include_dims ext_sound_include_dims)


subsection \<open>Combining\<close>

definition combine_ext :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<Rightarrow> ('k, 'f, 'r, 'a::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'b::bifinite) expr_ext \<Rightarrow>
    ('k, 'f, 'r, 'c::bifinite) expr_ext" where
  "combine_ext f X\<^sub>1 X\<^sub>2 = with_ext (combine f X\<^sub>1 X\<^sub>2) (\<lambda>D F k. lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 D F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 D F (proj (kd X\<^sub>2 F)\<cdot>k)))"

lemma combine_ext_simps [simp]:
  "semilawful (combine_ext f X\<^sub>1 X\<^sub>2) \<longleftrightarrow> semilawful (combine f X\<^sub>1 X\<^sub>2)"
  "emind (combine_ext f X\<^sub>1 X\<^sub>2) = emind (combine f X\<^sub>1 X\<^sub>2)" "eguards (combine_ext f X\<^sub>1 X\<^sub>2) = eguards (combine f X\<^sub>1 X\<^sub>2)" "evalues (combine_ext f X\<^sub>1 X\<^sub>2) = evalues (combine f X\<^sub>1 X\<^sub>2)"
  "esem (combine_ext f X\<^sub>1 X\<^sub>2) = esem (combine f X\<^sub>1 X\<^sub>2)" "csem (combine_ext f X\<^sub>1 X\<^sub>2) = csem (combine f X\<^sub>1 X\<^sub>2)"
  "sem_ext (combine_ext f X\<^sub>1 X\<^sub>2) D F k =
     lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 D F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 D F (proj (kd X\<^sub>2 F)\<cdot>k))"
  by (simp_all add: combine_ext_def)

theorem ext_sound_combine:
  assumes X\<^sub>1: "ext_sound X\<^sub>1" and X\<^sub>2: "ext_sound X\<^sub>2"
  shows "ext_sound (combine_ext f X\<^sub>1 X\<^sub>2)"
proof (rule ext_soundI, simp only: combine_ext_simps combine_simps)
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_rows\<cdot>D' = up\<cdot>data" and cf: "conforms data"
    and d: "fconf (evalues X\<^sub>1 @ evalues X\<^sub>2) data F"
  have d1: "fconf (evalues X\<^sub>1) data F" and d2: "fconf (evalues X\<^sub>2) data F"
    using d by (simp_all add: fconf_def)
  show "lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 D F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 D F (proj (kd X\<^sub>2 F)\<cdot>k))
      \<sqsubseteq> lift2_option_pd f\<cdot>(esem X\<^sub>1 data F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>
          (esem X\<^sub>2 data F (proj (kd X\<^sub>2 F)\<cdot>k))"
    by (rule monofun_cfun [OF monofun_cfun_arg ext_soundD [OF X\<^sub>2 DD cD nD cf d2 proj_idem]],
        rule ext_soundD [OF X\<^sub>1 DD cD nD cf d1 proj_idem])
qed

theorem ext_lawful_combine: "ext_lawful X\<^sub>1 \<Longrightarrow> ext_lawful X\<^sub>2 \<Longrightarrow> ext_lawful (combine_ext f X\<^sub>1 X\<^sub>2)"
  unfolding ext_lawful_def by (simp add: semilawful_combine ext_sound_combine)


subsection \<open>Presence tests\<close>

text \<open>A group is populated as far as the selection test of the frame's filter at the fiber's key
  part says: populated where some definite row there passes the filter and the part is maximal (the
  data point above it is in the fiber and passes too), unpopulated where no possible key may end up
  at the part, and undecided otherwise.\<close>

definition populated_ext :: "('r, 'k) split_pd \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> tr" where
  "populated_ext D a \<rho> F k = select_test (a \<squnion> (\<rho> \<sqinter> flod F)) (proj (a \<squnion> (\<rho> \<sqinter> flod F))\<cdot>k)
     (amb F) (sopen (coarsen \<rho> (slice F))) D"

text \<open>The frame's filter is its row part, the ambient filter, and its key part, the slice
  coarsened to the upper part.\<close>

lemma fguard_split: "fguard \<rho> F\<cdot>y = pand\<cdot>(amb F\<cdot>y)\<cdot>(sopen (coarsen \<rho> (slice F))\<cdot>(row_key\<cdot>y))"
  by (simp add: fguard_def gand_apply guard_holds_apply)

lemma populated_ext_TT:
  "maximal_at (a \<squnion> (\<rho> \<sqinter> flod F)) (proj (a \<squnion> (\<rho> \<sqinter> flod F))\<cdot>k) \<Longrightarrow> split_definite y D \<Longrightarrow>
     rproj (a \<squnion> (\<rho> \<sqinter> flod F)) y = proj (a \<squnion> (\<rho> \<sqinter> flod F))\<cdot>k \<Longrightarrow> fguard \<rho> F\<cdot>y = TT \<Longrightarrow> populated_ext D a \<rho> F k = TT"
  unfolding populated_ext_def fguard_split pand_TT_iff by (rule select_test_TT) blast+

lemma populated_ext_sound:
  assumes DD: "D \<sqsubseteq> D'" and cD: "compact D'" and d: "split_rows\<cdot>D' = up\<cdot>data"
  shows "populated_ext D a \<rho> F k \<sqsubseteq> populated data a \<rho> F k"
  unfolding populated_ext_def populated_def fiber_def fguard_split by (rule select_test_sound [OF DD cD d])

definition present_at_ext :: "'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "present_at_ext a \<rho> X = with_ext (present_at a \<rho> X)
     (\<lambda>D F k. populated_ext D (emind X \<squnion> a) \<rho> F k \<odot> sem_ext X D F (proj (kd X F)\<cdot>k))"

lemma present_at_ext_simps [simp]:
  "semilawful (present_at_ext a \<rho> X) \<longleftrightarrow> semilawful (present_at a \<rho> X)"
  "emind (present_at_ext a \<rho> X) = emind (present_at a \<rho> X)" "eguards (present_at_ext a \<rho> X) = eguards (present_at a \<rho> X)"
  "evalues (present_at_ext a \<rho> X) = evalues (present_at a \<rho> X)"
  "esem (present_at_ext a \<rho> X) = esem (present_at a \<rho> X)" "csem (present_at_ext a \<rho> X) = csem (present_at a \<rho> X)"
  "sem_ext (present_at_ext a \<rho> X) D F k = populated_ext D (emind X \<squnion> a) \<rho> F k \<odot> sem_ext X D F (proj (kd X F)\<cdot>k)"
  by (simp_all add: present_at_ext_def)

theorem ext_sound_present_at: "ext_sound X \<Longrightarrow> ext_sound (present_at_ext a \<rho> X)"
proof (rule ext_soundI, simp only: present_at_ext_simps present_at_simps)
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume X: "ext_sound X" and DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_rows\<cdot>D' = up\<cdot>data"
    and cf: "conforms data" and d: "fconf (evalues X) data F"
  show "populated_ext D (emind X \<squnion> a) \<rho> F k \<odot> sem_ext X D F (proj (kd X F)\<cdot>k)
      \<sqsubseteq> populated data (emind X \<squnion> a) \<rho> F k \<odot> esem X data F (proj (kd X F)\<cdot>k)"
    by (rule monofun_cfun [OF monofun_cfun_arg [OF populated_ext_sound [OF DD cD nD]] ext_soundD [OF X DD cD nD cf d proj_idem]])
qed

theorem ext_lawful_present_at: "ext_lawful X \<Longrightarrow> ext_lawful (present_at_ext a \<rho> X)"
  unfolding ext_lawful_def by (simp add: semilawful_present_at ext_sound_present_at)


subsection \<open>Aggregation\<close>

text \<open>The data points of a compact dataset are finitely many.\<close>

lemma split_maximal_finite:
  assumes cD: "compact D'" and d: "split_rows\<cdot>D' = up\<cdot>data"
  shows "finite (lower_maximal data)"
proof -
  obtain t where t: "D' = split_principal t" using split_pd.compact_imp_principal [OF cD] by blast
  have "lower_maximal data \<subseteq> Rep_compact_basis ` srows t"
    using split_maximal_row_generator [OF d [unfolded t]] by blast
  then show ?thesis by (rule finite_subset) (simp add: finite_srows)
qed

text \<open>An aggregate over a compact split dataset folds over the inner keys of the outer key in the
  conforming keyspace that are definitely there, those maximal at the inner key LOD with a definite
  row, and those possibly there, the inner key parts possible at the inner key LOD.  A definite
  inner key is folded with its value, a possible one with its value or the unit.  The rows of a
  dataset above are finitely many, so it is the greatest lower bound of the folds over the definite
  keys and finitely many possible ones.  Over an arbitrary split dataset the aggregate is the lub of
  these over the compact datasets below: of infinitely many rows only what finitely many show is
  known.\<close>

definition agg_definite :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'k set" where
  "agg_definite E D F k = {\<kappa>. maximal_at (kd E F) \<kappa> \<and> proj (flod F)\<cdot>\<kappa> = k \<and> \<kappa> \<in> Rep_cfun (proj (kd E F)) ` conforming_keyspace \<and>
     (\<exists>y. split_definite y D \<and> rproj (kd E F) y = \<kappa>)}"

definition agg_possible :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'k set" where
  "agg_possible E D F k = {\<kappa>. proj (flod F)\<cdot>\<kappa> = k \<and> \<kappa> \<in> Rep_cfun (proj (kd E F)) ` conforming_keyspace \<and>
     split_possible_at (kd E F) \<kappa> D}"

definition agg_member :: "('k, 'f, 'r, 'v::bifinite) expr_ext \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> 'v option_pd" where
  "agg_member X D F k \<kappa> = (if \<kappa> \<in> agg_definite X D F k then populated_ext D (emind X) \<top> F \<kappa> \<odot> sem_ext X D F \<kappa>
     else populated_ext D (emind X) \<top> F \<kappa> \<odot> sem_ext X D F \<kappa> + Absent)"

definition agg_glb :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd" where
  "agg_glb f X D F k = glb {agg_fold f (agg_member X D F k) (agg_definite X D F k \<union> C) | C. finite C \<and> C \<subseteq> agg_possible X D F k}"

definition agg_approx :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd set" where
  "agg_approx f X D F k = {agg_glb f X D\<^sub>0 F k | D\<^sub>0. compact D\<^sub>0 \<and> D\<^sub>0 \<sqsubseteq> D}"

definition agg_ext_sem :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'v option_pd" where
  "agg_ext_sem f X D F k = lub (agg_approx f X D F k)"

definition aggregate_ext :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext \<Rightarrow> ('k, 'f, 'r, 'v) expr_ext" where
  "aggregate_ext f X = with_ext (aggregate f X) (agg_ext_sem f X)"

lemma aggregate_ext_simps [simp]:
  "semilawful (aggregate_ext f X) \<longleftrightarrow> semilawful (aggregate f X)"
  "emind (aggregate_ext f X) = emind (aggregate f X)" "eguards (aggregate_ext f X) = eguards (aggregate f X)"
  "evalues (aggregate_ext f X) = evalues (aggregate f X)"
  "esem (aggregate_ext f X) = esem (aggregate f X)" "csem (aggregate_ext f X) = csem (aggregate f X)"
  "sem_ext (aggregate_ext f X) = agg_ext_sem f X"
  by (simp_all add: aggregate_ext_def)

lemma agg_glb_sound:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and X: "ext_sound X"
    and DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_rows\<cdot>D' = up\<cdot>data"
    and cf: "conforms data" and d0: "fconf (map release (evalues X)) data F"
  shows "agg_glb f X D F k \<sqsubseteq> esem (aggregate f X) data F k"
proof -
  have d: "fconf (evalues X) data F" using d0 by (simp only: fconf_release)
  let ?K = "kd X F" and ?Z = "afiber data F (flod F) k"
  let ?A = "rproj ?K ` ?Z"
  let ?V = "\<lambda>\<kappa>. populated data (emind X) \<top> F \<kappa> \<odot> esem X data F \<kappa>"
  have FK: "flod F \<sqsubseteq> ?K" by (rule lattice_join_ge2)
  have pK: "proj (flod F)\<cdot>(rproj ?K y) = rproj (flod F) y" for y by (rule proj_le [OF FK])
  have fA: "finite ?A" by (rule finite_imageI, rule finite_subset [OF _ split_maximal_finite [OF cD nD]]) (auto simp: afiber_def)
  have rigid: "agg_fold f ?V (inner_keys X data F k) = agg_fold f ?V ?A"
  proof -
    interpret agg: comm_monoid_set "\<lambda>x y. combine_option_pd f\<cdot>x\<cdot>y" Absent
      unfolding comm_monoid_set_def by (rule comm_monoid_combine_option_pd [OF f])
    have sub: "inner_keys X data F k \<subseteq> ?A" by (auto simp: inner_keys_def)
    have "agg.F ?V (inner_keys X data F k) = agg.F ?V ?A"
      by (rule agg.mono_neutral_left [OF fA sub]) (auto simp: inner_keys_def)
    then show ?thesis by (simp only: agg_fold_finite [OF f fA] agg_fold_finite [OF f finite_subset [OF sub fA]])
  qed
  have defA: "agg_definite X D F k \<subseteq> ?A"
  proof
    fix \<kappa> assume "\<kappa> \<in> agg_definite X D F k"
    then obtain y where mx: "maximal_at ?K \<kappa>" and k: "proj (flod F)\<cdot>\<kappa> = k"
      and y: "split_definite y D" "rproj ?K y = \<kappa>" by (auto simp: agg_definite_def)
    have mx': "maximal_at ?K (rproj ?K y)" using mx y(2) by simp
    obtain m where m: "m \<in> lower_maximal data" "rproj ?K m = rproj ?K y"
      using definite_maximal_point [OF DD nD y(1) mx'] by blast
    have "rproj (flod F) m = k" unfolding pK [symmetric] m(2) y(2) by (rule k)
    then have mZ: "m \<in> ?Z" using m(1) by (simp add: afiber_def)
    have "\<kappa> = rproj ?K m" by (simp only: m(2) y(2))
    then show "\<kappa> \<in> ?A" by (rule image_eqI [OF _ mZ])
  qed
  have Apos: "?A \<subseteq> agg_possible X D F k"
  proof
    fix \<kappa> assume "\<kappa> \<in> ?A"
    then obtain m where m: "m \<in> ?Z" "\<kappa> = rproj ?K m" by blast
    have mm: "m \<in> lower_maximal data" and mk: "rproj (flod F) m = k" using m(1) by (simp_all add: afiber_def)
    have p: "split_possible_at ?K (rproj ?K m) D" by (rule split_possible_atI [OF impossible_no_point [OF DD cD nD mm]])
    have r: "row_key\<cdot>m \<in> conforming_keyspace" using universallyD [OF universally_keyspace cf] mm by blast
    show "\<kappa> \<in> agg_possible X D F k" unfolding agg_possible_def m(2) using p r pK mk by blast
  qed
  have DA: "agg_definite X D F k \<union> ?A = ?A" using defA by blast
  have "agg_glb f X D F k \<sqsubseteq> agg_fold f (agg_member X D F k) (agg_definite X D F k \<union> ?A)"
    unfolding agg_glb_def by (rule glb_below, rule CollectI, rule exI [of _ ?A]) (intro conjI refl fA Apos)
  also have "\<dots> \<sqsubseteq> agg_fold f ?V ?A" unfolding DA
  proof (rule agg_fold_mono [OF f fA])
    fix \<kappa> assume "\<kappa> \<in> ?A"
    then obtain m where m: "\<kappa> = rproj ?K m" by blast
    have kk: "proj (kd X F)\<cdot>\<kappa> = \<kappa>" by (simp only: m proj_idem)
    have "populated_ext D (emind X) \<top> F \<kappa> \<odot> sem_ext X D F \<kappa> \<sqsubseteq> ?V \<kappa>"
      by (rule monofun_cfun [OF monofun_cfun_arg [OF populated_ext_sound [OF DD cD nD]] ext_soundD [OF X DD cD nD cf d kk]])
    moreover have "populated_ext D (emind X) \<top> F \<kappa> \<odot> sem_ext X D F \<kappa> + Absent \<sqsubseteq> populated_ext D (emind X) \<top> F \<kappa> \<odot> sem_ext X D F \<kappa>"
      by (rule plus_option_pd_below1)
    ultimately show "agg_member X D F k \<kappa> \<sqsubseteq> ?V \<kappa>" unfolding agg_member_def by (auto intro: below_trans)
  qed
  finally show ?thesis by (simp only: aggregate_simps rigid)
qed

theorem ext_sound_aggregate:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and X: "ext_sound X"
  shows "ext_sound (aggregate_ext f X)"
proof (rule ext_soundI, simp only: aggregate_ext_simps)
  fix D D' :: "('r, 'k) split_pd" and data F k
  assume DD: "D \<sqsubseteq> D'" and cD: "compact D'" and nD: "split_rows\<cdot>D' = up\<cdot>data"
    and cf: "conforms data" and d0: "fconf (evalues (aggregate f X)) data F"
  have d: "fconf (map release (evalues X)) data F" using d0 by simp
  have ub: "agg_approx f X D F k <| esem (aggregate f X) data F k"
  proof (rule is_ubI)
    fix v assume "v \<in> agg_approx f X D F k"
    then obtain D\<^sub>0 where v: "v = agg_glb f X D\<^sub>0 F k" and le: "D\<^sub>0 \<sqsubseteq> D" by (auto simp: agg_approx_def)
    show "v \<sqsubseteq> esem (aggregate f X) data F k" unfolding v by (rule agg_glb_sound [OF f X below_trans [OF le DD] cD nD cf d])
  qed
  have ne: "agg_approx f X D F k \<noteq> {}" unfolding agg_approx_def by auto
  show "agg_ext_sem f X D F k \<sqsubseteq> esem (aggregate f X) data F k"
    unfolding agg_ext_sem_def by (rule lub_belowI [OF ne ub])
qed

theorem ext_lawful_aggregate:
  "semilawful X \<Longrightarrow> ext_sound X \<Longrightarrow> abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b) \<Longrightarrow> ext_lawful (aggregate_ext f X)"
  unfolding ext_lawful_def using lawful_aggregate [of X f] by (simp add: lawful_def ext_sound_aggregate)


subsection \<open>Tuples\<close>

primrec tuple_ext :: "('k, 'f, 'r, 'a::domain) expr_ext list \<Rightarrow> ('k, 'f, 'r, 'a list u) expr_ext" where
  "tuple_ext [] = const_ext (up\<cdot>[])"
| "tuple_ext (X # Xs) = combine_ext (\<Lambda> v w. fup\<cdot>(\<Lambda> ys. up\<cdot>(v # ys))\<cdot>w) X (tuple_ext Xs)"

theorem ext_sound_tuple: "(\<And>X. X \<in> set Xs \<Longrightarrow> ext_sound X) \<Longrightarrow> ext_sound (tuple_ext Xs)"
proof (induct Xs)
  case Nil
  show ?case unfolding tuple_ext.simps const_ext_def by (rule ext_soundI) simp
next
  case (Cons X Xs)
  then show ?case by (simp add: ext_sound_combine)
qed


subsection \<open>Rigid parts\<close>

text \<open>The rigid combinators read only the rigid fields of their arguments, so an extended
  expression's rigid part is the rigid combinator applied to the rigid parts.\<close>

lemma truncate_with_ext [simp]: "expr.truncate (with_ext E s) = E"
  by (simp add: with_ext_def expr.defs expr_ext.defs)

lemma truncate_sel [simp]:
  "emind (expr.truncate X) = emind X" "eguards (expr.truncate X) = eguards X" "evalues (expr.truncate X) = evalues X"
  "esem (expr.truncate X) = esem X" "csem (expr.truncate X) = csem X"
  by (simp_all add: expr.defs)

lemma smap_truncate: "smap g (expr.truncate X) = smap g X"
  by (simp add: smap_def)

lemma restrict_truncate: "restrict \<gamma> (expr.truncate X) = restrict \<gamma> X"
  by (simp add: restrict_def)

lemma filtfor_truncate: "filtfor \<tau> G (expr.truncate X) = filtfor \<tau> G X"
  by (simp add: filtfor_def)

lemma include_dims_truncate: "include_dims M (expr.truncate X) = include_dims M X"
  by (simp add: include_dims_def)

lemma combine_truncate: "combine f (expr.truncate X\<^sub>1) (expr.truncate X\<^sub>2) = combine f X\<^sub>1 X\<^sub>2"
  by (simp add: combine_def combine_csem_def)

lemma aggregate_truncate: "aggregate f (expr.truncate X) = aggregate f X"
  by (simp add: aggregate_def inner_keys_def agg_csem_def)

lemma present_at_truncate: "present_at a \<rho> (expr.truncate X) = present_at a \<rho> X"
  by (simp add: present_at_def cong: option.case_cong)

lemma truncate_ext_simps:
  "expr.truncate (key_at_ext b) = key_at b" "expr.truncate (column_ext c a v) = column c a v"
  "expr.truncate (const_ext w) = const_expr w"
  "expr.truncate (smap_ext g X) = smap g (expr.truncate X)"
  "expr.truncate (restrict_ext \<gamma> X) = restrict \<gamma> (expr.truncate X)"
  "expr.truncate (filtfor_ext \<tau> G X) = filtfor \<tau> G (expr.truncate X)"
  "expr.truncate (include_dims_ext M X) = include_dims M (expr.truncate X)"
  "expr.truncate (combine_ext f X\<^sub>1 X\<^sub>2) = combine f (expr.truncate X\<^sub>1) (expr.truncate X\<^sub>2)"
  "expr.truncate (aggregate_ext h X) = aggregate h (expr.truncate X)"
  "expr.truncate (present_at_ext a \<rho> X) = present_at a \<rho> (expr.truncate X)"
  by (simp_all only: key_at_ext_def column_ext_def const_ext_def smap_ext_def restrict_ext_def filtfor_ext_def
      include_dims_ext_def combine_ext_def aggregate_ext_def present_at_ext_def truncate_with_ext
      smap_truncate restrict_truncate filtfor_truncate include_dims_truncate combine_truncate aggregate_truncate
      present_at_truncate)

lemma semilawful_truncate [simp]: "semilawful (expr.truncate X) \<longleftrightarrow> semilawful X"
  by (simp add: semilawful_def cstrict_def)

lemma truncate_tuple_ext: "expr.truncate (tuple_ext Xs) = tuple (map expr.truncate Xs)"
proof (induct Xs)
  case (Cons X Xs)
  have "expr.truncate (tuple_ext (X # Xs)) = combine (\<Lambda> v w. fup\<cdot>(\<Lambda> ys. up\<cdot>(v # ys))\<cdot>w) X (tuple_ext Xs)"
    by (simp only: tuple_ext.simps combine_ext_def truncate_with_ext)
  also have "\<dots> = combine (\<Lambda> v w. fup\<cdot>(\<Lambda> ys. up\<cdot>(v # ys))\<cdot>w) (expr.truncate X) (expr.truncate (tuple_ext Xs))"
    by (rule combine_truncate [symmetric])
  finally show ?case by (simp only: Cons list.map tuple.simps)
qed (simp add: const_ext_def)

theorem ext_lawful_tuple: "(\<And>X. X \<in> set Xs \<Longrightarrow> ext_lawful X) \<Longrightarrow> ext_lawful (tuple_ext Xs)"
proof -
  assume X: "\<And>X. X \<in> set Xs \<Longrightarrow> ext_lawful X"
  have "semilawful (expr.truncate (tuple_ext Xs))" unfolding truncate_tuple_ext
    by (rule semilawful_tuple) (auto dest: X simp: ext_lawful_def)
  then have "semilawful (tuple_ext Xs)" by (simp only: semilawful_truncate)
  moreover have "ext_sound (tuple_ext Xs)" by (rule ext_sound_tuple) (simp add: X [unfolded ext_lawful_def])
  ultimately show ?thesis unfolding ext_lawful_def ..
qed


subsection \<open>Monotonicity of the combinators below conforming datasets\<close>

theorem ext_mono_const: "ext_mono (const_ext v)"
  by (rule ext_monoI) simp

theorem ext_mono_smap: "ext_mono X \<Longrightarrow> ext_mono (smap_ext g X)"
  by (rule ext_monoI) (simp add: monofun_cfun_arg ext_monoD)

theorem ext_mono_restrict: "ext_mono X \<Longrightarrow> ext_mono (restrict_ext \<gamma> X)"
  unfolding ext_mono_def by simp

theorem ext_mono_filtfor: "ext_mono X \<Longrightarrow> ext_mono (filtfor_ext \<tau> G X)"
  unfolding ext_mono_def by (simp add: lod_bounded_ffor)

theorem ext_mono_include_dims: "lod_small M \<Longrightarrow> ext_mono X \<Longrightarrow> ext_mono (include_dims_ext M X)"
  unfolding ext_mono_def by (simp add: lod_bounded_finclude)

theorem ext_mono_combine: "ext_mono X\<^sub>1 \<Longrightarrow> ext_mono X\<^sub>2 \<Longrightarrow> ext_mono (combine_ext f X\<^sub>1 X\<^sub>2)"
  by (rule ext_monoI) (simp add: monofun_cfun monofun_cfun_arg ext_monoD)

theorem ext_mono_tuple: "(\<And>X. X \<in> set Xs \<Longrightarrow> ext_mono X) \<Longrightarrow> ext_mono (tuple_ext Xs)"
  by (induct Xs) (simp_all add: ext_mono_const const_ext_def [symmetric] ext_mono_combine)

subsection \<open>Continuity of the combinators\<close>

theorem ext_cont_const: "ext_cont (const_ext v)"
  by (rule ext_contI2 [OF ext_mono_const]) simp

theorem ext_cont_smap:
  assumes X: "ext_cont X"
  shows "ext_cont (smap_ext g X)"
proof (rule ext_contI2 [OF ext_mono_smap [OF ext_cont_mono [OF X]]], simp only: smap_ext_simps)
  fix Y :: "nat \<Rightarrow> ('r, 'k) split_pd" and C F k
  assume F: "lod_bounded F" and Y: "chain Y" and cC: "conforming_rows (split_rows\<cdot>C)" and LC: "(\<Squnion>i. Y i) \<sqsubseteq> C"
  show "map_option_pd g\<cdot>(sem_ext X (\<Squnion>i. Y i) F k) \<sqsubseteq> (\<Squnion>i. map_option_pd g\<cdot>(sem_ext X (Y i) F k))"
    unfolding ext_cont_lub [OF X F Y cC LC] contlub_cfun_arg [OF ext_cont_chain [OF X F Y cC LC]] ..
qed

theorem ext_cont_restrict: "ext_cont X \<Longrightarrow> ext_cont (restrict_ext \<gamma> X)"
  unfolding ext_cont_def by simp

theorem ext_cont_filtfor: "ext_cont X \<Longrightarrow> ext_cont (filtfor_ext \<tau> G X)"
  unfolding ext_cont_def by (simp add: lod_bounded_ffor)

theorem ext_cont_include_dims: "lod_small M \<Longrightarrow> ext_cont X \<Longrightarrow> ext_cont (include_dims_ext M X)"
  unfolding ext_cont_def by (simp add: lod_bounded_finclude)

theorem ext_cont_combine:
  assumes X\<^sub>1: "ext_cont X\<^sub>1" and X\<^sub>2: "ext_cont X\<^sub>2"
  shows "ext_cont (combine_ext f X\<^sub>1 X\<^sub>2)"
proof (rule ext_contI2 [OF ext_mono_combine [OF ext_cont_mono [OF X\<^sub>1] ext_cont_mono [OF X\<^sub>2]]], simp only: combine_ext_simps)
  fix Y :: "nat \<Rightarrow> ('r, 'k) split_pd" and C F k
  assume F: "lod_bounded F" and Y: "chain Y" and cC: "conforming_rows (split_rows\<cdot>C)" and LC: "(\<Squnion>i. Y i) \<sqsubseteq> C"
  let ?a = "\<lambda>i. sem_ext X\<^sub>1 (Y i) F (proj (kd X\<^sub>1 F)\<cdot>k)" and ?b = "\<lambda>i. sem_ext X\<^sub>2 (Y i) F (proj (kd X\<^sub>2 F)\<cdot>k)"
  have a: "chain ?a" and b: "chain ?b" by (rule ext_cont_chain [OF X\<^sub>1 F Y cC LC], rule ext_cont_chain [OF X\<^sub>2 F Y cC LC])
  have "lift2_option_pd f\<cdot>(\<Squnion>i. ?a i)\<cdot>(\<Squnion>i. ?b i) = (\<Squnion>i. lift2_option_pd f\<cdot>(?a i)\<cdot>(?b i))"
    by (simp add: contlub_cfun_arg [OF a] lub_APP [OF ch2ch_Rep_cfunR [OF a] b])
  then show "lift2_option_pd f\<cdot>(sem_ext X\<^sub>1 (\<Squnion>i. Y i) F (proj (kd X\<^sub>1 F)\<cdot>k))\<cdot>(sem_ext X\<^sub>2 (\<Squnion>i. Y i) F (proj (kd X\<^sub>2 F)\<cdot>k))
      \<sqsubseteq> (\<Squnion>i. lift2_option_pd f\<cdot>(?a i)\<cdot>(?b i))"
    by (simp only: ext_cont_lub [OF X\<^sub>1 F Y cC LC] ext_cont_lub [OF X\<^sub>2 F Y cC LC] below_refl)
qed

theorem ext_cont_tuple: "(\<And>X. X \<in> set Xs \<Longrightarrow> ext_cont X) \<Longrightarrow> ext_cont (tuple_ext Xs)"
  by (induct Xs) (simp_all add: ext_cont_const const_ext_def [symmetric] ext_cont_combine)

text \<open>A definite row at a compact key part maximal at \<open>c\<close> makes that key part possible: at each
  basis element above a compact approximation of the row, a generator above it carries the key
  part, and its key is above a possible key.\<close>

lemma definite_maximal_possible:
  assumes y: "split_definite y D" and c: "compact (rproj c y)" and mx: "maximal_at c (rproj c y)"
  shows "split_possible_at c (rproj c y) D"
proof -
  obtain y' where y': "compact y'" "y' \<sqsubseteq> y" "(proj c oo row_key)\<cdot>y' = (proj c oo row_key)\<cdot>y"
    by (rule compact_approx_value [of "proj c oo row_key" y]) (simp add: c)
  have ky: "rproj c y' = rproj c y" using y'(3) by simp
  have dy: "split_definite y' D" by (rule split_definite_below [OF y y'(2)])
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and DZ: "D = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  obtain i0 where i0: "split_definite y' (split_principal (Z i0))"
    using split_definite_lub_compact [OF ch y'(1)] dy DZ by blast
  have p: "split_possible_at c (rproj c y) (split_principal (Z (j + i0)))" for j
  proof -
    have "split_definite y' (split_principal (Z (j + i0)))"
      by (rule split_definite_mono [OF i0 chain_mono [OF ch]]) simp
    then have "split_definite (Rep_compact_basis (Abs_compact_basis y')) (split_principal (Z (j + i0)))"
      by (simp only: Abs_compact_basis_inverse' [OF y'(1)])
    then obtain x where x0: "x \<in> srows (Z (j + i0))" "Abs_compact_basis y' \<sqsubseteq> x"
      unfolding split_definite_principal by blast
    have x: "x \<in> srows (Z (j + i0))" "y' \<sqsubseteq> Rep_compact_basis x"
      using x0 unfolding compact_le_def Abs_compact_basis_inverse' [OF y'(1)] by simp_all
    obtain u where u: "u \<in> skeys (Z (j + i0))" "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
      using split_basis_consistentD [OF x(1)] by blast
    have "split_possible (Rep_compact_basis u) (split_principal (Z (j + i0)))"
      using u(1) by (auto simp: split_possible_principal)
    then have "split_possible (row_key\<cdot>(Rep_compact_basis x)) (split_principal (Z (j + i0)))"
      by (rule split_possible_up [OF _ u(2)])
    then have p: "split_possible_at c (rproj c (Rep_compact_basis x)) (split_principal (Z (j + i0)))"
      by (rule split_possible_atI)
    have "rproj c y' \<sqsubseteq> rproj c (Rep_compact_basis x)" by (intro monofun_cfun_arg x(2))
    then have "rproj c (Rep_compact_basis x) = rproj c y"
      unfolding ky by (rule maximal_at_eq [OF mx proj_idem])
    then show ?thesis using p by simp
  qed
  have ch': "chain (\<lambda>j. split_principal (Z (j + i0)))" by (rule chain_shift [OF ch])
  have "split_possible_at c (rproj c y) (\<Squnion>j. split_principal (Z (j + i0)))" by (rule split_possible_at_lub [OF ch' p])
  then show ?thesis unfolding lub_range_shift [OF ch] DZ .
qed

text \<open>At a compact key part a definite row passing the key test is not refuted: at a stage
  where both are witnessed, the row's generator carries a possible key below its key, at the same
  maximal part.  Impossibility refutes any key test: at a stage, no possible key may end up there.\<close>

lemma select_refuted_not_TT:
  assumes k: "compact \<kappa>" and mx: "maximal_at s \<kappa>" and y: "split_definite y D" and ky: "rproj s y = \<kappa>"
    and hy: "h\<cdot>(row_key\<cdot>y) = TT" and r: "split_refuted s \<kappa> h D"
  shows False
proof -
  let ?f = "\<Lambda> y. (rproj s y, h\<cdot>(row_key\<cdot>y))"
  obtain y' where y': "compact y'" "y' \<sqsubseteq> y" "?f\<cdot>y' = ?f\<cdot>y"
    by (rule compact_approx_value [of ?f y]) (simp add: ky hy k compact_TT)
  have ky': "rproj s y' = \<kappa>" and hy': "h\<cdot>(row_key\<cdot>y') = TT" using y'(3) ky hy by simp_all
  have dy: "split_definite y' D" by (rule split_definite_below [OF y y'(2)])
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and DZ: "D = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  obtain i0 where i0: "split_definite y' (split_principal (Z i0))"
    using split_definite_lub_compact [OF ch y'(1)] dy DZ by blast
  obtain i1 where i1: "split_refuted s \<kappa> h (split_principal (Z i1))"
    using split_refuted_lub [OF ch] r DZ by blast
  let ?j = "i0 + i1"
  have dj: "split_definite y' (split_principal (Z ?j))" by (rule split_definite_mono [OF i0 chain_mono [OF ch]]) simp
  have rj: "split_refuted s \<kappa> h (split_principal (Z ?j))" by (rule split_refuted_mono [OF i1 chain_mono [OF ch]]) simp
  have "split_definite (Rep_compact_basis (Abs_compact_basis y')) (split_principal (Z ?j))"
    by (simp only: Abs_compact_basis_inverse' [OF y'(1)] dj)
  then obtain x where x0: "x \<in> srows (Z ?j)" "Abs_compact_basis y' \<sqsubseteq> x"
    unfolding split_definite_principal by blast
  have x: "x \<in> srows (Z ?j)" "y' \<sqsubseteq> Rep_compact_basis x"
    using x0 unfolding compact_le_def Abs_compact_basis_inverse' [OF y'(1)] by simp_all
  obtain u where u: "u \<in> skeys (Z ?j)" "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
    using split_basis_consistentD [OF x(1)] by blast
  have "split_possible (Rep_compact_basis u) (split_principal (Z ?j))"
    using u(1) by (auto simp: split_possible_principal)
  then have p: "split_possible (row_key\<cdot>(Rep_compact_basis x)) (split_principal (Z ?j))"
    by (rule split_possible_up [OF _ u(2)])
  have "rproj s y' \<sqsubseteq> rproj s (Rep_compact_basis x)" by (intro monofun_cfun_arg x(2))
  then have "rproj s (Rep_compact_basis x) = \<kappa>" unfolding ky' by (rule maximal_at_eq [OF mx proj_idem])
  then have "h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = FF" by (intro split_refuted_possible [OF rj p]) simp
  moreover have "TT \<sqsubseteq> h\<cdot>(row_key\<cdot>(Rep_compact_basis x))" unfolding hy' [symmetric] by (intro monofun_cfun_arg x(2))
  ultimately show False by simp
qed

text \<open>A compact definite row of a dataset given by a chain of basis elements lies below a generator
  at some stage.\<close>

lemma definite_chain_generator:
  assumes Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and y: "split_definite y (\<Squnion>i. split_principal (Z i))" and cy: "compact y"
  obtains i x where "x \<in> srows (Z i)" "y \<sqsubseteq> Rep_compact_basis x"
proof -
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  obtain i where i: "split_definite y (split_principal (Z i))" by (rule split_definite_lub_compact [OF ch cy y])
  have "split_definite (Rep_compact_basis (Abs_compact_basis y)) (split_principal (Z i))"
    by (simp only: Abs_compact_basis_inverse' [OF cy] i)
  then obtain x where x0: "x \<in> srows (Z i)" "Abs_compact_basis y \<sqsubseteq> x"
    unfolding split_definite_principal by blast
  have "y \<sqsubseteq> Rep_compact_basis x" using x0(2) unfolding compact_le_def Abs_compact_basis_inverse' [OF cy] .
  then show ?thesis using that x0(1) by blast
qed

lemma generator_definite: "x \<in> srows t \<Longrightarrow> split_definite (Rep_compact_basis x) (split_principal t)"
  unfolding split_definite_principal by blast

text \<open>At a compact key part the selection test reads only the selection: the definite rows at a
  maximal part passing the tests are those of the selected dataset, and refutation reads the
  selected possible keys.\<close>

lemma select_test_select:
  assumes k: "compact \<kappa>"
  shows "select_test s \<kappa> g h (split_select s \<kappa>\<cdot>D) = select_test s \<kappa> g h D"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and DZ: "D = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have Z': "\<forall>i. split_le (SSelect s \<kappa> (Z i)) (SSelect s \<kappa> (Z (Suc i)))" using Z SSelect_split_mono by blast
  have ch': "chain (\<lambda>i. split_principal (SSelect s \<kappa> (Z i)))" by (rule split_pd.ch2ch_principal [OF Z'])
  have SD: "split_select s \<kappa>\<cdot>D = (\<Squnion>i. split_principal (SSelect s \<kappa> (Z i)))"
    unfolding DZ by (simp add: contlub_cfun_arg [OF ch])
  let ?f = "\<Lambda> y. (rproj s y, g\<cdot>y, h\<cdot>(row_key\<cdot>y))"
  let ?T = "\<lambda>D. maximal_at s \<kappa> \<and> (\<exists>y. split_definite y D \<and> rproj s y = \<kappa> \<and> g\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)"
  have approx: "\<exists>y0. compact y0 \<and> y0 \<sqsubseteq> y \<and> rproj s y0 = \<kappa> \<and> g\<cdot>y0 = TT \<and> h\<cdot>(row_key\<cdot>y0) = TT"
    if ky: "rproj s y = \<kappa>" and gy: "g\<cdot>y = TT" and hy: "h\<cdot>(row_key\<cdot>y) = TT" for y
  proof -
    obtain y0 where "compact y0" "y0 \<sqsubseteq> y" "?f\<cdot>y0 = ?f\<cdot>y"
      by (rule compact_approx_value [of ?f y]) (simp add: gy hy k [folded ky] compact_TT)
    then show ?thesis using ky gy hy by auto
  qed
  have up: "g\<cdot>x = TT \<and> h\<cdot>(row_key\<cdot>x) = TT" if "y0 \<sqsubseteq> x" "g\<cdot>y0 = TT" "h\<cdot>(row_key\<cdot>y0) = TT" for x y0
  proof -
    have "TT \<sqsubseteq> g\<cdot>x" unfolding that(2) [symmetric] by (rule monofun_cfun_arg [OF that(1)])
    moreover have "TT \<sqsubseteq> h\<cdot>(row_key\<cdot>x)" unfolding that(3) [symmetric] by (intro monofun_cfun_arg that(1))
    ultimately show ?thesis by simp
  qed
  have "?T (split_select s \<kappa>\<cdot>D) \<longleftrightarrow> ?T D"
  proof
    assume "?T (split_select s \<kappa>\<cdot>D)"
    then obtain y where mx: "maximal_at s \<kappa>" and y: "split_definite y (split_select s \<kappa>\<cdot>D)" "rproj s y = \<kappa>"
      "g\<cdot>y = TT" "h\<cdot>(row_key\<cdot>y) = TT" by blast
    obtain y0 where y0: "compact y0" "y0 \<sqsubseteq> y" "g\<cdot>y0 = TT" "h\<cdot>(row_key\<cdot>y0) = TT"
      using approx [OF y(2-4)] by blast
    have "split_definite y0 (\<Squnion>i. split_principal (SSelect s \<kappa> (Z i)))"
      using split_definite_below [OF y(1) y0(2)] unfolding SD .
    then obtain i x where x: "x \<in> srows (SSelect s \<kappa> (Z i))" "y0 \<sqsubseteq> Rep_compact_basis x"
      by (rule definite_chain_generator [OF Z' _ y0(1)])
    have xZ: "x \<in> srows (Z i)" and xk: "rproj s (Rep_compact_basis x) = \<kappa>" using x(1) by simp_all
    have "split_definite (Rep_compact_basis x) D"
      by (rule split_definite_mono [OF generator_definite [OF xZ]]) (simp only: DZ is_ub_thelub [OF ch])
    then show "?T D" using mx xk up [OF x(2) y0(3,4)] by blast
  next
    assume "?T D"
    then obtain y where mx: "maximal_at s \<kappa>" and y: "split_definite y D" "rproj s y = \<kappa>"
      "g\<cdot>y = TT" "h\<cdot>(row_key\<cdot>y) = TT" by blast
    obtain y0 where y0: "compact y0" "y0 \<sqsubseteq> y" "rproj s y0 = \<kappa>" "g\<cdot>y0 = TT" "h\<cdot>(row_key\<cdot>y0) = TT"
      using approx [OF y(2-4)] by blast
    have "split_definite y0 (\<Squnion>i. split_principal (Z i))" using split_definite_below [OF y(1) y0(2)] unfolding DZ .
    then obtain i x where x: "x \<in> srows (Z i)" "y0 \<sqsubseteq> Rep_compact_basis x"
      by (rule definite_chain_generator [OF Z _ y0(1)])
    have "rproj s y0 \<sqsubseteq> rproj s (Rep_compact_basis x)" by (intro monofun_cfun_arg x(2))
    then have xk: "rproj s (Rep_compact_basis x) = \<kappa>" unfolding y0(3) by (rule maximal_at_eq [OF mx proj_idem])
    have xS: "x \<in> srows (SSelect s \<kappa> (Z i))" using x(1) xk mx by simp
    have "split_definite (Rep_compact_basis x) (split_select s \<kappa>\<cdot>D)"
      by (rule split_definite_mono [OF generator_definite [OF xS]]) (simp only: SD is_ub_thelub [OF ch'])
    then show "?T (split_select s \<kappa>\<cdot>D)" using mx xk up [OF x(2) y0(4,5)] by blast
  qed
  moreover have "split_refuted s \<kappa> h (split_select s \<kappa>\<cdot>D) \<longleftrightarrow> split_refuted s \<kappa> h D"
    unfolding split_refuted_def split_select_idem ..
  ultimately show ?thesis unfolding select_test_def by (simp only:)
qed

text \<open>The selection test is the plain presence test on the dataset as seen from the entry: selected
  at the part, filtered by the key guard and by the row guard.  Present where it has rows (at a
  maximal part, passing both guards), absent where it has no possible keys, undecided otherwise.\<close>

definition split_present :: "('r, 'k) split_pd \<Rightarrow> tr" where
  "split_present C = (if split_rows\<cdot>C \<noteq> \<bottom> then TT else if split_keys\<cdot>C = Top then FF else \<bottom>)"

lemma select_test_guarded:
  assumes k: "compact \<kappa>"
  shows "select_test s \<kappa> g h D = split_present (split_rowguard g\<cdot>(split_keyguard h\<cdot>(split_select s \<kappa>\<cdot>D)))"
proof -
  let ?C = "split_rowguard g\<cdot>(split_keyguard h\<cdot>(split_select s \<kappa>\<cdot>D))"
  let ?T = "maximal_at s \<kappa> \<and> (\<exists>y. split_definite y D \<and> rproj s y = \<kappa> \<and> g\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)"
  let ?B = "\<lambda>t. SRowGuard g (SKeyGuard h (SSelect s \<kappa> t))"
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and DZ: "D = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  have ch1: "chain (\<lambda>i. split_principal (SSelect s \<kappa> (Z i)))"
    by (rule split_pd.ch2ch_principal) (blast intro: Z [rule_format] SSelect_split_mono)
  have ch2: "chain (\<lambda>i. split_principal (SKeyGuard h (SSelect s \<kappa> (Z i))))"
    by (rule split_pd.ch2ch_principal) (blast intro: Z [rule_format] SKeyGuard_split_mono SSelect_split_mono)
  have chB: "chain (\<lambda>i. split_principal (?B (Z i)))"
    by (rule split_pd.ch2ch_principal) (blast intro: Z [rule_format] SRowGuard_split_mono SKeyGuard_split_mono SSelect_split_mono)
  have C: "?C = (\<Squnion>i. split_principal (?B (Z i)))"
  proof -
    have "split_select s \<kappa>\<cdot>D = (\<Squnion>i. split_principal (SSelect s \<kappa> (Z i)))"
      unfolding DZ contlub_cfun_arg [OF ch] by simp
    moreover have "split_keyguard h\<cdot>(\<Squnion>i. split_principal (SSelect s \<kappa> (Z i))) = (\<Squnion>i. split_principal (SKeyGuard h (SSelect s \<kappa> (Z i))))"
      unfolding contlub_cfun_arg [OF ch1] by simp
    moreover have "split_rowguard g\<cdot>(\<Squnion>i. split_principal (SKeyGuard h (SSelect s \<kappa> (Z i)))) = (\<Squnion>i. split_principal (?B (Z i)))"
      unfolding contlub_cfun_arg [OF ch2] by simp
    ultimately show ?thesis by simp
  qed
  have rows: "split_rows\<cdot>?C \<noteq> \<bottom> \<longleftrightarrow> (\<exists>i. srows (?B (Z i)) \<noteq> {})"
  proof -
    have e: "split_rows\<cdot>?C = (\<Squnion>i. split_rows\<cdot>(split_principal (?B (Z i))))"
      unfolding C by (rule contlub_cfun_arg [OF chB])
    have "split_rows\<cdot>?C \<noteq> \<bottom> \<longleftrightarrow> \<not> (\<forall>i. split_rows\<cdot>(split_principal (?B (Z i))) = \<bottom>)"
      unfolding e by (simp only: lub_eq_bottom_iff [OF ch2ch_Rep_cfunR [OF chB]])
    then show ?thesis by (simp only: split_rows_principal_bot) blast
  qed
  have tt: "?T \<longleftrightarrow> (\<exists>i. srows (?B (Z i)) \<noteq> {})"
  proof
    assume "?T"
    then obtain y where mx: "maximal_at s \<kappa>" and y: "split_definite y D" "rproj s y = \<kappa>" and gy: "g\<cdot>y = TT"
      and hy: "h\<cdot>(row_key\<cdot>y) = TT" by blast
    let ?f = "\<Lambda> y. (rproj s y, g\<cdot>y, h\<cdot>(row_key\<cdot>y))"
    obtain y0 where y0: "compact y0" "y0 \<sqsubseteq> y" "?f\<cdot>y0 = ?f\<cdot>y"
      by (rule compact_approx_value [of ?f y]) (simp add: gy hy k [folded y(2)] compact_TT)
    have e: "rproj s y0 = \<kappa>" "g\<cdot>y0 = TT" "h\<cdot>(row_key\<cdot>y0) = TT" using y0(3) y(2) gy hy by simp_all
    have "split_definite y0 (\<Squnion>i. split_principal (Z i))" using split_definite_below [OF y(1) y0(2)] unfolding DZ .
    then obtain i x where x: "x \<in> srows (Z i)" "y0 \<sqsubseteq> Rep_compact_basis x"
      by (rule definite_chain_generator [OF Z _ y0(1)])
    have "rproj s y0 \<sqsubseteq> rproj s (Rep_compact_basis x)" by (intro monofun_cfun_arg x(2))
    then have xk: "rproj s (Rep_compact_basis x) = \<kappa>" unfolding e(1) by (rule maximal_at_eq [OF mx proj_idem])
    have xg: "g\<cdot>(Rep_compact_basis x) = TT" by (rule TT_up [OF e(2) x(2)])
    have xh: "h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = TT" by (rule TT_up [OF e(3) monofun_cfun_arg [OF x(2)]])
    have "x \<in> srows (?B (Z i))" using x(1) xk xg xh mx by simp
    then show "\<exists>i. srows (?B (Z i)) \<noteq> {}" by blast
  next
    assume "\<exists>i. srows (?B (Z i)) \<noteq> {}"
    then obtain i x where x: "x \<in> srows (?B (Z i))" by blast
    then have xZ: "x \<in> srows (Z i)" and mx: "maximal_at s \<kappa>" and xk: "rproj s (Rep_compact_basis x) = \<kappa>"
      and xg: "g\<cdot>(Rep_compact_basis x) = TT" and xh: "h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = TT" by simp_all
    have "split_definite (Rep_compact_basis x) D"
      by (rule split_definite_mono [OF generator_definite [OF xZ]]) (simp only: DZ is_ub_thelub [OF ch])
    then show "?T" using mx xk xg xh by blast
  qed
  have ff: "split_refuted s \<kappa> h D \<longleftrightarrow> split_keys\<cdot>?C = Top"
    by (simp only: split_keys_rowguard split_refuted_keyguard)
  show ?thesis unfolding select_test_def split_present_def by (simp only: rows tt [symmetric] ff)
qed

lemma impossible_refuted:
  assumes n: "\<not> split_possible_at s \<kappa> D"
  shows "split_refuted s \<kappa> h D"
proof -
  obtain Z where Z: "\<forall>i. split_le (Z i) (Z (Suc i))" and DZ: "D = (\<Squnion>i. split_principal (Z i))"
    by (rule split_pd.obtain_principal_chain)
  have ch: "chain (\<lambda>i. split_principal (Z i))" by (rule split_pd.ch2ch_principal [OF Z])
  obtain i where i: "\<not> split_possible_at s \<kappa> (split_principal (Z i))"
    using split_possible_at_lub [OF ch] n DZ by blast
  have e: "skeys (SSelect s \<kappa> (Z i)) = {}"
  proof (rule ccontr)
    assume "skeys (SSelect s \<kappa> (Z i)) \<noteq> {}"
    then obtain u where u: "u \<in> skeys (Z i)" "proj s\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>" by auto
    have "split_possible (Rep_compact_basis u) (split_principal (Z i))"
      using u(1) by (auto simp: split_possible_principal)
    then have "split_possible_at s (proj s\<cdot>(Rep_compact_basis u)) (split_principal (Z i))" by (rule split_possible_atI)
    moreover have "down\<cdot>{proj s\<cdot>(Rep_compact_basis u)}\<sharp> \<sqsubseteq> down\<cdot>{\<kappa>}\<sharp>" by (simp add: down_beta below_Of u(2))
    ultimately have "split_possible_at s \<kappa> (split_principal (Z i))"
      unfolding split_possible_at_def by (rule below_trans)
    then show False using i by blast
  qed
  have "split_keys\<cdot>(split_select s \<kappa>\<cdot>(split_principal (Z i))) = Top"
    by (simp only: split_select_principal split_keys_principal skeys_upper_def e simp_thms if_True)
  then have "split_refuted s \<kappa> h (split_principal (Z i))" unfolding split_refuted_def by simp
  then show ?thesis unfolding DZ by (rule split_refuted_mono) (rule is_ub_thelub [OF ch])
qed

text \<open>At a compact key part the selection test is monotone and decided at a finite stage.\<close>

lemma select_test_FF_iff:
  "compact \<kappa> \<Longrightarrow> select_test s \<kappa> g h D = FF \<longleftrightarrow> split_refuted s \<kappa> h D"
  unfolding select_test_def by (auto dest: select_refuted_not_TT)

lemma select_test_impossible: "compact \<kappa> \<Longrightarrow> \<not> split_possible_at s \<kappa> D \<Longrightarrow> select_test s \<kappa> g h D = FF"
  by (simp add: select_test_FF_iff impossible_refuted)

lemma select_test_mono:
  assumes k: "compact \<kappa>" and le: "D \<sqsubseteq> D'"
  shows "select_test s \<kappa> g h D \<sqsubseteq> select_test s \<kappa> g h D'"
proof -
  let ?T = "\<lambda>D. maximal_at s \<kappa> \<and> (\<exists>y. split_definite y D \<and> rproj s y = \<kappa> \<and> g\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)"
  show ?thesis
  proof (cases "?T D")
    case True
    then obtain y where mx: "maximal_at s \<kappa>" and y: "split_definite y D" "rproj s y = \<kappa>" "g\<cdot>y = TT" "h\<cdot>(row_key\<cdot>y) = TT"
      by blast
    show ?thesis by (simp only: select_test_TT [OF mx y(1) y(2,3,4)] select_test_TT [OF mx split_definite_mono [OF y(1) le] y(2,3,4)] below_refl)
  next
    case nT: False
    show ?thesis
    proof (cases "split_refuted s \<kappa> h D")
      case False
      show ?thesis by (simp only: select_test_bot [OF nT False] minimal)
    next
      case r: True
      have r': "split_refuted s \<kappa> h D'" by (rule split_refuted_mono [OF r le])
      show ?thesis by (simp only: select_test_FF_iff [OF k, THEN iffD2, OF r] select_test_FF_iff [OF k, THEN iffD2, OF r'] below_refl)
    qed
  qed
qed

lemma select_test_lub:
  assumes k: "compact \<kappa>" and Y: "chain Y"
  shows "select_test s \<kappa> g h (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. select_test s \<kappa> g h (Y i))"
proof -
  let ?T = "\<lambda>D. maximal_at s \<kappa> \<and> (\<exists>y. split_definite y D \<and> rproj s y = \<kappa> \<and> g\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)"
  have ch: "chain (\<lambda>i. select_test s \<kappa> g h (Y i))" by (rule chainI) (simp add: select_test_mono [OF k] chainE [OF Y])
  have stage: "select_test s \<kappa> g h (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. select_test s \<kappa> g h (Y i))"
    if "select_test s \<kappa> g h (\<Squnion>i. Y i) = select_test s \<kappa> g h (Y i)" for i
    unfolding that by (rule is_ub_thelub [OF ch])
  show ?thesis
  proof (cases "?T (\<Squnion>i. Y i)")
    case True
    then obtain y where mx: "maximal_at s \<kappa>" and y: "split_definite y (\<Squnion>i. Y i)" "rproj s y = \<kappa>"
      and gy: "g\<cdot>y = TT" and hy: "h\<cdot>(row_key\<cdot>y) = TT" by blast
    let ?f = "\<Lambda> y. (rproj s y, g\<cdot>y, h\<cdot>(row_key\<cdot>y))"
    obtain y' where y': "compact y'" "y' \<sqsubseteq> y" "?f\<cdot>y' = ?f\<cdot>y"
      by (rule compact_approx_value [of ?f y]) (simp add: y(2) gy hy k compact_TT)
    obtain i where i: "split_definite y' (Y i)"
      by (rule split_definite_lub_compact [OF Y y'(1) split_definite_below [OF y(1) y'(2)]])
    have e: "rproj s y' = \<kappa>" "g\<cdot>y' = TT" "h\<cdot>(row_key\<cdot>y') = TT" using y'(3) y(2) gy hy by simp_all
    show ?thesis by (rule stage [of i]) (simp only: select_test_TT [OF mx y(1) y(2) gy hy] select_test_TT [OF mx i e])
  next
    case nT: False
    show ?thesis
    proof (cases "split_refuted s \<kappa> h (\<Squnion>i. Y i)")
      case False
      show ?thesis by (simp only: select_test_bot [OF nT False] minimal)
    next
      case r: True
      obtain i where i: "split_refuted s \<kappa> h (Y i)" by (rule split_refuted_lub [OF Y r])
      show ?thesis
        by (rule stage [of i]) (simp only: select_test_FF_iff [OF k, THEN iffD2, OF i] select_test_FF_iff [OF k, THEN iffD2, OF r])
    qed
  qed
qed

lemma select_test_chain_mult:
  assumes k: "compact \<kappa>" and Y: "chain Y" and x: "chain X"
  shows "select_test s \<kappa> g h (\<Squnion>i. Y i) \<odot> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. select_test s \<kappa> g h (Y i) \<odot> X i)"
proof -
  have t: "chain (\<lambda>i. select_test s \<kappa> g h (Y i))" by (rule chainI) (simp add: select_test_mono [OF k] chainE [OF Y])
  have "select_test s \<kappa> g h (\<Squnion>i. Y i) \<odot> (\<Squnion>i. X i) \<sqsubseteq> (\<Squnion>i. select_test s \<kappa> g h (Y i)) \<odot> (\<Squnion>i. X i)"
    by (intro monofun_cfun_fun monofun_cfun_arg select_test_lub [OF k Y])
  also have "\<dots> = (\<Squnion>i. select_test s \<kappa> g h (Y i) \<odot> X i)"
    by (simp add: contlub_cfun_arg [OF t] lub_APP [OF ch2ch_Rep_cfunR [OF t] x])
  finally show ?thesis .
qed

lemma key_at_sem_mono:
  assumes c: "lod_small c" and le: "D \<sqsubseteq> D'"
  shows "key_at_sem c D k \<sqsubseteq> key_at_sem c D' k"
  by (intro monofun_cfun_fun monofun_cfun_arg select_test_mono [OF lod_small_proj [OF c] le])

theorem ext_mono_key_at: "lod_small c \<Longrightarrow> ext_mono (key_at_ext c)"
  by (rule ext_monoI) (simp add: key_at_sem_mono)

theorem ext_cont_key_at:
  assumes c: "lod_small c"
  shows "ext_cont (key_at_ext c)"
proof (rule ext_contI2 [OF ext_mono_key_at [OF c]], simp only: key_at_ext_simps)
  fix Y :: "nat \<Rightarrow> ('r, 'k) split_pd" and k
  assume Y: "chain Y"
  show "key_at_sem c (\<Squnion>i. Y i) k \<sqsubseteq> (\<Squnion>i. key_at_sem c (Y i) k)"
    using select_test_chain_mult [OF lod_small_proj [OF c] Y chain_const [of "Present\<cdot>(proj c\<cdot>k)"], where s=c and g="\<Lambda> _. TT" and h="\<Lambda> _. TT"]
    by simp
qed

text \<open>At an LOD-bounded frame and a small lower part, the fiber's key parts are compact, and
  the presence test is monotone and decided at a finite stage.\<close>

lemma compact_fiber_key:
  assumes a: "lod_small a" and F: "lod_bounded F"
  shows "compact (proj (a \<squnion> (\<rho> \<sqinter> flod F))\<cdot>k)"
  using F unfolding lod_bounded_def
  by (intro lod_small_proj lod_small_sup [OF a] lod_small_below [OF _ lattice_meet_le2])

lemma populated_ext_FF:
  "lod_small a \<Longrightarrow> lod_bounded F \<Longrightarrow> \<not> split_possible_at (a \<squnion> (\<rho> \<sqinter> flod F)) (proj (a \<squnion> (\<rho> \<sqinter> flod F))\<cdot>k) D \<Longrightarrow>
     populated_ext D a \<rho> F k = FF"
  unfolding populated_ext_def by (rule select_test_impossible [OF compact_fiber_key])

lemma populated_ext_mono:
  assumes a: "lod_small a" and F: "lod_bounded F" and le: "D \<sqsubseteq> D'"
  shows "populated_ext D a \<rho> F k \<sqsubseteq> populated_ext D' a \<rho> F k"
  unfolding populated_ext_def by (rule select_test_mono [OF compact_fiber_key [OF a F] le])

lemma populated_ext_lub:
  assumes a: "lod_small a" and F: "lod_bounded F" and Y: "chain Y"
  shows "populated_ext (\<Squnion>i. Y i) a \<rho> F k \<sqsubseteq> (\<Squnion>i. populated_ext (Y i) a \<rho> F k)"
  unfolding populated_ext_def by (rule select_test_lub [OF compact_fiber_key [OF a F] Y])

theorem ext_mono_present_at: "lod_small (emind X \<squnion> a) \<Longrightarrow> ext_mono X \<Longrightarrow> ext_mono (present_at_ext a \<rho> X)"
  by (rule ext_monoI) (simp add: monofun_cfun monofun_cfun_arg populated_ext_mono ext_monoD)

theorem ext_cont_present_at:
  assumes m: "lod_small (emind X \<squnion> a)" and X: "ext_cont X"
  shows "ext_cont (present_at_ext a \<rho> X)"
proof (rule ext_contI2 [OF ext_mono_present_at [OF m ext_cont_mono [OF X]]], simp only: present_at_ext_simps)
  fix Y :: "nat \<Rightarrow> ('r, 'k) split_pd" and C F k
  assume F: "lod_bounded F" and Y: "chain Y" and cC: "conforming_rows (split_rows\<cdot>C)" and LC: "(\<Squnion>i. Y i) \<sqsubseteq> C"
  let ?t = "\<lambda>i. populated_ext (Y i) (emind X \<squnion> a) \<rho> F k" and ?x = "\<lambda>i. sem_ext X (Y i) F (proj (kd X F)\<cdot>k)"
  have t: "chain ?t" by (rule chainI) (simp add: populated_ext_mono [OF m F] chainE [OF Y])
  have x: "chain ?x" by (rule ext_cont_chain [OF X F Y cC LC])
  have "populated_ext (\<Squnion>i. Y i) (emind X \<squnion> a) \<rho> F k \<odot> sem_ext X (\<Squnion>i. Y i) F (proj (kd X F)\<cdot>k)
      \<sqsubseteq> (\<Squnion>i. ?t i) \<odot> (\<Squnion>i. ?x i)"
    unfolding ext_cont_lub [OF X F Y cC LC] by (intro monofun_cfun_fun monofun_cfun_arg populated_ext_lub [OF m F Y])
  also have "\<dots> = (\<Squnion>i. ?t i \<odot> ?x i)"
    by (simp add: contlub_cfun_arg [OF t] lub_APP [OF ch2ch_Rep_cfunR [OF t] x])
  finally show "populated_ext (\<Squnion>i. Y i) (emind X \<squnion> a) \<rho> F k \<odot> sem_ext X (\<Squnion>i. Y i) F (proj (kd X F)\<cdot>k)
      \<sqsubseteq> (\<Squnion>i. ?t i \<odot> ?x i)" .
qed

text \<open>A dataset with a definite row has rows.  With conforming rows and the column's dependency,
  the sections of the definite rows at a key maximal at the key part are bounded by the section of
  the data points there.\<close>

lemma definite_has_rows:
  assumes y: "split_definite y D"
  obtains data where "split_rows\<cdot>D = up\<cdot>data"
proof -
  have "up\<cdot>(lower_unit\<cdot>y) \<sqsubseteq> split_rows\<cdot>D"
    using monofun_cfun_arg [OF y [unfolded split_definite_def], of split_rows] by simp
  then have "split_rows\<cdot>D \<noteq> \<bottom>" by auto
  then show ?thesis using that by (cases "split_rows\<cdot>D") simp_all
qed

lemma col_sections_ub:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))" and cf: "conforming_rows (split_rows\<cdot>D)"
    and mx: "maximal_at a (proj a\<cdot>k)" and ne: "col_sections c a D k \<noteq> {}"
  shows "\<exists>b. col_sections c a D k <| b"
proof -
  obtain y0 where y0: "split_definite y0 D" "rproj a y0 = proj a\<cdot>k" using ne by (auto simp: col_sections_def)
  obtain data where d: "split_rows\<cdot>D = up\<cdot>data" by (rule definite_has_rows [OF y0(1)])
  have conf: "conforms data" using cf d by simp
  have P: "vfd (lower_maximal data) (\<bottom>, a) (c, \<bottom>)" by (rule universallyD [OF fd conf])
  have point: "\<exists>m. m \<in> lower_maximal data \<and> y \<sqsubseteq> m \<and> rproj a m = proj a\<cdot>k"
    if yd: "split_definite y D" and yk: "rproj a y = proj a\<cdot>k" for y
  proof -
    have "maximal_at a (rproj a y)" using mx yk by simp
    then obtain m where "m \<in> lower_maximal data" "y \<sqsubseteq> m" "rproj a m = rproj a y"
      using definite_maximal_point [OF below_refl d yd] by blast
    then show ?thesis using yk by auto
  qed
  obtain m0 where m0: "m0 \<in> lower_maximal data" "rproj a m0 = proj a\<cdot>k" using point [OF y0] by blast
  have "col_sections c a D k <| m0 \<downharpoonright> c"
  proof (rule is_ubI)
    fix z assume "z \<in> col_sections c a D k"
    then obtain y where y: "split_definite y D" "rproj a y = proj a\<cdot>k" "z = y \<downharpoonright> c" by (auto simp: col_sections_def)
    obtain m where m: "m \<in> lower_maximal data" "y \<sqsubseteq> m" "rproj a m = proj a\<cdot>k" using point [OF y(1,2)] by blast
    have "vpart (c, \<bottom>) m = vpart (c, \<bottom>) m0" by (rule vfdD [OF P m(1) m0(1)]) (simp add: m(3) m0(2) proj_bot)
    then have "m \<downharpoonright> c = m0 \<downharpoonright> c" by simp
    moreover have "y \<downharpoonright> c \<sqsubseteq> m \<downharpoonright> c" by (intro monofun_cfun_arg m(2))
    ultimately show "z \<sqsubseteq> m0 \<downharpoonright> c" using y(3) by simp
  qed
  then show ?thesis ..
qed

lemma col_sections_mono: "D \<sqsubseteq> D' \<Longrightarrow> col_sections c a D k \<subseteq> col_sections c a D' k"
  unfolding col_sections_def by (blast intro: split_definite_mono)

lemma lub_subset_below: "S \<noteq> {} \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T <| (b :: 'a::bounded_complete) \<Longrightarrow> lub S \<sqsubseteq> lub T"
  by (rule lub_belowI) (auto intro: below_lubI is_ub_upward simp: is_ub_def)

lemma col_value_mono_below:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))"
    and cf: "conforming_rows (split_rows\<cdot>C)" and le: "D \<sqsubseteq> D'" and le': "D' \<sqsubseteq> C"
  shows "col_value c a D k \<sqsubseteq> col_value c a D' k"
proof (cases "maximal_at a (proj a\<cdot>k) \<and> col_sections c a D k \<noteq> {}")
  case True
  then have mx: "maximal_at a (proj a\<cdot>k)" and ne: "col_sections c a D k \<noteq> {}" by simp_all
  have neC: "col_sections c a C k \<noteq> {}" using ne col_sections_mono [OF below_trans [OF le le'], of c a k] by blast
  obtain b where b: "col_sections c a C k <| b" using col_sections_ub [OF fd cf mx neC] by blast
  have b': "col_sections c a D' k <| b" using b col_sections_mono [OF le', of c a k] by (auto simp: is_ub_def)
  have "lub (col_sections c a D k) \<sqsubseteq> lub (col_sections c a D' k)"
    by (rule lub_subset_below [OF ne col_sections_mono [OF le] b'])
  then show ?thesis unfolding col_value_def by (simp only: if_P [OF mx])
next
  case False
  then show ?thesis unfolding col_value_def by (auto simp: lub_empty)
qed

lemma column_sem_mono_below:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))" and ca: "lod_small a"
    and cf: "conforming_rows (split_rows\<cdot>C)" and le: "D \<sqsubseteq> D'" and le': "D' \<sqsubseteq> C"
  shows "column_sem c a v D k \<sqsubseteq> column_sem c a v D' k"
  by (rule monofun_cfun [OF monofun_cfun_arg [OF select_test_mono [OF lod_small_proj [OF ca] le]]
        monofun_cfun_arg [OF monofun_cfun_arg [OF col_value_mono_below [OF fd cf le le']]]])

lemma column_sem_mono:
  "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>)) \<Longrightarrow> lod_small a \<Longrightarrow> conforming_rows (split_rows\<cdot>D') \<Longrightarrow> D \<sqsubseteq> D' \<Longrightarrow>
    column_sem c a v D k \<sqsubseteq> column_sem c a v D' k"
  by (rule column_sem_mono_below [OF _ _ _ _ below_refl])

theorem ext_mono_column:
  "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>)) \<Longrightarrow> lod_small a \<Longrightarrow> ext_mono (column_ext c a v)"
  by (rule ext_monoI) (simp add: column_sem_mono_below)

text \<open>The selected sections at the lub are approximated by sections at the stages, at the same key.\<close>

lemma col_value_lub:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))" and ca: "lod_small a"
    and Y: "chain Y" and cC: "conforming_rows (split_rows\<cdot>C)" and LC: "(\<Squnion>i. Y i) \<sqsubseteq> C"
  shows "col_value c a (\<Squnion>i. Y i) k \<sqsubseteq> (\<Squnion>i. col_value c a (Y i) k)"
proof (cases "maximal_at a (proj a\<cdot>k) \<and> col_sections c a (\<Squnion>i. Y i) k \<noteq> {}")
  case True
  let ?C = "\<lambda>D. maximal_at a (proj a\<cdot>k) \<and> col_sections c a D k \<noteq> {}"
  let ?L = "\<Squnion>i. Y i"
  have YC: "Y i \<sqsubseteq> C" for i by (rule ext_cont_below [OF LC Y])
  have ch: "chain (\<lambda>i. col_value c a (Y i) k)" by (rule chainI) (rule col_value_mono_below [OF fd cC chainE [OF Y] YC])
  have mx: "maximal_at a (proj a\<cdot>k)" and ne: "col_sections c a ?L k \<noteq> {}" using True by simp_all
  have kc: "compact (proj a\<cdot>k)" by (rule lod_small_proj [OF ca])
  obtain r :: "nat \<Rightarrow> 'r \<rightarrow> 'r" where r: "approx_chain r" using bifinite by blast
  interpret R: approx_chain r by (fact r)
  have approx: "\<exists>j y'. y' \<in> col_sections c a (Y j) k \<and> r n\<cdot>z \<sqsubseteq> y'" if z: "z \<in> col_sections c a ?L k" for z n
  proof -
    obtain y where y: "split_definite y ?L" "rproj a y = proj a\<cdot>k" "z = y \<downharpoonright> c"
      using z by (auto simp: col_sections_def)
    let ?f = "\<Lambda> y. (rproj a y, r n\<cdot>(y \<downharpoonright> c))"
    have "compact (?f\<cdot>y)" by (simp add: y(2) kc finite_deflation.compact [OF R.finite_deflation_approx])
    then obtain y' where y': "compact y'" "y' \<sqsubseteq> y" "?f\<cdot>y' = ?f\<cdot>y" by (rule compact_approx_value)
    obtain j where j: "split_definite y' (Y j)"
      by (rule split_definite_lub_compact [OF Y y'(1) split_definite_below [OF y(1) y'(2)]])
    have "y' \<downharpoonright> c \<in> col_sections c a (Y j) k" using j y'(3) y(2) by (auto simp: col_sections_def)
    moreover have "r n\<cdot>z \<sqsubseteq> y' \<downharpoonright> c"
    proof -
      have "r n\<cdot>z = r n\<cdot>(y' \<downharpoonright> c)" using y'(3) y(3) by simp
      also have "\<dots> \<sqsubseteq> y' \<downharpoonright> c" by (rule deflation.below [OF finite_deflation_imp_deflation [OF R.finite_deflation_approx]])
      finally show ?thesis .
    qed
    ultimately show ?thesis by blast
  qed
  obtain z0 where z0: "z0 \<in> col_sections c a ?L k" using ne by blast
  obtain i0 y0 where i0: "y0 \<in> col_sections c a (Y i0) k" using approx [OF z0, of 0] by blast
  have Ci: "?C (Y (j + i0))" for j using mx col_sections_mono [OF chain_mono [OF Y le_add2]] i0 by blast
  let ?l = "\<lambda>j. lub (col_sections c a (Y (j + i0)) k)"
  have ub: "\<exists>b. col_sections c a (Y (j + i0)) k <| b" for j
  proof -
    have sub: "col_sections c a (Y (j + i0)) k \<subseteq> col_sections c a C k" by (rule col_sections_mono [OF YC])
    have "col_sections c a C k \<noteq> {}" using Ci [of j] sub by blast
    then obtain b where "col_sections c a C k <| b" using col_sections_ub [OF fd cC mx] by blast
    then show ?thesis using sub by (auto simp: is_ub_def)
  qed
  have l: "?l j = col_value c a (Y (j + i0)) k" for j unfolding col_value_def by (simp only: if_P [OF mx])
  have lch: "chain ?l" unfolding l by (rule chain_shift [OF ch])
  have sec: "z \<sqsubseteq> ?l j" if "z \<in> col_sections c a (Y j') k" "j' \<le> j + i0" for z j j'
  proof -
    obtain b where b: "col_sections c a (Y (j + i0)) k <| b" using ub by blast
    have "z \<in> col_sections c a (Y (j + i0)) k" using that col_sections_mono [OF chain_mono [OF Y that(2)]] by blast
    then show ?thesis by (rule below_lubI [OF b, rotated])
  qed
  have below: "lub (col_sections c a ?L k) \<sqsubseteq> (\<Squnion>j. ?l j)"
  proof (rule lub_belowI [OF ne], rule is_ubI)
    fix z assume z: "z \<in> col_sections c a ?L k"
    have "r n\<cdot>z \<sqsubseteq> (\<Squnion>j. ?l j)" for n
    proof -
      obtain j y' where y': "y' \<in> col_sections c a (Y j) k" "r n\<cdot>z \<sqsubseteq> y'" using approx [OF z] by blast
      have "y' \<sqsubseteq> ?l j" by (rule sec [OF y'(1)]) simp
      then show ?thesis by (rule below_trans [OF y'(2) below_trans [OF _ is_ub_thelub [OF lch]]])
    qed
    then have "(\<Squnion>n. r n\<cdot>z) \<sqsubseteq> (\<Squnion>j. ?l j)" by (intro lub_below ch2ch_Rep_cfunL R.chain_approx)
    then show "z \<sqsubseteq> (\<Squnion>j. ?l j)" by (simp add: contlub_cfun_fun [OF R.chain_approx, symmetric] R.lub_approx)
  qed
  have "col_value c a ?L k = lub (col_sections c a ?L k)" unfolding col_value_def by (simp only: if_P [OF mx])
  also have "\<dots> \<sqsubseteq> (\<Squnion>j. col_value c a (Y (j + i0)) k)" using below by (simp only: l)
  also have "\<dots> = (\<Squnion>i. col_value c a (Y i) k)" by (rule lub_range_shift [OF ch])
  finally show ?thesis .
next
  case False
  then show ?thesis unfolding col_value_def by (auto simp: lub_empty)
qed

theorem ext_cont_column:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))" and ca: "lod_small a"
  shows "ext_cont (column_ext c a v)"
proof (rule ext_contI2 [OF ext_mono_column [OF fd ca]], simp only: column_ext_simps)
  fix Y :: "nat \<Rightarrow> ('r, 'k) split_pd" and C k
  assume Y: "chain Y" and cC: "conforming_rows (split_rows\<cdot>C)" and LC: "(\<Squnion>i. Y i) \<sqsubseteq> C"
  have YC: "Y i \<sqsubseteq> C" for i by (rule ext_cont_below [OF LC Y])
  have ch: "chain (\<lambda>i. col_value c a (Y i) k)" by (rule chainI) (rule col_value_mono_below [OF fd cC chainE [OF Y] YC])
  let ?x = "\<lambda>i. Present\<cdot>(v\<cdot>(col_value c a (Y i) k))"
  have x: "chain ?x" by (rule chainI) (intro monofun_cfun_arg chainE [OF ch])
  have "Present\<cdot>(v\<cdot>(col_value c a (\<Squnion>i. Y i) k)) \<sqsubseteq> Present\<cdot>(v\<cdot>(\<Squnion>i. col_value c a (Y i) k))"
    by (intro monofun_cfun_arg col_value_lub [OF fd ca Y cC LC])
  also have "\<dots> = (\<Squnion>i. ?x i)" by (simp add: contlub_cfun_arg [OF ch] contlub_cfun_arg [OF ch2ch_Rep_cfunR [OF ch]])
  finally have xl: "Present\<cdot>(v\<cdot>(col_value c a (\<Squnion>i. Y i) k)) \<sqsubseteq> (\<Squnion>i. ?x i)" .
  have "column_sem c a v (\<Squnion>i. Y i) k \<sqsubseteq> select_test a (proj a\<cdot>k) (\<Lambda> _. TT) (\<Lambda> _. TT) (\<Squnion>i. Y i) \<odot> (\<Squnion>i. ?x i)"
    by (intro monofun_cfun_arg xl)
  also have "\<dots> \<sqsubseteq> (\<Squnion>i. column_sem c a v (Y i) k)"
    by (rule select_test_chain_mult [OF lod_small_proj [OF ca] Y x])
  finally show "column_sem c a v (\<Squnion>i. Y i) k \<sqsubseteq> (\<Squnion>i. column_sem c a v (Y i) k)" .
qed


subsection \<open>Monotonicity and continuity of aggregation\<close>

text \<open>A compact dataset has finitely many definite inner keys: they are those of its generators.\<close>

lemma agg_definite_finite:
  assumes cD: "compact D"
  shows "finite (agg_definite X D F k)"
proof -
  obtain t where t: "D = split_principal t" using split_pd.compact_imp_principal [OF cD] by blast
  let ?K = "kd X F"
  have "agg_definite X D F k \<subseteq> (\<lambda>s. rproj ?K (Rep_compact_basis s)) ` srows t"
  proof
    fix \<kappa> assume "\<kappa> \<in> agg_definite X D F k"
    then obtain y where mx: "maximal_at ?K \<kappa>" and y: "split_definite y D" "rproj ?K y = \<kappa>"
      by (auto simp: agg_definite_def)
    obtain data where d: "split_rows\<cdot>D = up\<cdot>data" by (rule definite_has_rows [OF y(1)])
    have "y \<in>\<flat> data" by (rule split_definite_rows_mem [OF y(1) d])
    then obtain s where s: "s \<in> srows t" "y \<sqsubseteq> Rep_compact_basis s" using split_rows_mem_principal [OF d [unfolded t]] by blast
    have "rproj ?K y \<sqsubseteq> rproj ?K (Rep_compact_basis s)" by (intro monofun_cfun_arg s(2))
    then have "rproj ?K (Rep_compact_basis s) = \<kappa>" unfolding y(2) by (rule maximal_at_eq [OF mx proj_idem])
    then show "\<kappa> \<in> (\<lambda>s. rproj ?K (Rep_compact_basis s)) ` srows t" using s(1) by force
  qed
  then show ?thesis by (rule finite_subset) (simp add: finite_srows)
qed

lemma agg_definite_mono: "D \<sqsubseteq> D' \<Longrightarrow> agg_definite X D F k \<subseteq> agg_definite X D' F k"
  unfolding agg_definite_def by (blast intro: split_definite_mono)

lemma agg_possible_mono: "D \<sqsubseteq> D' \<Longrightarrow> agg_possible X D' F k \<subseteq> agg_possible X D F k"
  unfolding agg_possible_def by (blast intro: split_possible_at_below)

text \<open>At an LOD-bounded frame and a small minimal LOD, definite inner keys are possible.\<close>

lemma agg_definite_possible:
  assumes m: "lod_small (emind X)" and F: "lod_bounded F"
  shows "agg_definite X D F k \<subseteq> agg_possible X D F k"
proof
  fix \<kappa> assume "\<kappa> \<in> agg_definite X D F k"
  then obtain y where mx: "maximal_at (kd X F) \<kappa>" and k: "proj (flod F)\<cdot>\<kappa> = k"
    and r: "\<kappa> \<in> Rep_cfun (proj (kd X F)) ` conforming_keyspace"
    and y: "split_definite y D" "rproj (kd X F) y = \<kappa>" by (auto simp: agg_definite_def)
  have c: "compact (rproj (kd X F) y)"
    using F unfolding lod_bounded_def by (intro lod_small_proj lod_small_sup [OF m])
  have "split_possible_at (kd X F) \<kappa> D"
    using definite_maximal_possible [OF y(1) c] mx y(2) by simp
  then show "\<kappa> \<in> agg_possible X D F k" unfolding agg_possible_def using k r by blast
qed

lemma agg_glb_mono:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and X: "ext_mono X" and m: "lod_small (emind X)" and F: "lod_bounded F"
    and cC: "conforming_rows (split_rows\<cdot>C)" and le: "D \<sqsubseteq> D'" and le': "D' \<sqsubseteq> C" and cD': "compact D'"
  shows "agg_glb f X D F k \<sqsubseteq> agg_glb f X D' F k"
proof -
  let ?Def = "agg_definite X D F k" and ?Def' = "agg_definite X D' F k"
  let ?S = "\<lambda>D. {agg_fold f (agg_member X D F k) (agg_definite X D F k \<union> C) | C. finite C \<and> C \<subseteq> agg_possible X D F k}"
  have ne: "?S D' \<noteq> {}" by blast
  show ?thesis unfolding agg_glb_def
  proof (rule glb_greatest [OF ne], intro ballI)
    fix x assume "x \<in> ?S D'"
    then obtain C' where x: "x = agg_fold f (agg_member X D' F k) (?Def' \<union> C')" and fC': "finite C'"
      and C': "C' \<subseteq> agg_possible X D' F k" by blast
    let ?C'' = "(?Def' - ?Def) \<union> C'"
    have fD': "finite ?Def'" by (rule agg_definite_finite [OF cD'])
    have sub: "?C'' \<subseteq> agg_possible X D F k"
      using agg_definite_possible [OF m F, of D'] C' agg_possible_mono [OF le] by blast
    have eq: "?Def \<union> ?C'' = ?Def' \<union> C'" using agg_definite_mono [OF le] by blast
    have "glb (?S D) \<sqsubseteq> agg_fold f (agg_member X D F k) (?Def \<union> ?C'')"
      by (rule glb_below, rule CollectI, rule exI [of _ ?C'']) (use fD' fC' sub in simp)
    also have "\<dots> = agg_fold f (agg_member X D F k) (?Def' \<union> C')" by (simp only: eq)
    also have "\<dots> \<sqsubseteq> x" unfolding x
    proof (rule agg_fold_mono [OF f finite_UnI [OF fD' fC']])
      fix \<kappa>
      have V: "populated_ext D (emind X) \<top> F \<kappa> \<odot> sem_ext X D F \<kappa> \<sqsubseteq> populated_ext D' (emind X) \<top> F \<kappa> \<odot> sem_ext X D' F \<kappa>"
        by (intro monofun_cfun monofun_cfun_arg populated_ext_mono [OF m F le] ext_monoD [OF X F cC le le'])
      have dm: "?Def \<subseteq> ?Def'" by (rule agg_definite_mono [OF le])
      show "agg_member X D F k \<kappa> \<sqsubseteq> agg_member X D' F k \<kappa>"
      proof (cases "\<kappa> \<in> ?Def")
        case True
        then show ?thesis using V dm unfolding agg_member_def by auto
      next
        case nD: False
        have l: "populated_ext D (emind X) \<top> F \<kappa> \<odot> sem_ext X D F \<kappa> + Absent \<sqsubseteq> populated_ext D' (emind X) \<top> F \<kappa> \<odot> sem_ext X D' F \<kappa>"
          by (rule below_trans [OF plus_option_pd_below1 V])
        show ?thesis
        proof (cases "\<kappa> \<in> ?Def'")
          case True
          then show ?thesis using nD l unfolding agg_member_def by simp
        next
          case False
          then show ?thesis using nD unfolding agg_member_def
            by (simp add: plus_option_pd_greatest [OF l plus_option_pd_below2])
        qed
      qed
    qed
    finally show "glb (?S D) \<sqsubseteq> x" .
  qed
qed

text \<open>Below a conforming dataset, the folds at the compact datasets below form a directed set: the
  compact datasets below are directed, and the fold grows along them.\<close>

lemma agg_approx_directed:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and X: "ext_mono X" and m: "lod_small (emind X)" and F: "lod_bounded F"
    and cC: "conforming_rows (split_rows\<cdot>C)" and DC: "D \<sqsubseteq> C"
  shows "directed (agg_approx f X D F k)"
  unfolding directed_def
proof (intro ballI)
  fix x y assume "x \<in> agg_approx f X D F k" "y \<in> agg_approx f X D F k"
  then obtain D\<^sub>1 D\<^sub>2 where x: "x = agg_glb f X D\<^sub>1 F k" "compact D\<^sub>1" "D\<^sub>1 \<sqsubseteq> D"
    and y: "y = agg_glb f X D\<^sub>2 F k" "compact D\<^sub>2" "D\<^sub>2 \<sqsubseteq> D" by (auto simp: agg_approx_def)
  obtain t\<^sub>1 t\<^sub>2 where t: "D\<^sub>1 = split_principal t\<^sub>1" "D\<^sub>2 = split_principal t\<^sub>2"
    using split_pd.compact_imp_principal [OF x(2)] split_pd.compact_imp_principal [OF y(2)] by blast
  have "t\<^sub>1 \<in> Rep_split_pd D" "t\<^sub>2 \<in> Rep_split_pd D"
    using x(3) y(3) unfolding t split_pd.principal_below_iff_mem_rep by simp_all
  then obtain t\<^sub>3 where t3: "t\<^sub>3 \<in> Rep_split_pd D" "split_le t\<^sub>1 t\<^sub>3" "split_le t\<^sub>2 t\<^sub>3"
    using split_le.idealD2 [OF split_pd.ideal_rep] by blast
  let ?D = "split_principal t\<^sub>3"
  have D3: "compact ?D" "?D \<sqsubseteq> D" using t3(1) by (simp_all add: split_pd.compact_principal split_pd.principal_below_iff_mem_rep)
  have D3C: "?D \<sqsubseteq> C" by (rule below_trans [OF D3(2) DC])
  have "x \<sqsubseteq> agg_glb f X ?D F k" unfolding x(1) t(1)
    by (rule agg_glb_mono [OF f X m F cC split_pd.principal_mono [OF t3(2)] D3C D3(1)])
  moreover have "y \<sqsubseteq> agg_glb f X ?D F k" unfolding y(1) t(2)
    by (rule agg_glb_mono [OF f X m F cC split_pd.principal_mono [OF t3(3)] D3C D3(1)])
  moreover have "agg_glb f X ?D F k \<in> agg_approx f X D F k" using D3 by (auto simp: agg_approx_def)
  ultimately show "\<exists>z\<in>agg_approx f X D F k. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" by blast
qed

lemma agg_approx_mono: "D \<sqsubseteq> D' \<Longrightarrow> agg_approx f X D F k \<subseteq> agg_approx f X D' F k"
  unfolding agg_approx_def by (blast intro: below_trans)

theorem ext_mono_aggregate:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and X: "ext_mono X" and m: "lod_small (emind X)"
  shows "ext_mono (aggregate_ext f X)"
proof (rule ext_monoI, simp only: aggregate_ext_simps)
  fix D D' C :: "('r, 'k) split_pd" and F k
  assume F: "lod_bounded F" and cC: "conforming_rows (split_rows\<cdot>C)" and le: "D \<sqsubseteq> D'" and le': "D' \<sqsubseteq> C"
  have d: "agg_approx f X D F k <<| lub (agg_approx f X D F k)"
    by (rule directed_lub [OF agg_approx_directed [OF f X m F cC below_trans [OF le le']]])
  have d': "agg_approx f X D' F k <<| lub (agg_approx f X D' F k)"
    by (rule directed_lub [OF agg_approx_directed [OF f X m F cC le']])
  have "agg_approx f X D F k <| lub (agg_approx f X D' F k)"
    using is_lubD1 [OF d'] agg_approx_mono [OF le, of f X F k] by (auto simp: is_ub_def)
  then show "agg_ext_sem f X D F k \<sqsubseteq> agg_ext_sem f X D' F k" unfolding agg_ext_sem_def by (rule is_lubD2 [OF d])
qed

theorem ext_cont_aggregate:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and X: "ext_cont X" and m: "lod_small (emind X)"
  shows "ext_cont (aggregate_ext f X)"
proof (rule ext_contI2 [OF ext_mono_aggregate [OF f ext_cont_mono [OF X] m]], simp only: aggregate_ext_simps)
  fix Y :: "nat \<Rightarrow> ('r, 'k) split_pd" and C F k
  assume F: "lod_bounded F" and Y: "chain Y" and cC: "conforming_rows (split_rows\<cdot>C)" and LC: "(\<Squnion>i. Y i) \<sqsubseteq> C"
  note Xm = ext_cont_mono [OF X]
  have YC: "Y i \<sqsubseteq> C" for i by (rule ext_cont_below [OF LC Y])
  have di: "agg_approx f X (Y i) F k <<| agg_ext_sem f X (Y i) F k" for i
    unfolding agg_ext_sem_def by (rule directed_lub [OF agg_approx_directed [OF f Xm m F cC YC]])
  have ch: "chain (\<lambda>i. agg_ext_sem f X (Y i) F k)"
    using ext_monoD [OF ext_mono_aggregate [OF f Xm m] F cC chainE [OF Y] YC] by (intro chainI) simp
  have dL: "agg_approx f X (\<Squnion>i. Y i) F k <<| agg_ext_sem f X (\<Squnion>i. Y i) F k"
    unfolding agg_ext_sem_def by (rule directed_lub [OF agg_approx_directed [OF f Xm m F cC LC]])
  have "agg_approx f X (\<Squnion>i. Y i) F k <| (\<Squnion>i. agg_ext_sem f X (Y i) F k)"
  proof (rule is_ubI)
    fix x assume "x \<in> agg_approx f X (\<Squnion>i. Y i) F k"
    then obtain D\<^sub>0 where x: "x = agg_glb f X D\<^sub>0 F k" "compact D\<^sub>0" "D\<^sub>0 \<sqsubseteq> (\<Squnion>i. Y i)" by (auto simp: agg_approx_def)
    obtain i where i: "D\<^sub>0 \<sqsubseteq> Y i" using compact_below_lub_iff [OF x(2) Y] x(3) by blast
    have "x \<in> agg_approx f X (Y i) F k" using x(1,2) i by (auto simp: agg_approx_def)
    then have "x \<sqsubseteq> agg_ext_sem f X (Y i) F k" using is_lubD1 [OF di] by (auto simp: is_ub_def)
    then show "x \<sqsubseteq> (\<Squnion>i. agg_ext_sem f X (Y i) F k)" by (rule below_trans [OF _ is_ub_thelub [OF ch]])
  qed
  then show "agg_ext_sem f X (\<Squnion>i. Y i) F k \<sqsubseteq> (\<Squnion>i. agg_ext_sem f X (Y i) F k)" by (rule is_lubD2 [OF dL])
qed

end

end
