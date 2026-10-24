theory Views
  imports Schema
begin

default_sort "{bifinite, distributive_cpo}"

section \<open>Views and functional dependencies\<close>

text \<open>A \<^emph>\<open>view\<close> reads a section of the row and a part of its key: a pair of a column-side and a
  key-side semi-factor.  Functional dependencies between views cover all four combinations of
  sides (columns to columns, columns to keys, keys to columns, keys to keys) at once.  The key of a
  row is computed from a declared column support, so columns-to-keys dependencies hold on every
  set of rows; the others are properties of datasets.\<close>

type_synonym ('r, 'k) view = "'r semi_factor \<times> 'k semi_factor"

text \<open>A keying computes keys from rows and declares the column support of each key part.\<close>

record ('r, 'k) keying =
  key_fun :: "'r \<rightarrow> 'k"
  key_supp :: "'k semi_factor \<Rightarrow> 'r semi_factor"

hide_const (open) keying.truncate

locale keyed =
  fixes keying :: "('r, 'k) keying"
  assumes csupp_reads: "proj a\<cdot>(key_fun keying\<cdot>(x \<downharpoonright> key_supp keying a)) = proj a\<cdot>(key_fun keying\<cdot>x)"
    and csupp_bot: "key_supp keying \<bottom> = \<bottom>"
    and csupp_sup: "key_supp keying (a \<squnion> b) = key_supp keying a \<squnion> key_supp keying b"
begin

abbreviation rkey :: "'r \<rightarrow> 'k" where "rkey \<equiv> key_fun keying"
abbreviation csupp :: "'k semi_factor \<Rightarrow> 'r semi_factor" where "csupp \<equiv> key_supp keying"

abbreviation rproj :: "'k semi_factor \<Rightarrow> 'r \<Rightarrow> 'k" where
  "rproj a x \<equiv> proj a\<cdot>(rkey\<cdot>x)"

definition vpart :: "('r, 'k) view \<Rightarrow> 'r \<Rightarrow> 'r \<times> 'k" where
  "vpart v x = (x \<downharpoonright> fst v, rproj (snd v) x)"

lemma vpart_pair [simp]: "vpart (c, a) x = (x \<downharpoonright> c, rproj a x)"
  by (simp add: vpart_def)

text \<open>A key part is read off any section covering its support.\<close>

lemma rproj_section: "csupp a \<sqsubseteq> c \<Longrightarrow> rproj a (y \<downharpoonright> c) = rproj a y"
  by (metis csupp_reads proj_le)

lemma csupp_mono: "a \<sqsubseteq> b \<Longrightarrow> csupp a \<sqsubseteq> csupp b"
  by (metis csupp_sup join_absorb lattice_join_ge1)

subsection \<open>Dependencies on a set of rows\<close>

text \<open>A view determines a function on a set of rows when rows agreeing on the view agree on the
  function.  A dependency between views is the case where the function is the other view.\<close>

definition determines :: "'r set \<Rightarrow> ('r, 'k) view \<Rightarrow> ('r \<Rightarrow> 'b::type) \<Rightarrow> bool" where
  "determines P v g \<longleftrightarrow> (\<forall>x\<in>P. \<forall>y\<in>P. vpart v x = vpart v y \<longrightarrow> g x = g y)"

abbreviation vfd :: "'r set \<Rightarrow> ('r, 'k) view \<Rightarrow> ('r, 'k) view \<Rightarrow> bool" where
  "vfd P v w \<equiv> determines P v (vpart w)"

lemma determinesD: "determines P v g \<Longrightarrow> x \<in> P \<Longrightarrow> y \<in> P \<Longrightarrow> vpart v x = vpart v y \<Longrightarrow> g x = g y"
  unfolding determines_def by blast

lemma determines_subset: "determines P v g \<Longrightarrow> Q \<subseteq> P \<Longrightarrow> determines Q v g"
  unfolding determines_def by blast

lemma determines_trans: "vfd P u v \<Longrightarrow> determines P v g \<Longrightarrow> determines P u g"
  unfolding determines_def by blast

lemma determines_key: "determines P (c, a) (h \<circ> rproj a)"
  unfolding determines_def by simp

lemma determines_pair:
  assumes f: "determines P v f" and g: "determines P v g"
  shows "determines P v (\<lambda>x. h (f x) (g x))"
  unfolding determines_def
  using determinesD[OF f] determinesD[OF g] by metis

definition vle :: "('r, 'k) view \<Rightarrow> ('r, 'k) view \<Rightarrow> bool" where
  "vle v w \<longleftrightarrow> fst v \<sqsubseteq> fst w \<and> snd v \<sqsubseteq> snd w"

definition vsup :: "('r, 'k) view \<Rightarrow> ('r, 'k) view \<Rightarrow> ('r, 'k) view" where
  "vsup v w = (fst v \<squnion> fst w, snd v \<squnion> snd w)"

lemma vpart_le:
  assumes le: "vle v w" and eq: "vpart w x = vpart w y"
  shows "vpart v x = vpart v y"
proof -
  have c: "x \<downharpoonright> fst w = y \<downharpoonright> fst w" and k: "rproj (snd w) x = rproj (snd w) y"
    using eq by (simp_all add: vpart_def)
  have "x \<downharpoonright> fst v = y \<downharpoonright> fst v"
    using arg_cong[OF c, of "Rep_cfun (proj (fst v))"] le by (simp add: vle_def proj_le)
  moreover have "rproj (snd v) x = rproj (snd v) y"
    using arg_cong[OF k, of "Rep_cfun (proj (snd v))"] le by (simp add: vle_def proj_le)
  ultimately show ?thesis by (simp add: vpart_def)
qed

lemma vfd_refl: "vle w v \<Longrightarrow> vfd P v w"
  unfolding determines_def by (blast intro: vpart_le)

lemma vpart_vsup:
  assumes v: "vpart v x = vpart v y" and w: "vpart w x = vpart w y"
  shows "vpart (vsup v w) x = vpart (vsup v w) y"
proof -
  have "x \<downharpoonright> fst v = y \<downharpoonright> fst v" "x \<downharpoonright> fst w = y \<downharpoonright> fst w"
    "rproj (snd v) x = rproj (snd v) y" "rproj (snd w) x = rproj (snd w) y"
    using v w by (simp_all add: vpart_def)
  then show ?thesis unfolding vpart_def vsup_def fst_conv snd_conv proj_sup by simp
qed

lemma vfd_sup: "vfd P u v \<Longrightarrow> vfd P u w \<Longrightarrow> vfd P u (vsup v w)"
  unfolding determines_def by (blast intro: vpart_vsup)

text \<open>Columns-to-keys dependencies are a matter of computation.\<close>

lemma vfd_support: "csupp a \<sqsubseteq> c \<Longrightarrow> vfd P (c, \<bottom>) (\<bottom>, a)"
  unfolding determines_def
proof (intro ballI impI)
  fix x y assume le: "csupp a \<sqsubseteq> c" and eq: "vpart (c, \<bottom>) x = vpart (c, \<bottom>) y"
  have "x \<downharpoonright> csupp a = y \<downharpoonright> csupp a" using eq proj_le[OF le, of x] proj_le[OF le, of y] by simp
  then have "rproj a x = rproj a y" by (metis csupp_reads)
  then show "vpart (\<bottom>, a) x = vpart (\<bottom>, a) y" by (simp add: proj_bot)
qed

subsection \<open>Weak dependencies\<close>

text \<open>A weak dependency only holds between rows where both sides are present, as for the two
  sides of a join.  Weak dependencies do not compose with each other (the middle view may be absent
  in one row), but they compose with dependencies on either side, given that presence passes from
  the outer view to the middle one.\<close>

definition vpresent :: "('r, 'k) view \<Rightarrow> 'r \<Rightarrow> bool" where
  "vpresent v x \<longleftrightarrow> vpart v x \<noteq> \<bottom>"

definition weak_fd :: "'r set \<Rightarrow> ('r, 'k) view \<Rightarrow> ('r, 'k) view \<Rightarrow> bool" where
  "weak_fd P v w \<longleftrightarrow> (\<forall>x\<in>P. \<forall>y\<in>P. vpart v x = vpart v y \<longrightarrow> vpresent v x \<longrightarrow>
    vpresent w x \<longrightarrow> vpresent w y \<longrightarrow> vpart w x = vpart w y)"

lemma vfd_weak_fd: "vfd P v w \<Longrightarrow> weak_fd P v w"
  unfolding weak_fd_def determines_def by blast

lemma vfd_weak_fd_trans:
  "vfd P u v \<Longrightarrow> weak_fd P v w \<Longrightarrow> (\<forall>x\<in>P. vpresent u x \<longrightarrow> vpresent v x) \<Longrightarrow> weak_fd P u w"
  unfolding weak_fd_def determines_def by blast

lemma weak_fd_vfd_trans:
  "weak_fd P u v \<Longrightarrow> vfd P v w \<Longrightarrow> (\<forall>x\<in>P. vpresent w x \<longrightarrow> vpresent v x) \<Longrightarrow> weak_fd P u w"
  unfolding weak_fd_def determines_def by blast

text \<open>The chase only guarantees the guarded form: equal \<^emph>\<open>maximal\<close> determinants.  It becomes a
  dependency between views when the determinant is maximal where present and the dependent part
  is absent where the determinant is.\<close>

lemma fd_vfd:
  assumes f: "fd a b P" and m: "\<forall>x\<in>P. x \<downharpoonright> a \<noteq> \<bottom> \<longrightarrow> maximal_at a (x \<downharpoonright> a)"
    and abs: "\<forall>x\<in>P. x \<downharpoonright> a = \<bottom> \<longrightarrow> x \<downharpoonright> b = \<bottom>"
  shows "vfd P (a, \<bottom>) (b, \<bottom>)"
  unfolding determines_def
proof (intro ballI impI)
  fix x y assume x: "x \<in> P" and y: "y \<in> P" and eq: "vpart (a, \<bottom>) x = vpart (a, \<bottom>) y"
  have eq': "x \<downharpoonright> a = y \<downharpoonright> a" using eq by simp
  have "x \<downharpoonright> b = y \<downharpoonright> b"
  proof (cases "x \<downharpoonright> a = \<bottom>")
    case True
    then show ?thesis using abs x y eq' by simp
  next
    case False
    then show ?thesis using fdD[OF f x y _ eq'] m x by blast
  qed
  then show "vpart (b, \<bottom>) x = vpart (b, \<bottom>) y" by (simp add: proj_bot)
qed

end

section \<open>Dependencies over all conforming datasets\<close>

locale keyed_schema = schema rules + keyed keying
  for rules :: "'r schema_rules" and keying :: "('r, 'k) keying"
begin

definition universally :: "('r set \<Rightarrow> bool) \<Rightarrow> bool" where
  "universally Q \<longleftrightarrow> (\<forall>X. conforms X \<longrightarrow> Q (lower_maximal X))"

lemma universallyD: "universally Q \<Longrightarrow> conforms X \<Longrightarrow> Q (lower_maximal X)"
  unfolding universally_def by blast

lemma universally_mono: "universally Q \<Longrightarrow> (\<And>P. Q P \<Longrightarrow> T P) \<Longrightarrow> universally T"
  unfolding universally_def by blast

lemma universally_mono2:
  "universally Q \<Longrightarrow> universally Q' \<Longrightarrow> (\<And>P. Q P \<Longrightarrow> Q' P \<Longrightarrow> T P) \<Longrightarrow> universally T"
  unfolding universally_def by blast

text \<open>A functional dependency of the schema holds universally between views, given maximal
  determinants and absent dependents where the determinant is absent.\<close>

lemma universally_fd_rule:
  assumes r: "fd_rule a b \<in> chase_rules"
    and m: "universally (\<lambda>P. \<forall>x\<in>P. x \<downharpoonright> a \<noteq> \<bottom> \<longrightarrow> maximal_at a (x \<downharpoonright> a))"
    and abs: "universally (\<lambda>P. \<forall>x\<in>P. x \<downharpoonright> a = \<bottom> \<longrightarrow> x \<downharpoonright> b = \<bottom>)"
  shows "universally (\<lambda>P. vfd P (a, \<bottom>) (b, \<bottom>))"
  unfolding universally_def
  using fd_vfd conforms_fd[OF _ r] universallyD[OF m] universallyD[OF abs] by blast

subsection \<open>Strong keys\<close>

text \<open>A key is \<^emph>\<open>strong\<close> when it is functionally equivalent to its column support in every
  conforming dataset; one direction holds by computation.  Strong keys transfer column dependencies
  to keys: recover the columns from the key, then compute the other key from them.\<close>

definition strong_key :: "'k semi_factor \<Rightarrow> bool" where
  "strong_key a \<longleftrightarrow> universally (\<lambda>P. vfd P (\<bottom>, a) (csupp a, \<bottom>))"

lemma strong_key_equiv:
  "strong_key a \<Longrightarrow> conforms X \<Longrightarrow>
    vfd (lower_maximal X) (\<bottom>, a) (csupp a, \<bottom>) \<and> vfd (lower_maximal X) (csupp a, \<bottom>) (\<bottom>, a)"
  unfolding strong_key_def by (auto dest: universallyD intro: vfd_support)

theorem strong_key_transfer:
  assumes a: "strong_key a" and c: "universally (\<lambda>P. vfd P (csupp a, \<bottom>) (c, \<bottom>))"
    and b: "csupp b \<sqsubseteq> c"
  shows "universally (\<lambda>P. vfd P (\<bottom>, a) (\<bottom>, b))"
  using a c unfolding strong_key_def
  by (rule universally_mono2) (blast intro: determines_trans vfd_support[OF b])

subsection \<open>Supports of content functions\<close>

text \<open>A content function reads a section of the row (its column support, which is what it
  depends on across datasets) and, within every conforming dataset, is determined by a part of the key
  (its key support), as when it reads a value column whose primary key is in the key.\<close>

definition fun_support :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r \<rightarrow> 'b::cpo) \<Rightarrow> bool" where
  "fun_support c a f \<longleftrightarrow> (\<forall>x. f\<cdot>(x \<downharpoonright> c) = f\<cdot>x) \<and> universally (\<lambda>P. determines P (\<bottom>, a) (Rep_cfun f))"

text \<open>A function reading columns that the key determines is supported by that key.\<close>

lemma fun_support_columns:
  assumes reads: "\<And>x. f\<cdot>(x \<downharpoonright> c) = f\<cdot>x" and ka: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))"
  shows "fun_support c a f"
proof -
  have "determines P (c, \<bottom>) (Rep_cfun f)" for P
    unfolding determines_def by (metis reads vpart_pair prod.inject)
  then show ?thesis
    unfolding fun_support_def using reads ka by (blast intro: universally_mono determines_trans)
qed

end

end
