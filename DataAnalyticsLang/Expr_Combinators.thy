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

definition ekd :: "('l, 'f, 'r, 'k, 'v) expr \<Rightarrow> ('l, 'f, 'r) frame \<Rightarrow> 'l" where
  "ekd E F = sup (emind E) (flod F)"

subsection \<open>Collect\<close>

text \<open>The components are evaluated at the frame extended by all their minds, each at its own key
  LOD; the collected minimal and natural LODs are the joins, and a key coordinate is read when
  some component reads it: the mask is the pointwise join.\<close>

definition collect :: "('l, 'f, 'r, 'k, 'a::domain) expr list \<Rightarrow> ('l, 'f, 'r, 'k, 'a stuple) expr"
  where "collect Es =
    (let M = fold sup (map emind Es) bot in
     \<lparr>emind = M, enatd = fold sup (map enatd Es) bot,
      emaskd = \<lambda>a. fold sup (map (\<lambda>E. emaskd E a) Es) bot,
      esem = \<lambda>F k. stuple_of (map (\<lambda>E. esem E (finclude M F) (proj (ekd E (finclude M F))\<cdot>k)) Es)\<rparr>)"

end

end
