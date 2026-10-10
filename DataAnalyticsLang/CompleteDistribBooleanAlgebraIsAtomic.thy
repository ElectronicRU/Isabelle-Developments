theory CompleteDistribBooleanAlgebraIsAtomic
  imports Main "Order_Lattice_Props.Order_Lattice_Props" "HOL-Library.FuncSet"
begin

lemma (in complete_distrib_lattice) INF_SUP_distrib:
  fixes I :: "'i set" and p :: "'j \<Rightarrow> 'i" and f :: "'j \<Rightarrow> 'a"
  shows
"(INF i \<in> I. SUP j \<in> p -` {i}. f j) = (SUP q \<in> (\<Pi> i\<in>I. p -` {i}). INF i \<in> I. f(q i))"
  




subclass (in complete_boolean_algebra) complete_atomic_boolean_algebra
proof
  fix x :: 'a assume "x \<noteq> \<bottom>"



end