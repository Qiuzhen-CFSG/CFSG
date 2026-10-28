module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Grouping coefficient words by their finite root index

Filtering a word by each index in order gives a permutation of the original
word. Each block belongs to its one-root subalgebra. If that subalgebra is
spanned by the truncated coefficients, their ordered block product is exactly
the span of coefficient tuples. No commutativity between roots is assumed.

This is the finite normal-form step of the source PBW argument.
-/

open scoped Pointwise
namespace CoefficientPBW
@[expose] public noncomputable section
variable {k A I : Type*} [Field k] [Ring A] [Algebra k A]
def blockWord {m:ℕ} (key:I→Fin m) (w:List I) : List I :=
  (List.ofFn fun i:Fin m=>w.filter (fun a=>decide (key a=i))).flatten
lemma blockWord_perm {m:ℕ} (key:I→Fin m) (w:List I) : (blockWord key w).Perm w := by
  classical
  apply List.perm_iff_count.mpr
  intro a
  simp only [blockWord,List.count_flatten,List.map_ofFn,List.sum_ofFn]
  have hcount (i:Fin m) : List.count a (w.filter fun x=>decide (key x=i)) =
      if key a=i then List.count a w else 0 := by
    by_cases h:key a=i
    · rw [if_pos h]
      exact List.count_filter (by simp [h])
    · rw [if_neg h]
      apply List.count_eq_zero.mpr
      intro ha
      exact h (of_decide_eq_true (List.mem_filter.mp ha).2)
  change (∑ i:Fin m, List.count a (w.filter fun x=>decide (key x=i))) = List.count a w
  simp_rw [hcount]
  simp

def algebraBlockProduct {m:ℕ} (B:Fin m→Subalgebra k A) : Submodule k A :=
  (List.ofFn fun i=> (B i).toSubmodule).prod
lemma blockWord_value_mem {m:ℕ} (X:I→A) (key:I→Fin m) (B:Fin m→Subalgebra k A)
    (hX:∀a,X a∈B (key a)) (w:List I) :
    ((blockWord key w).map X).prod∈algebraBlockProduct B := by
  classical
  have hb (i:Fin m) : ((w.filter fun a=>decide (key a=i)).map X).prod∈B i := by
    apply (B i).list_prod_mem
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    have hi := of_decide_eq_true (List.mem_filter.mp ha).2
    simpa only [←hi] using hX a
  have hp : ∀(l:List (Fin m)), (l.map fun i=>((w.filter fun a=>decide (key a=i)).map X).prod).prod∈
      (l.map fun i=>(B i).toSubmodule).prod := by
    intro l
    induction l with
    | nil => simp only [List.map_nil,List.prod_nil]; exact Submodule.one_le.mp le_rfl
    | cons i l ih =>
      simp only [List.map_cons,List.prod_cons]
      exact Submodule.mul_mem_mul (hb i) ih
  simpa only [blockWord,algebraBlockProduct,List.map_flatten,List.prod_flatten,
    List.map_map,List.map_ofFn,List.ofFn_eq_map,Function.comp_def] using hp (List.finRange m)
def orderedSpan {m q:ℕ} (C:Fin m→Fin q→A) : Submodule k A :=
  Submodule.span k (Set.range fun a:Fin m→Fin q=>(List.ofFn fun i=>C i (a i)).prod)
lemma algebraBlockProduct_eq_span {q:ℕ} : ∀(m:ℕ) (B:Fin m→Subalgebra k A) (C:Fin m→Fin q→A),
    (∀i,(B i).toSubmodule=Submodule.span k (Set.range (C i))) →
    algebraBlockProduct B=orderedSpan C := by
  intro m
  induction m with
  | zero =>
    intro B C hB
    simp [algebraBlockProduct,orderedSpan,Submodule.one_eq_span]
  | succ m ih =>
    intro B C hB
    have he : algebraBlockProduct B=(B 0).toSubmodule*algebraBlockProduct (fun i=>B i.succ) := by
      simp only [algebraBlockProduct,List.ofFn_succ,List.prod_cons]
    rw [he,hB 0,ih (fun i=>B i.succ) (fun i=>C i.succ) (fun i=>hB i.succ)]
    apply le_antisymm
    · apply Submodule.mul_le.mpr
      intro x hx y hy
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j,rfl⟩ := hx
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨a,rfl⟩ := hy
          apply Submodule.subset_span
          refine ⟨Fin.cons j a, ?_⟩
          simp only [List.ofFn_succ,List.prod_cons,Fin.cons_zero,Fin.cons_succ]
        | zero => simpa only [mul_zero] using (orderedSpan C).zero_mem
        | add a b _ _ ha hb => simpa only [mul_add] using (orderedSpan C).add_mem ha hb
        | smul c a _ ha => simpa only [mul_smul_comm] using (orderedSpan C).smul_mem c ha
      | zero => simpa only [zero_mul] using (orderedSpan C).zero_mem
      | add a b _ _ ha hb => simpa only [add_mul] using (orderedSpan C).add_mem ha hb
      | smul c a _ ha => simpa only [smul_mul_assoc] using (orderedSpan C).smul_mem c ha
    · apply Submodule.span_le.mpr
      rintro x ⟨a,rfl⟩
      simp only [List.ofFn_succ,List.prod_cons]
      exact Submodule.mul_mem_mul (Submodule.subset_span (Set.mem_range_self (a 0)))
        (Submodule.subset_span (Set.mem_range_self (fun i:Fin m=>a i.succ)))

end
end CoefficientPBW
