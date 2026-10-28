module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Point stabilizers from generator reductions

A left Schreier reduction table expresses every generator/representative
product as a representative times an element of a proposed next subgroup.
Induction on the generated subgroup gives such a decomposition for every
word. If the next subgroup fixes the base point and only the identity
representative returns that point, an element fixing it lies in the next
subgroup. Neither a group order nor distinctness of all representatives is
needed.

This is the stabilizer form of Schreier rewriting, for concrete permutation
certificates such as the Fi₂₃ lift in the ATLAS Fi₂₄′ action.
-/

public section

namespace Subgroup

variable {G X A I : Type*} [Group G] [MulAction G X]

/-- Local Schreier transitions, with the orientation of a left group action. -/
structure GeneratorStabilizerReduction (gen : A → G) (next : Subgroup G) (base : X)
    (I : Type*) where
  representative : I → G
  initial : I
  initial_eq : representative initial = 1
  step : ∀ a i, ∃ j, ∃ k : next, gen a * representative i = representative j * k.val
  inv_step : ∀ a i, ∃ j, ∃ k : next,
    (gen a)⁻¹ * representative i = representative j * k.val
  next_fixes : ∀ k : next, k.val • base = base
  returns_base : ∀ i, representative i • base = base → representative i = 1

/-- Bijective transition maps let a certificate check only positive generator
steps: the inverse steps follow by solving the same group equalities. -/
def GeneratorStabilizerReduction.ofPermutations (gen : A → G) (next : Subgroup G)
    (base : X) (representative : I → G) (initial : I)
    (initial_eq : representative initial = 1)
    (transition : A → Equiv.Perm I) (factor : A → I → next)
    (step : ∀ a i, gen a * representative i =
      representative (transition a i) * (factor a i).val)
    (next_fixes : ∀ k : next, k.val • base = base)
    (returns_base : ∀ i, representative i • base = base → representative i = 1) :
    GeneratorStabilizerReduction gen next base I where
  representative := representative
  initial := initial
  initial_eq := initial_eq
  step a i := ⟨transition a i, factor a i, step a i⟩
  inv_step a j := by
    let i := (transition a).symm j
    refine ⟨i, (factor a i)⁻¹, ?_⟩
    have he := congrArg (fun x : G => (gen a)⁻¹ * x * (factor a i).val⁻¹) (step a i)
    simpa [i, mul_assoc] using he.symm
  next_fixes := next_fixes
  returns_base := returns_base

/-- The transition equalities produce a decomposition for every generated element. -/
theorem GeneratorStabilizerReduction.decompose {gen : A → G} {next : Subgroup G}
    {base : X} (C : GeneratorStabilizerReduction gen next base I)
    {g : G} (hg : g ∈ closure (Set.range gen)) :
    ∃ i, ∃ k : next, g = C.representative i * k.val := by
  induction hg using closure_induction_left with
  | one => exact ⟨C.initial, 1, by simp [C.initial_eq]⟩
  | mul_left a ha g _ ih =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨i, k, rfl⟩ := ih
    obtain ⟨j, k', he⟩ := C.step a i
    refine ⟨j, k' * k, ?_⟩
    change gen a * (C.representative i * k.val) =
      C.representative j * (k'.val * k.val)
    rw [← mul_assoc, he, mul_assoc]
  | inv_mul_cancel a ha g _ ih =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨i, k, rfl⟩ := ih
    obtain ⟨j, k', he⟩ := C.inv_step a i
    refine ⟨j, k' * k, ?_⟩
    change (gen a)⁻¹ * (C.representative i * k.val) =
      C.representative j * (k'.val * k.val)
    rw [← mul_assoc, he, mul_assoc]

/-- A checked Schreier table bounds the actual point stabilizer. -/
theorem GeneratorStabilizerReduction.mem_next {gen : A → G} {next : Subgroup G}
    {base : X} (C : GeneratorStabilizerReduction gen next base I)
    {g : G} (hg : g ∈ closure (Set.range gen)) (hfix : g • base = base) :
    g ∈ next := by
  obtain ⟨i, k, rfl⟩ := C.decompose hg
  have hi : C.representative i • base = base := by
    simpa only [mul_smul, C.next_fixes] using hfix
  rw [C.returns_base i hi, one_mul]
  exact k.property

/-- Successive certified generator reductions can be composed without counting
any group or orbit. The final subgroup can be certified separately. -/
theorem mem_of_generatorStabilizerReductions {n : Nat}
    (groups : Fin (n + 1) → Subgroup G) (points : Fin n → X)
    (generators : (i : Fin n) → A → G)
    (generated : ∀ i, closure (Set.range (generators i)) = groups i.castSucc)
    (indices : Fin n → Type*)
    (certificates : ∀ i,
      GeneratorStabilizerReduction (generators i) (groups i.succ) (points i) (indices i))
    {g : G} (hg : g ∈ groups 0) (hfix : ∀ i, g • points i = points i) :
    g ∈ groups (Fin.last n) := by
  have hmem : ∀ i : Fin (n + 1), g ∈ groups i := by
    intro i
    induction i using Fin.induction with
    | zero => exact hg
    | succ i ih =>
      apply (certificates i).mem_next
      · rwa [generated i]
      · exact hfix i
  exact hmem _

end Subgroup
