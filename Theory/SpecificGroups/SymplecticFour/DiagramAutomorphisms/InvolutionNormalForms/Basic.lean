module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Construction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFacts
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Inner twists and restriction to the derived symplectic group

The characteristic-two symplectic group has trivial center. Consequently an
inner twist of an involutory automorphism has square one exactly when its
matrix satisfies the nonabelian cocycle equation. An explicit coboundary
then gives conjugacy in the actual automorphism group.

Restriction is a homomorphism on the genuine commutator subgroup; in the
binary case the exceptional graph map restricts to a map with square one.
These reductions do not assert that every cocycle is a coboundary.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Notation
16.1.3 and Lemma 16.1.4, printed pp.1170–1173 of `refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
variable {F : Type*} [Field F]

/-- Restriction to the characteristic commutator subgroup, as an actual homomorphism. -/
noncomputable def derivedRestriction : MulAut (Sp F) →* MulAut (commutator (Sp F)) where
  toFun a := restrict a _ (Subgroup.characteristic_iff_map_eq.mp inferInstance a)
  map_one' := by
    ext x
    rfl
  map_mul' a b := by
    ext x
    rfl

@[simp] theorem derivedRestriction_apply (a : MulAut (Sp F)) (x : commutator (Sp F)) :
    (derivedRestriction a x : Sp F) = a x := rfl

@[simp] theorem derivedRestriction_conj (g : Sp F) :
    derivedRestriction (MulAut.conj g) = MulAut.conjNormal g := by
  ext x
  rfl

variable [CharP F 2]

/-- Conjugation is faithful on the actual characteristic-two matrix group. -/
theorem inner_injective : Function.Injective (MulAut.conj : Sp F →* MulAut (Sp F)) := by
  apply (MulAut.conj : Sp F →* MulAut (Sp F)).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  have hc : g ∈ Subgroup.center (Sp F) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have he := congrArg (fun a : MulAut (Sp F) => a x) hg
    change g * x * g⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  simpa only [EvenProjective.center_eq_bot, Subgroup.mem_bot] using hc

/-- An inner involutory automorphism is induced by a genuine matrix involution. -/
theorem inner_involution (a : MulAut (Sp F)) (ha : orderOf a = 2)
    (hi : a ∈ MulAut.innerSubgroup (Sp F)) :
    ∃ g : Sp F, orderOf g = 2 ∧ a = MulAut.conj g := by
  obtain ⟨g, rfl⟩ := hi
  exact ⟨g, (orderOf_injective MulAut.conj inner_injective g).symm.trans ha, rfl⟩

omit [CharP F 2] in
theorem inner_twist_square (s : MulAut (Sp F)) (g : Sp F) :
    (MulAut.conj g * s) ^ 2 = MulAut.conj (g * s g) * s ^ 2 := by
  apply MulEquiv.ext
  intro x
  simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

/-- Squaring an inner twist gives the precise nonabelian cocycle equation. -/
theorem inner_twist_square_eq_one_iff (s : MulAut (Sp F)) (hs : s ^ 2 = 1)
    (g : Sp F) : (MulAut.conj g * s) ^ 2 = 1 ↔ g * s g = 1 := by
  rw [inner_twist_square, hs, mul_one, ← map_one MulAut.conj]
  exact inner_injective.eq_iff

omit [CharP F 2] in
theorem inner_twist_eq_conjugate (s : MulAut (Sp F)) (g h : Sp F)
    (hg : g = h * (s h)⁻¹) :
    MulAut.conj g * s = MulAut.conj h * s * (MulAut.conj h)⁻¹ := by
  subst g
  apply MulEquiv.ext
  intro x
  simp only [MulAut.mul_apply, MulAut.conj_apply, ← map_inv, map_mul]


omit [CharP F 2] in
theorem inner_twist_isConj (s : MulAut (Sp F)) (g h : Sp F)
    (hg : g = h * (s h)⁻¹) : IsConj s (MulAut.conj g * s) := by
  exact isConj_iff.mpr ⟨MulAut.conj h, (inner_twist_eq_conjugate s g h hg).symm⟩

variable [Finite F]

theorem binary_graph_square (hF : Nat.card F = 2) :
    ExceptionalGraph.graphAut (F := F) ^ 2 = 1 := by
  rw [ExceptionalGraph.graphAut_square, fieldAutomorphism_eq_one_of_card_two hF]

theorem binary_derivedGraph_square (hF : Nat.card F = 2) :
    (derivedRestriction (ExceptionalGraph.graphAut (F := F))) ^ 2 = 1 := by
  rw [← map_pow, binary_graph_square hF, map_one]
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
