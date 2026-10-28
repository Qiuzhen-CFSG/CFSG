module

public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Commutator generation for an elementary abelian conjugation module

If a representation agrees with ambient conjugation on an elementary abelian
subgroup `N`, then `[N,G] = N` makes the representation commutator-generated.
The span of the linear displacements, interpreted as an ambient subgroup,
contains each group commutator. The acting group may be a quotient of `G`.

This supplies the passage from group commutators to module covers used in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), C.1.13(c), printed p.125, and I.1.5, printed p.408.
-/

public section

open scoped IsMulCommutative commutatorElement

namespace Representation

/-- Literal conjugation and `[N,G] = N` imply generation by linear displacements. -/
theorem coinvariants_ker_eq_top_of_commutator_eq {p : ℕ} [Fact p.Prime]
    {G A : Type*} [Group G] [Group A] (N : Subgroup G)
    [IsElementaryAbelian p N]
    (σ : Representation (ZMod p) A (Additive N)) (a : G →* A)
    (ha : ∀ g w, ((σ (a g) w).toMul : G) = g * (w.toMul : G) * g⁻¹)
    (hc : ⁅N, (⊤ : Subgroup G)⁆ = N) : Coinvariants.ker σ = ⊤ := by
  let C : Subgroup N := (Coinvariants.ker σ).toAddSubgroup.toSubgroup'
  have hNC : N ≤ C.map N.subtype := by
    conv_lhs => rw [← hc, Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro g _ n hn
    let w : Additive N := Additive.ofMul ⟨n, hn⟩
    refine ⟨(σ (a g) w - w).toMul, Coinvariants.sub_mem_ker _ _, ?_⟩
    change ((σ (a g) w).toMul : G) / n = ⁅g, n⁆
    rw [ha, div_eq_mul_inv]
    rfl
  apply top_unique
  intro w _
  obtain ⟨n, hn, he⟩ := hNC w.toMul.property
  have hnw : n = w.toMul := Subtype.ext he
  subst n
  exact hn

end Representation
