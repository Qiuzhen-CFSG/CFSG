module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.ModelWitnesses

/-!+# Coordinates required for the Sylow normalizer construction

These are OUTPUT data for the natural orthogonal action calculation. Both
quotient maps factor the given matrix action through injective model maps.
The distinguished half-turn inverts Y modulo the action kernel, and the
other reflection fixes the first plane. No normalizer or splitting appears
in these data. The Frattini argument upgrades the quotient coordinates to
actual normalizer isomorphisms and an actual section.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136,
combined manuscript (1 March 2004).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer

/-- The base four-group in D₈ with the graph reflection distinguished. -/
@[expose] def baseFour : Subgroup (DihedralGroup 4) where
  carrier x := x = 1 ∨ x = .sr 0 ∨ x = .r 2 ∨ x = .sr 2
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    change x * y = 1 ∨ x * y = .sr 0 ∨ x * y = .r 2 ∨ x * y = .sr 2
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    intro x hx
    change x⁻¹ = 1 ∨ x⁻¹ = .sr 0 ∨ x⁻¹ = .r 2 ∨ x⁻¹ = .sr 2
    rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem baseFour_eq :
    baseFour = zpowers (.sr 0) ⊔ zpowers (.r 2) := by
  apply le_antisymm
  · intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · have h : (DihedralGroup.sr (0 : ZMod 4)) * .r 2 = .sr 2 := rfl
      rw [← h]
      exact mul_mem_sup (mem_zpowers _) (mem_zpowers _)
  · apply sup_le <;> apply zpowers_le.mpr
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))

variable {G : Type*} [Group G]

/-- Compatible quotient coordinates for the genuine rank-four action.
This is an output contract, not a substitute for deriving the coordinates
from the natural action and the preceding local-cover conclusions. -/
structure NaturalCoordinates (T : Sylow 2 G) (M Y S R V V₁ : Subgroup G)
    (a : NaturalOrthogonalAction M V) (hTM : (T : Subgroup G) ≤ M)
    (hYSM : Y ⊔ S ≤ M) where
  tProjection : T →* DihedralGroup 4
  tOnto : Function.Surjective tProjection
  tKernel : tProjection.ker = R.subgroupOf (T : Subgroup G)
  tEmbedding : DihedralGroup 4 →* OrthogonalActor
  tInjective : Function.Injective tEmbedding
  tCompatible : ∀ t : T,
    a.actor (inclusion hTM t) = tEmbedding (tProjection t)
  ysProjection : (Y ⊔ S : Subgroup G) →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  ysOnto : Function.Surjective ysProjection
  ysKernel : ysProjection.ker = R.subgroupOf (Y ⊔ S)
  ysEmbedding : (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) →* OrthogonalActor
  ysInjective : Function.Injective ysEmbedding
  ysCompatible : ∀ y : (Y ⊔ S : Subgroup G),
    a.actor (inclusion hYSM y) = ysEmbedding (ysProjection y)
  s_preimage : ∀ t : T, (t : G) ∈ S ↔ tProjection t ∈ baseFour
  inverts_modulo : ∀ t : T, tProjection t = .r 2 →
    ∀ y ∈ Y, (t : G) * y * (t : G)⁻¹ * y ∈ R
  fixes_plane : ∀ t : T, tProjection t = .sr 2 →
    (t : G) ∈ centralizer (V₁ : Set G)
  fixed_vectors : V ⊓ centralizer (Y : Set G) = ⊥

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer
