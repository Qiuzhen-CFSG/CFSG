module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_2_g

/-!
This module isolates `theorem_2_1_4` from `Theory.AlgebraicGroup.Automorphisms.Lang`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_4
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : Variety.IsConnected K) :
    ∀ (H : ClosedSubgroup K)
      (hInv : σ.onPoints '' (H : Set (Variety.Point K)) =
        (H : Set (Variety.Point K))),
      letI := H.carrierAlgebraicGroup
      let hInv' : ∀ x : Variety.Point H.carrierVariety,
          σ.onPoints (H.inclusion.onPoints x) ∈ H.toSubgroup := by
        intro x
        change σ.onPoints (H.inclusion.onPoints x) ∈
          (H : Set (Variety.Point K))
        rw [← hInv]
        exact ⟨H.inclusion.onPoints x, (H.pointEquiv x).property, rfl⟩
      let σH := (σ.comp H.inclusion).codRestrictClosedSubgroup H hInv'
      let H₀ := identityComponentSubgroup H.carrierVariety
      let : H₀.Normal := by
        simpa [H₀, identityComponentClosedSubgroup_carrier] using
          identityComponentClosedSubgroup_isNormal H.carrierVariety
      let hmap : H₀ ≤ Subgroup.comap σH.onPoints H₀ := by
        intro x hx
        exact σH.map_identityComponentSubgroup ⟨x, hx, rfl⟩
      let σQ : (Variety.Point H.carrierVariety ⧸ H₀) →*
          (Variety.Point H.carrierVariety ⧸ H₀) :=
        QuotientGroup.map H₀ H₀ σH.onPoints hmap
      let π : Variety.Point H.carrierVariety →*
          (Variety.Point H.carrierVariety ⧸ H₀) := QuotientGroup.mk' H₀
      ∃ e : H1 σH.onPoints ≃ H1 σQ,
        ∀ x, e (H1.mk σH.onPoints x) = H1.mk σQ (π x) := by
  sorry

/-! The displayed clauses (a)--(d) of source Theorem 2.1.5 are absent from
the authoritative Chapter 2 transcription.  No partial numbered declaration
is exported here; the action-theoretic core belongs to its dedicated task
module until the source statement is recovered. -/

end Theory.AlgebraicGroup
