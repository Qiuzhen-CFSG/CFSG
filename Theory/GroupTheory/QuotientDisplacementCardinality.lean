module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group

namespace Subgroup

open scoped commutatorElement

universe u

private def ambientProjection {G : Type u} [Group G]
    (D X : Subgroup G) [D.Normal] : X ⧸ D.subgroupOf X →* G ⧸ D :=
  QuotientGroup.map _ _ X.subtype le_rfl

private theorem ambientProjection_injective {G : Type u} [Group G]
    (D X : Subgroup G) [D.Normal] : Function.Injective (ambientProjection D X) := by
  intro first second
  induction first using QuotientGroup.induction_on with | H first =>
  induction second using QuotientGroup.induction_on with | H second =>
  intro heq
  change (QuotientGroup.mk (first : G) : G ⧸ D) = QuotientGroup.mk (second : G) at heq
  apply QuotientGroup.eq.mpr
  change (first : G)⁻¹ * (second : G) ∈ D
  exact QuotientGroup.eq.mp heq

/-- Commutator displacement embeds `X / D` into `(B ⊔ D) / D` when the
intersection of `P` with its actor conjugate lies in `D`. The auxiliary
containments involving `Y` and `D ≤ B` are retained for the intended application;
the displacement proof only needs its values in `B ⊔ D`. -/
public theorem quotient_card_le_of_conjugate_intersection
    {G : Type u} [Group G] [Finite G]
    (D X B Y P Q R : Subgroup G) [D.Normal]
    (hDX : D ≤ X) (_hDB : D ≤ B) (hXP : X ≤ P) (hXQ : X ≤ Q)
    (_hBY : B ≤ Y) (_hDY : D ≤ Y) (hbound : ⁅Q, R⁆ ≤ B)
    (actor : G) (hactor : actor ∈ R)
    (hintersection : P ⊓ P.map (MulAut.conj actor).toMonoidHom ≤ D) :
    Nat.card (X ⧸ D.subgroupOf X) ≤
      Nat.card ((B ⊔ D : Subgroup G) ⧸ D.subgroupOf (B ⊔ D)) := by
  let projection := QuotientGroup.mk' D
  let representative : X → (B ⊔ D : Subgroup G) := fun element =>
    ⟨⁅(element : G), actor⁆,
      (le_sup_left : B ≤ B ⊔ D)
        (hbound (commutator_mem_commutator (hXQ element.property) hactor))⟩
  have hwellDefined (first second : X)
      (heq : (QuotientGroup.mk first : X ⧸ D.subgroupOf X) =
        QuotientGroup.mk second) :
      (QuotientGroup.mk (representative first) :
        (B ⊔ D : Subgroup G) ⧸ D.subgroupOf (B ⊔ D)) =
        QuotientGroup.mk (representative second) := by
    apply ambientProjection_injective D (B ⊔ D)
    have hambient : projection (first : G) = projection (second : G) :=
      congrArg (ambientProjection D X) heq
    change projection ⁅(first : G), actor⁆ = projection ⁅(second : G), actor⁆
    simp only [commutatorElement_def, map_mul, map_inv, hambient]
  let displacement : X ⧸ D.subgroupOf X →
      (B ⊔ D : Subgroup G) ⧸ D.subgroupOf (B ⊔ D) :=
    Quotient.lift (fun element => QuotientGroup.mk (representative element))
      (fun first second hrel => hwellDefined first second (Quotient.sound hrel))
  apply Nat.card_le_card_of_injective displacement
  intro first second
  induction first using QuotientGroup.induction_on with | H first =>
  induction second using QuotientGroup.induction_on with | H second =>
  intro heq
  have hcomm : projection ⁅(first : G), actor⁆ = projection ⁅(second : G), actor⁆ :=
    congrArg (ambientProjection D (B ⊔ D)) heq
  let difference : G := (second : G)⁻¹ * first
  have hmem : difference ∈ P :=
    P.mul_mem (P.inv_mem (hXP second.property)) (hXP first.property)
  have hfix : projection ((MulAut.conj actor) difference) = projection difference := by
    change projection (actor * ((second : G)⁻¹ * first) * actor⁻¹) = _
    calc
      projection (actor * ((second : G)⁻¹ * first) * actor⁻¹) =
          projection ((second : G)⁻¹ * ⁅(second : G), actor⁆ *
            ⁅(first : G), actor⁆⁻¹ * first) := by
        congr 1
        simp only [commutatorElement_def]
        group
      _ = projection difference := by
        simp only [map_mul, map_inv, hcomm, difference]
        group
  have herror : difference⁻¹ * (MulAut.conj actor) difference ∈ D :=
    QuotientGroup.eq.mp hfix.symm
  have hconjP : (MulAut.conj actor) difference ∈ P := by
    have hproduct := P.mul_mem hmem (hXP (hDX herror))
    simpa only [mul_inv_cancel_left] using hproduct
  have hconjD : (MulAut.conj actor) difference ∈ D :=
    hintersection ⟨hconjP, mem_map.mpr ⟨difference, hmem, rfl⟩⟩
  have hdifference : difference ∈ D := by
    apply (QuotientGroup.eq_one_iff difference).mp
    exact hfix.symm.trans ((QuotientGroup.eq_one_iff _).mpr hconjD)
  symm
  apply QuotientGroup.eq.mpr
  exact hdifference

end Subgroup
