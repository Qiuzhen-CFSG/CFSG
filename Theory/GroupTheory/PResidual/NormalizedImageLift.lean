module
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# A normalized residual lift inside a prescribed subgroup

Intersect a normal subgroup K with the preimage of a two-perfect image P,
then take the embedded two-residual. Surjections preserve residuals, so the
result still maps onto P and lies inside K. The preimage of any group
normalizing P normalizes the intersection and its characteristic residual.

Source application: the actual K_B lift in Aschbacher--Smith 13.1.9,
printed pp.870--871. Normality of K is relative to the stated ambient group.
-/

public noncomputable section
open Subgroup

namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

/-- Lift a two-perfect subgroup within a prescribed normal subgroup, preserving
its exact image and the full relative normalizer preimage. -/
theorem exists_pPerfect_lift_within_normal
    (q : G →* Q) (K : Subgroup G) [K.Normal] (P E : Subgroup Q)
    (hPK : P ≤ K.map q) (hEP : E ≤ normalizer (P : Set Q)) (hp : IsPPerfect 2 P) :
    ∃ B : Subgroup G, B ≤ K ∧ IsPPerfect 2 B ∧ B.map q = P ∧
      E.comap q ≤ normalizer (B : Set G) := by
  let X := K ⊓ P.comap q
  let B := (pResidual 2 X).map X.subtype
  have hX : X.map q = P := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x,hx,hxy⟩ := hPK hy
      exact ⟨x,⟨hx,by change q x ∈ P; rwa [hxy]⟩,hxy⟩
  have hXN : E.comap q ≤ normalizer (X : Set G) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro u
    have hKx := mem_normalizer_iff.mp (show x ∈ normalizer (K : Set G) from
      le_normalizer_of_normal (mem_top x)) u
    have hPx := mem_normalizer_iff.mp (hEP hx) (q u)
    change (u ∈ K ∧ q u ∈ P) ↔ x * u * x⁻¹ ∈ K ∧ q (x * u * x⁻¹) ∈ P
    rw [map_mul,map_mul,map_inv]
    exact and_congr hKx hPx
  refine ⟨B,(map_subtype_le _).trans inf_le_left,?_,?_,?_⟩
  · exact (isPPerfect_pResidual 2).of_surjective (X.subtype.subgroupMap (pResidual 2 X))
      (X.subtype.subgroupMap_surjective _)
  · change ((pResidual 2 X).map X.subtype).map q = P
    rw [map_embedded_pResidual,hX,(pResidual_eq_top_iff 2 P).mpr hp,
      ←MonoidHom.range_eq_map,range_subtype]
  · exact hXN.trans (normalizer_le_normalizer_characteristic_image X (pResidual 2 X))
end Subgroup
