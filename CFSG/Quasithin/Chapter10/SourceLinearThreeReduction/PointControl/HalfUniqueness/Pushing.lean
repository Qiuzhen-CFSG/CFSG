module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Normalizer

/-!
# The literal pushing-up setup for the containing-component argument

Every SQTK group containing L₀T₁ contains the original R=O₂(L₀T).
Source A.4.2(7) and characteristic-normalizer control therefore construct
C.2.3 on that R. In a containing pair, this applies to the actual group
H₀=K₁L₂T₁ used in the constrained branch of 10.2.6. No normality in the
ambient simple group is inferred from normality inside H.

This constructs C.2.3, not the subsequent C.2.7 classification or
the embedding contradiction.
Source: Aschbacher--Smith, 10.2.6, printed pp.748--749.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original R supplies every field of C.2.3 for a half-join overgroup. -/
theorem pushingSetup_of_halfJoin_le {X : Subgroup G}
    (hsq : IsSQTK KnownSimple.IsKnownSimple X) (hX : halfJoin T L ≤ X) :
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple X
      ((localJoin T L).pCoreIn 2) (X ⊓ D.maximalLocal) :=
  source_join_core_pushing_setup D hsq (le_sup_left.trans hX)
    ((join_core_le_stabilizer D).trans (le_sup_right.trans hX))

variable {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- The first literal H₀=K₁L₂T₁ in source 10.2.6 has the required C.2.3
setup, independently of whether K₁ is the strictly larger component. -/
theorem ContainingPair.first_pushingSetup (C : ContainingPair D H t K₁ K₂) :
    let X := (K₁.map H.subtype ⊔ L.map (MulAut.conj t).toMonoidHom) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G))
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple X
      ((localJoin T L).pCoreIn 2) (X ⊓ D.maximalLocal) := by
  let B := L.map (MulAut.conj t).toMonoidHom
  let X := (K₁.map H.subtype ⊔ B) ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
  have hLH : L ≤ H := (le_componentOrbit L T).trans (le_sup_left.trans C.half_le)
  have hBH : B ≤ H := (le_sup_right.trans C.orbit_eq.ge).trans (le_sup_left.trans C.half_le)
  have hLX : L ≤ K₁.map H.subtype := by
    have hh := map_mono (f := H.subtype) C.first_le
    rwa [map_subgroupOf_eq_of_le hLH] at hh
  have hXH : X ≤ H := sup_le (sup_le (map_subtype_le K₁) hBH)
    (le_sup_right.trans C.half_le)
  have hsq := D.simpleQTKE.twoLocal_sqtk C.maximal.1
  apply pushingSetup_of_halfJoin_le D
    ⟨hsq.stronglyQuasithin.of_injective (inclusion hXH) (inclusion_injective hXH),
      hsq.isKGroup.of_injective (inclusion hXH) (inclusion_injective hXH)⟩
  apply sup_le ?_ le_sup_right
  rw [C.orbit_eq]
  exact sup_le (hLX.trans (le_sup_left.trans le_sup_left)) (le_sup_right.trans le_sup_left)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
