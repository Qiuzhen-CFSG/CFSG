module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.Constructions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.Notation
public import Theory.SpecificGroups.PSL3.CartanActions.BorelResidual
public import Theory.GroupTheory.SylowKernelCore

/-!
# The genuine source residuals and Borel image in SL₃(4)

Two-perfectness of L₀ and L₁,+ follows from their definitions in 13.2.1.
The image of B = O²(B₀) is the full Borel, since the SL₃(4) Borel itself
is two-perfect. Its two-core is the marked Sylow image, and its quotient
is the full two-parameter torus. Neither B nor B* is replaced by that torus.
Self-normalization identifies L₁* with this Borel once containment and
normalization have been established from the standing configuration.

The model-center comparison is transported into the literal subgroup of
H/O₂(H), supplying the equality required by the existing normalizer lift.
Source marking and the automorphism alternatives remain separate obligations.

Source: Aschbacher–Smith, Notation 13.2.1, printed p.877, and the proof
of 13.8.20, printed pp.954–955 (PDF pp.971–972), combined manuscript
of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
open Matrix.PSL3.CartanActions.BorelQuotient
open HigherFieldReduction
open LinearThree.Geometry.CoveredProduct
variable {G : Type*} [Group G]

/-- Two-perfectness comes from the actual source definition of L₀. -/
theorem zero_isPPerfect [Finite G] (L : Subgroup G) : IsPPerfect 2 (ResidualPlacement.zero L) :=
  isPPerfect_embedded_pResidual 2 (ResidualPlacement.centralPreimage L)

/-- The other marked factor is also an embedded two-residual. -/
theorem plus_isPPerfect [Finite G] (L T V₁ : Subgroup G) :
    IsPPerfect 2 (ResidualPlacement.plus L T V₁) :=
  isPPerfect_embedded_pResidual 2 ⁅ResidualPlacement.one L T V₁, T ⊓ L⁆

/-- The actual preimage of D* in the specified special linear model. -/
def modelImage (H K D : Subgroup G) (eK : Source.starImage H K ≃* SL) : Subgroup SL :=
  (Source.starImage H D).comap (sourceActor H K eK)

/-- The scalar center maps to the center of the actual component K*. -/
theorem sourceActor_center (H K : Subgroup G) (eK : Source.starImage H K ≃* SL) :
    (center SL).map (sourceActor H K eK) =
      (center (Source.starImage H K)).map (Source.starImage H K).subtype := by
  apply le_antisymm
  · rintro x ⟨g, hg, rfl⟩
    exact ⟨eK.symm g, (centerCongr eK.symm ⟨g, hg⟩).property, rfl⟩
  · rintro x ⟨g, hg, rfl⟩
    refine ⟨eK g, (centerCongr eK ⟨g, hg⟩).property, ?_⟩
    exact congrArg Subtype.val (eK.symm_apply_apply g)

/-- A model-center comparison gives the literal central image needed by the normalizer lift. -/
theorem starImage_eq_center_of_modelImage (H K D : Subgroup G)
    (eK : Source.starImage H K ≃* SL)
    (hDK : Source.starImage H D ≤ Source.starImage H K)
    (hz : modelImage H K D eK = center SL) :
    Source.starImage H D =
      (center (Source.starImage H K)).map (Source.starImage H K).subtype := by
  have h := congrArg (Subgroup.map (sourceActor H K eK)) hz
  rw [modelImage, map_comap_eq_self (by rwa [sourceActor_range]), sourceActor_center] at h
  exact h

/-- The actual Borel image in H*, marked by its Sylow in the SL₃ model. -/
def modelBorel (H K : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (S : Sylow 2 SL) : Subgroup (Source.Hstar H) :=
  (normalizer (S : Set SL)).map (sourceActor H K eK)

theorem modelBorel_le (H K : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (S : Sylow 2 SL) : modelBorel H K eK S ≤ Source.starImage H K := by
  rw [← sourceActor_range H K eK]
  exact map_le_range (sourceActor H K eK) _

def modelBorelEquiv (H K : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (S : Sylow 2 SL) : normalizer (S : Set SL) ≃* modelBorel H K eK S :=
  equivMapOfInjective _ _ (sourceActor_injective H K eK)

theorem sl3Field_card : Nat.card F = 2 ^ 2 := by
  rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
  decide

/-- The full normalizer, not its torus, is two-perfect. -/
theorem modelBorel_isPPerfect (H K : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (S : Sylow 2 SL) : IsPPerfect 2 (modelBorel H K eK S) := by
  have hp := (pResidual_eq_top_iff 2 _).mp
    (sylowSLNormalizer_twoResidual F (by decide : 0 < 2) sl3Field_card (by rw [sl3Field_card]; decide) S)
  exact hp.of_surjective (modelBorelEquiv H K eK S).toMonoidHom
    (modelBorelEquiv H K eK S).surjective

/-- The Borel quotient is the full two-dimensional torus, with its core retained. -/
def modelBorelQuotientEquiv (H K : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (S : Sylow 2 SL) :
    modelBorel H K eK S ⧸ pCore 2 (modelBorel H K eK S) ≃* (Fˣ × Fˣ) :=
  (QuotientGroup.congr _ _ (modelBorelEquiv H K eK S).symm
    (pCore_map_iso 2 (modelBorelEquiv H K eK S).symm)).trans
    (sylowSLNormalizerQuotientEquiv F (by decide : 0 < 2) sl3Field_card S)

/-- The retained two-core is exactly the image of the specified Sylow. -/
theorem modelBorel_twoCore (H K : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (S : Sylow 2 SL) :
    (modelBorel H K eK S).pCoreIn 2 = (S : Subgroup SL).map (sourceActor H K eK) := by
  have hs : (normalizer (S : Set SL)).pCoreIn 2 = S := by
    apply S.is_maximal' (isPGroup_pCoreIn 2 _)
    exact le_pCoreIn_of_normalizes S.isPGroup' (S : Subgroup SL).le_normalizer le_rfl
  rw [modelBorel, ← map_pCoreIn_of_injective 2 _ _ (sourceActor_injective H K eK), hs]

/-- Passing from B₀ to O²(B₀) preserves this entire Borel star image. -/
theorem starImage_borelResidual_eq_modelBorel [Finite G]
    (H K B₀ : Subgroup G) (eK : Source.starImage H K ≃* SL) (S : Sylow 2 SL)
    (hBH : B₀ ≤ H) (hB : Source.starImage H B₀ = modelBorel H K eK S) :
    Source.starImage H (borelResidual B₀) = modelBorel H K eK S := by
  rw [borelResidual, starImage_residualIn 2 H B₀ hBH, hB]
  change (pResidual 2 (modelBorel H K eK S)).map (modelBorel H K eK S).subtype = _
  rw [(pResidual_eq_top_iff 2 _).mpr (modelBorel_isPPerfect H K eK S),
    ← MonoidHom.range_eq_map, range_subtype]

/-- Inside K*, a subgroup containing and normalizing this Borel equals it. -/
theorem starImage_eq_modelBorel_of_normalizes
    (H K D : Subgroup G) (eK : Source.starImage H K ≃* SL) (S : Sylow 2 SL)
    (hDK : Source.starImage H D ≤ Source.starImage H K)
    (hBD : modelBorel H K eK S ≤ Source.starImage H D)
    (hDN : Source.starImage H D ≤ normalizer (modelBorel H K eK S : Set _)) :
    Source.starImage H D = modelBorel H K eK S := by
  apply le_antisymm ?_ hBD
  intro x hx
  have hr : x ∈ (sourceActor H K eK).range := by
    rw [sourceActor_range]
    exact hDK hx
  obtain ⟨g, rfl⟩ := hr
  apply mem_map_of_mem
  have hn := (modelBorel H K eK S).le_normalizer_comap (sourceActor H K eK) (hDN hx)
  rw [modelBorel, comap_map_eq_self_of_injective (sourceActor_injective H K eK),
    S.normalizer_normalizer] at hn
  exact hn

/-- Two-perfectness also survives the literal star quotient. -/
theorem starImage_isPPerfect (H D : Subgroup G) (hDH : D ≤ H)
    (hp : IsPPerfect 2 D) : IsPPerfect 2 (Source.starImage H D) := by
  have hi := hp.of_surjective (starHom H D hDH).rangeRestrict
    (starHom H D hDH).rangeRestrict_surjective
  rwa [range_starHom] at hi

/-- In particular the prescribed Borel lift has the required residual image. -/
theorem starImage_liftedBorelResidual [Finite G]
    (H K : Subgroup G) (hKH : K ≤ H) (eK : Source.starImage H K ≃* SL)
    (S : Sylow 2 SL) :
    Source.starImage H (borelResidual (borelLift H K hKH (modelBorel H K eK S))) =
      modelBorel H K eK S :=
  starImage_borelResidual_eq_modelBorel H K _ eK S
    ((borelLift_le H K hKH _).trans hKH)
    (starImage_borelLift H K hKH _ (modelBorel_le H K eK S))
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
