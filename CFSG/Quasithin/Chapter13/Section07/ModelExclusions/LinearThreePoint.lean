module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LinearThreeSource
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneResiduals
/-!
# The original K0 in the contained binary three-space

The checked three-dimensional source theorem supplies the whole natural
coordinates. The original point has dimension one, so a nonzero point
can be selected without an additional hypothesis. The full component
equivariance then identifies the actual image of K0=O²(C_K(V2)) with the
two-residual of the corresponding model point stabilizer.

Source: Aschbacher–Smith, 13.7.6(iii) and the n=3 construction, pp.939–940.
-/
@[expose] public section
open Subgroup Representation Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryNaturalDual.VectorStabilizers
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
/-- Original n=3 application: the marked point and K0 image are conclusions. -/
theorem linear_three_plane_residual_image_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    ∃ (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
      (u : Additive (Section08.Source.Utilde H V₃ V₁)),
      u ∈ sectionImage H V₃ V₁ V₂ ∧ u ≠ 0 ∧ eV u ≠ 0 ∧
      (∀ k : K, ∀ v,
        eV (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v) =
          linearRepresentation 3 (eK (QuotientGroup.mk' (pCore 2 K) k)) (eV v)) ∧
      ((residual (K ⊓ centralizer (V₂ : Set G))).subgroupOf K).map
        (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) =
          residual (representationStabilizer (linearRepresentation 3) (eV u)) := by
  obtain ⟨eH,eV,heK,heV⟩ := linear_three_full_action_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs
  have hP₂ : sectionImage H V₃ V₁ V₂ ≠ ⊥ := by
    intro hz
    have hh := plane_section_finrank d (H := H)
    rw [hz,finrank_bot] at hh
    omega
  obtain ⟨u,hu,hu0⟩ := (Submodule.ne_bot_iff _).mp hP₂
  have he : ∀ k : K, ∀ v,
      eV (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v) =
        linearRepresentation 3 (eK (QuotientGroup.mk' (pCore 2 K) k)) (eV v) := by
    intro k v
    rw [heV,heK]
    rfl
  refine ⟨eV,u,hu,hu0,(fun h => hu0 (eV.injective (h.trans (map_zero eV).symm))),he,?_⟩
  exact plane_centralizer_residual_model_image d (hH.2.1.trans d.first_normalizer.le)
    hKH ρ hρ (linearRepresentation 3) eK eV he u hu hu0
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
