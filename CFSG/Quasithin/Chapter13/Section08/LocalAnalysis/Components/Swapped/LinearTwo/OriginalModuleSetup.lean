module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelLift
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalResidual
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SeedTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.OrthogonalEight.Model

/-!
# Source module targets for the exchanged linear-two component

The original residual identity puts the point residual L₁ inside K₀.
The original seed commutator theorem then identifies the whole literal
U_H/V₁ with its K₀-commutator, before any module classification is used.
The classification target below retains only the properties required by
13.8.16: cross-factor fixation in a proper quotient, or actual group and
module coordinates for the whole natural orthogonal action. It asserts
neither alternative without a proof.

Source: Aschbacher--Smith, 13.8.16(1), printed pp.952--953.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hmoving

/-- The point residual belongs to the actual moving component orbit. -/
theorem one_le_orbit {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n)) :
    one L T V₁ ≤ conjugateSpanBy K (T : Subgroup G) := by
  apply marked_le_orbit H _ (one L T V₁) (le_sup_left.trans hH.1.2)
    (residual_isPPerfect _)
    (fun x => ⟨1, by simpa using
      Section07.ModelExclusions.point_residual_quotient_cube (localNaturalSetup d) x⟩)
  exact threeResidual d h hF9all hcentral hcomm hsource hH hKH hK hmoving hn hmodel

/-- The entire original module is moved by K₀; no constituent saturation
or final model is assumed to obtain this equality. -/
theorem moved_eq_top {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) :
    subspaceCommutator ρ ⊤ (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) = ⊤ := by
  apply ModuleAlternatives.source_moved_eq_top H V₃ V₁ ρ hρ K (one L T V₁) T hgen.symm
    (one_le_orbit d h hF9all hcentral hcomm hsource hH hKH hK hmoving hn hmodel)
    (Section07.ModelExclusions.point_residual_normalizes_seed (localNaturalSetup d))
    (d.line_le_plane.trans d.plane_le_seed)
  rw [commutator_comm, Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup d)]
  exact le_sup_left

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]

/-- The joint output needed from source cases (a) and (b1). Case (b1)
uses the zero submodule; no semisimplicity or direct-sum premise is imposed. -/
def HasCrossFactorQuotient (ρ : Representation (ZMod 2) D U) (A B : Subgroup D) : Prop :=
  ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧
    subspaceCommutator W.quotientRepresentation ⊤ A ≤ fixedSpace W.quotientRepresentation B ∧
    subspaceCommutator W.quotientRepresentation ⊤ B ≤ fixedSpace W.quotientRepresentation A

/-- The whole-module alternative (b2), marked on the literal component
orbit. Both the group isomorphism and intertwining coordinates are retained. -/
def HasOrthogonalFourOrbit (ρ : Representation (ZMod 2) D U) (N : Subgroup D) : Prop :=
  ∃ f : N ≃* OrthogonalEight.G, ∃ e : U ≃ₗ[ZMod 2] OrthogonalEight.V,
    ∀ (g : N) (v : U), e (ρ g v) = OrthogonalEight.action (f g) (e v)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
