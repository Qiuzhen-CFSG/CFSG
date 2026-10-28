module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.CentralSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.FullAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.Lift
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.MovedEndpoint
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SymmetricFive
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction

/-!
# Reconstruction of the exceptional marked action

The full marked B.4.2(5) output and compatible literal constituent and
multiplicity quotients construct the five-by-three tensor coordinates on
the actual two-conjugate orbit. Projectivity proves that its central
bottom is zero, and the quotient coordinates lift to the orbit itself.

The full-action extension identifies every ambient actor, using the tensor
normalizer and an odd actor lifted from the actual constituent group on U.
The complete earlier Fitting alternative and solvable supplement prove that
the action on W is faithful. Full coordinates on W retain the original
module equivalence and both pointwise K* and S₃ markings.

`source_moved_tensor_branch_impossible` then excludes the exceptional branch.
The literal inclusion W → U transfers displacement ranks and quadraticity:
it rules out transvections on U, discharges the antecedent of 13.8.18(4),
and bounds the actual conjugate actor Vα* by two on W. The earlier rank
bound gives the contradiction. The exact earlier implication, actual
H-conjugation and placement Vα* ≤ T₀* ≤ K* remain visible for final assembly.

The old `source_coordinates_of_whole_space` API is preserved as a conditional
theorem. Its premise W = U is not needed by the moved-space endpoint and is
not asserted here. F.9.18(6a) supplies W = [U,K*], while source generation
is U = [U,X*]. The later L₁ ≤ K in alternative (b), 13.7.5 and 13.8.21 do
not supply whole-space generation in external alternative (a).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20, printed p.954; B.4.2(5), printed p.86; I.1.6(1), printed p.408.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open scoped TensorProduct IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

variable {G : Type*} [Group G]
    (H K X V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (s : S₃ →* Source.Hstar H)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (W : Subrepresentation ρ)

/-- The exceptional marked constituent constructs tensor coordinates on the actual
moved orbit and proves its central bottom is zero. It does not identify the orbit
with the entire source module or identify the full ambient acting group. -/
theorem source_moved_coordinates
    {E N : Type*} [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) E N)
    (e : MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (r : ConstituentRealization ρ (Source.starImage H K) σ (generalizedFitting E))
    (a : SectionMultiplicity ρ s (LinearTwo.centralBottom ρ (Source.starImage H K) W) W
      ≃ₗ[ZMod 2] N)
    (ha : ∀ k v,
      a (sectionMultiplicityAction ρ (Source.starImage H K).subtype s hs
        (LinearTwo.centralBottom ρ (Source.starImage H K) W) W k v) =
      σ (r.component k) (a v))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (hgen : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)
    (hne : r.space ≠ r.space.map (ρ (s cubic)))
    (horbit : W.toSubmodule = r.space ⊔ r.space.map (ρ (s cubic))) :
    LinearTwo.centralBottom ρ (Source.starImage H K) W = ⊥ ∧
      Nonempty (FactorCoordinates W.toRepresentation (Source.starImage H K) s) := by
  have hC := centralBottom_eq_bot ρ (Source.starImage H K) σ _ _ e r.component
    W r.space r.irrPlus r.linearEquiv r.component_intertwines (s cubic) hne horbit
  refine ⟨hC, ⟨?_⟩⟩
  exact upperFactorCoordinates ρ (Source.starImage H K) σ _ _ e s hs
    (LinearTwo.centralBottom ρ (Source.starImage H K) W) W hC r.component a
    (by rw [hmark]; exact hgen) ha

/-- Package the proved full-action extension on the literal source carrier.
The supplied factor coordinates need only intertwine K* and the specified S₃;
the realized marked constituent supplies the missing odd ambient actor. -/
def coordinatesOfFactors
    {E N : Type*} [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) E N)
    (hfaithful : Function.Injective ρ) (hσ : Function.Injective σ)
    (c : FactorCoordinates ρ (Source.starImage H K) s)
    (r : ConstituentRealization ρ (Source.starImage H K) σ (generalizedFitting E))
    (e : MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X) :
    SymmetricFive.Coordinates H K X V₃ V₁ ρ where
  groupEquiv := c.fullActionEquiv hfaithful hσ r e
  moduleEquiv := c.moduleEquiv
  equivariant := c.fullActionEquiv_intertwines hfaithful hσ r e
  component_mark := c.fullActionEquiv_map_component hfaithful hσ r e
  cubic_mark := by
    rw [← hmark]
    exact c.fullActionEquiv_map_cubic hfaithful hσ r e

/-- Complete marked coordinates once the source whole-space deduction is supplied.
Central-bottom vanishing, lifting, full ambient equivariance, and both subgroup
markings are proved here. The explicit `hwhole` premise is the remaining
external-branch obligation; this theorem does not assert it from the constituent
classification or from cubic generation alone. -/
theorem source_coordinates_of_whole_space
    {E N : Type*} [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) E N)
    (hfaithful : Function.Injective ρ) (hσ : Function.Injective σ)
    (e : MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (r : ConstituentRealization ρ (Source.starImage H K) σ (generalizedFitting E))
    (a : SectionMultiplicity ρ s (LinearTwo.centralBottom ρ (Source.starImage H K) W) W
      ≃ₗ[ZMod 2] N)
    (ha : ∀ k v,
      a (sectionMultiplicityAction ρ (Source.starImage H K).subtype s hs
        (LinearTwo.centralBottom ρ (Source.starImage H K) W) W k v) =
      σ (r.component k) (a v))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (hgen : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)
    (hne : r.space ≠ r.space.map (ρ (s cubic)))
    (horbit : W.toSubmodule = r.space ⊔ r.space.map (ρ (s cubic)))
    (hwhole : W.toSubmodule = ⊤) :
    Nonempty (SymmetricFive.Coordinates H K X V₃ V₁ ρ) := by
  obtain ⟨_, ⟨c⟩⟩ := source_moved_coordinates H K X V₃ V₁ ρ s hs W
    σ e r a ha hmark hgen hne horbit
  let c' := factorCoordinatesOfTop ρ (Source.starImage H K) s W hwhole c
  exact ⟨coordinatesOfFactors H K X V₃ V₁ ρ s σ hfaithful hσ c' r e hmark⟩

/-- Full marked H* coordinates on the literal two-conjugate orbit W.
The solvable supplement and complete earlier 13.8.14 alternative discharge
faithfulness; the realized B.4.2 constituent on U supplies the odd actor.
Neither faithfulness on W nor W = U is a premise. -/
theorem source_moved_full_coordinates
    [Finite G] [(K.subgroupOf H).Normal]
    (L L₁ L₁plus T : Subgroup G)
    (hH : H = K ⊔ L₁ ⊔ T) [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = L₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = L₁plus))
    (hfit : SolvableExclusion.ResidualAlternative L L₁ L₁plus
      (Components.Fitting.twoFittingResidual H))
    {E N : Type*} [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) E N)
    (e : MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (r : ConstituentRealization ρ (Source.starImage H K) σ (generalizedFitting E))
    (a : SectionMultiplicity ρ s (LinearTwo.centralBottom ρ (Source.starImage H K) W) W
      ≃ₗ[ZMod 2] N)
    (ha : ∀ k v,
      a (sectionMultiplicityAction ρ (Source.starImage H K).subtype s hs
        (LinearTwo.centralBottom ρ (Source.starImage H K) W) W k v) =
      σ (r.component k) (a v))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (hgen : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)
    (hne : r.space ≠ r.space.map (ρ (s cubic)))
    (horbit : W.toSubmodule = r.space ⊔ r.space.map (ρ (s cubic))) :
    Nonempty (FullCoordinates W.toRepresentation (Source.starImage H K) s) := by
  obtain ⟨_, ⟨c⟩⟩ := source_moved_coordinates H K X V₃ V₁ ρ s hs W
    σ e r a ha hmark hgen hne horbit
  have hi := WholeSpace.External.source_moved_faithfulness H K X L₁ T V₃ V₁ ρ s W c
    L L₁plus (by simpa only [sup_assoc] using hH) hlocal hfit hmark
  exact ⟨c.fullCoordinatesOfRealizedConstituent hi.1 r e⟩

/-- Source-facing exceptional endpoint for the external L₂ branch of
13.8.20. The constituent, its actual orbit and multiplicity quotient are
retained. The only earlier endpoint input is exactly 13.8.18(4), applied
after proving its no-transvection antecedent on U. The source conjugate
placement and quadraticity remain explicit for the final chapter assembly.
All coordinate extension, moved-action faithfulness and carrier restriction
obligations are discharged here. -/
theorem source_moved_tensor_branch_impossible
    [Finite G] [(K.subgroupOf H).Normal]
    (L L₁ L₁plus Vγ Vα T₀ : Subgroup G) (T : Sylow 2 G)
    (hH : H = K ⊔ L₁ ⊔ (T : Subgroup G))
    [Group.IsSolvable (L₁ ⊔ (T : Subgroup G) : Subgroup G)]
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = L₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = L₁plus))
    (hfit : SolvableExclusion.ResidualAlternative L L₁ L₁plus
      (Components.Fitting.twoFittingResidual H))
    {E N : Type*} [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) E N)
    (e : MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (r : ConstituentRealization ρ (Source.starImage H K) σ (generalizedFitting E))
    (a : SectionMultiplicity ρ s (LinearTwo.centralBottom ρ (Source.starImage H K) W) W
      ≃ₗ[ZMod 2] N)
    (ha : ∀ k v,
      a (sectionMultiplicityAction ρ (Source.starImage H K).subtype s hs
        (LinearTwo.centralBottom ρ (Source.starImage H K) W) W k v) =
      σ (r.component k) (a v))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (hgen : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)
    (hne : r.space ≠ r.space.map (ρ (s cubic)))
    (horbit : W.toSubmodule = r.space ⊔ r.space.map (ρ (s cubic)))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
    (earlier_13_8_18_4 : SeedAction.IsConjugation H V₃ V₁ ρ →
      H = K ⊔ L₁ ⊔ (T : Subgroup G) →
      (∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) →
      1 < rank (Source.starImage H Vγ))
    (hVγH : Vγ ≤ H) (h : H)
    (hconj : Vγ.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Source.starImage H Vα ≤ Source.starImage H T₀)
    (hcore : Source.starImage H T₀ =
      (Source.starImage H L₁ ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2)
    (hT₀K : Source.starImage H T₀ ≤ Source.starImage H K)
    (hquad : IsQuadratic ρ (Source.starImage H Vγ)) : False := by
  obtain ⟨c⟩ := source_moved_full_coordinates H K X V₃ V₁ ρ s hs W
    L L₁ L₁plus (T : Subgroup G) hH hlocal hfit σ e r a ha hmark hgen hne horbit
  exact tensor_branch_impossible_on_moved H K L₁ V₃ V₁ Vγ Vα T₀ T
    ρ s W hρ hH c earlier_13_8_18_4 hVγH h hconj hplace hcore hT₀K hquad

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

end
