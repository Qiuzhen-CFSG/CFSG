module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation.Critical

/-!
# The moved tensor endpoint with original geometry discharged

The original local source setup constructs every earlier geometric input and
an actual initial critical pair. The marked Borel calculation then places the
selected Vα* inside the component Sylow. Its rank exceeds one, whereas its
quadratic action on the faithful moved tensor module has order at most two.
This proves the exceptional endpoint without a supplied critical pair,
selected geometry, rank callback, or equality of the moved and full modules.

The preceding component/F.9.18 and marked local Borel data, and the actual
moved tensor coordinates, remain the independent field and model inputs.
Source: Aschbacher–Smith 13.8.18(4) and the exceptional L₂(4) branch of
13.8.20(a), printed pp.953–954, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
open CriticalGeometry TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.HigherFieldReduction
open ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FFSections
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K X : Subgroup G}
  [(K.subgroupOf H).Normal]
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Actual external-field consumer: the moved tensor alternative is impossible
under the original local geometry. All EarlierInputs and the initial critical
pair are constructed, with the literal star maps and H-conjugator retained. -/
theorem external_tensor_impossible
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
    (f : SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁)
      (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
    (S : Sylow 2 (Source.starImage H K))
    (localData : SourceCalculation.EarlierLocalData H K X L (T : Subgroup G) V V₃ V₁ M S)
    (ha : ExternalXAlternative H K X)
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H) (W : Subrepresentation ρ)
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ (Source.starImage H K))
    (coordinates : LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation
      (Source.starImage H K) s) : False := by
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.2.1)
  let : (Source.starImage H K).Normal := by unfold Source.starImage; infer_instance
  have e := earlier_inputs d hH hF9 hcentral hcomm ρ f.conjugation
  obtain ⟨initial, _, _⟩ := (localNaturalSetup d).exists_criticalPair d.abelian_span hF9
  obtain ⟨w, hplace, _, hcore, hTK⟩ := SourceCalculation.exists_critical_witness
    H K X L V V₃ V₁ M T ρ P f S localData ha hF9.V_le_H initial e s W hW coordinates
  have hgen : H = K ⊔ one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) := by
    rw [f.generation, f.single_component, f.overlap, sup_assoc]
  exact LinearTwo.FiveReconstruction.tensor_branch_impossible_on_moved H K
    (one L (T : Subgroup G) V₁) V₃ V₁ w.pair.Vgamma w.alpha ((T : Subgroup G) ⊓ K)
    T ρ s W f.conjugation hgen coordinates (fun _ _ _ => w.rank_gt_one)
    w.actor_le w.conjugator rfl hplace hcore hTK w.quadratic

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
