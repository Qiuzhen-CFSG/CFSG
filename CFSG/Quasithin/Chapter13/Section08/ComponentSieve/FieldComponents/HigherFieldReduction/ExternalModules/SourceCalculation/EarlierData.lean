module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SupplementGeneration
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelReduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel

/-!
# Earlier local data for the repaired external source calculation

Source: Aschbacher–Smith, proof of 13.8.20(a), printed pp.954–955,
with Notation 13.2.1–2, 13.7.3(9), and the earlier 13.8.14 alternative.

The local quotient marks select the genuine cubic residual, its seed action,
and the solvable supplement. Together with the ambient rank bound they
construct the commuting S₃ and the structural inputs for the FF calculation.
The contract contains only preceding local data: neither the obsolete covered
centralizer formula and index nor the desired centralization is included.
The supplement-generation calculation is separate from these structural inputs.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation
open Components.Swapped.LinearTwo
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FFSections
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Genuine preceding local data, retaining the ordinary and covered quotient
marks, theta, and the actual Sylow intersection. No source conclusion of the
external FF argument occurs as a field. -/
structure EarlierLocalData (H K X L T V V₃ V₁ M : Subgroup G)
    (S : Sylow 2 (Source.starImage H K)) : Prop where
  local_cases : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
    (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁)
  ordinary_card : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
    Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 3
  covered_action : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
    Nonempty (LocalAction.NaturalSetup L T V V₁ V₃)
  covered_factor : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
    one L T V₁ = plus L T V₁ ⊔ zero L
  seed_commutator : V₃ = ⁅V₃, one L T V₁⁆
  theta : one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}
  solvable_overgroups : ∀ J : Subgroup G, one L T V₁ ⊔ T ≤ J →
    J ≤ normalizer (V₁ : Set G) → Group.IsSolvable J → J ≤ M
  sylow : Chapter1.IsSylowIn 2 T H
  sylow_inter : (S : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype =
    Source.starImage H T ⊓ Source.starImage H K

namespace EarlierLocalData
variable {H K X L T V V₃ V₁ M : Subgroup G}
  {S : Sylow 2 (Source.starImage H K)} (d : EarlierLocalData H K X L T V V₃ V₁ M S)

omit [Finite G] in
include d in
/-- Forget the extra cover property while preserving the actual carrier mark. -/
theorem marked_cases :
    (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁) :=
  d.local_cases.imp id (fun h => h.2)

omit [Finite G] in
include d in
/-- The same local alternatives in the form consumed by the Fitting theorem. -/
theorem fitting_cases :
    (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = plus L T V₁) :=
  d.local_cases.imp id (fun h => ⟨h.1, h.2.2⟩)
end EarlierLocalData

variable (H K X L V V₃ V₁ M : Subgroup G) (T : Sylow 2 G)
  [(K.subgroupOf H).Normal]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
  (f : SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁) (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
  (S : Sylow 2 (Source.starImage H K))
  (d : EarlierLocalData H K X L (T : Subgroup G) V V₃ V₁ M S)

include f d in
/-- Construct the source FF structural inputs from the minimal preceding data.
Neither full-L₁ commutator generation nor any Borel centralizer formula is used. -/
theorem source_ff_inputs
    (ha : ExternalXAlternative H K X)
    (hmodel : Structure.HigherFieldCarrier (Source.starImage H K))
    (hfit : SolvableExclusion.ResidualAlternative L (one L (T : Subgroup G) V₁)
      (plus L (T : Subgroup G) V₁) (Components.Fitting.twoFittingResidual H)) :
    ∃ s : S₃ →* Source.Hstar H,
      AdequateExternalInputs H K X (one L (T : Subgroup G) V₁) (T : Subgroup G) V₃ V₁ ρ s := by
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  let : (Source.starImage H K).Normal := by unfold Source.starImage; infer_instance
  have hgen : H = K ⊔ (one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G)) := by
    rw [f.generation, f.single_component, f.overlap]
  obtain ⟨_, hp, hc, hsol, hseed⟩ := Structure.MarkedBorel.selected_local_inputs
    L (T : Subgroup G) V V₁ V₃ X T.isPGroup' f.setup.line_normalized d.marked_cases
    d.ordinary_card d.covered_action d.covered_factor d.seed_commutator
  let : Group.IsSolvable (one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) : Subgroup G) := hsol
  have hselected := Structure.selected_fitting_alternative H L
    (one L (T : Subgroup G) V₁) (plus L (T : Subgroup G) V₁) X d.fitting_cases hfit
  obtain ⟨hcstar, hnot, hn, hr⟩ := Structure.external_cubic_rank 𝒦 H K X
    f.sqtk f.component_le f.component hp hc ha
  have hrs : primeRank 3 (Source.starImage H K) ≤ 1 := by
    rw [← Structure.threeRank_eq_star H K f.component_le f.component.subnormal]
    exact hr
  obtain ⟨model, hz, _, _⟩ := hmodel.external_structure hrs
  obtain ⟨s, hi, hs, hm, hg, _⟩ := Structure.source_cubic_action H K X
    (one L (T : Subgroup G) V₁) (T : Subgroup G) V₃ V₁ hgen hc ha hz hselected ρ f.conjugation hseed
  exact ⟨s, {
    component_normal := inferInstance
    centerless := hz
    component_rank := hr
    model := model
    solvable := hsol
    one_twoPerfect := residual_isPPerfect _
    fitting := hselected
    cubic_card := hcstar
    cubic_normal := hn
    embedding := hi
    commuting := fun k g => hs ⟨g, rfl⟩ k k.property
    mark := hm
    cubic_generation := hg }⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation

end
