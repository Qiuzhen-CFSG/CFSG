module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.Setup
public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy
public import CFSG.Quasithin.Chapter1.SourceInputs.InvolutionCentralizers

/-!
# Applying 1.2.11 and 1.1.5--6 to the same deleted-point centralizer

Once its global two-core is exactly the marked involution, the centralizer
cannot have characteristic two: its order-960 block would lie in a group
of order two. The C-component containing that block is consequently an
ordinary component by 1.2.11. Lemma 1.1.6 supplies the complete 1.1.5
catalogue with the original central involution z, rather than a newly chosen
involution. The global core, component containment and residual commutator
are explicit inputs; this module does not assert their source construction.

Source: Aschbacher--Smith, final paragraph of 14.3.20, printed p.998.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
variable {F : InvariantFlag T V 2} {L A : Subgroup G}

namespace MarkedPoint
variable (P : MarkedPoint F L A)

/-- The three geometric premises preceding the Chapter 1 applications.
Each subgroup and residual uses the original ambient embedding. -/
structure CoreComponentInputs (z : G) : Prop where
  core_eq : P.globalCentralizer.pCoreIn 2 = zpowers P.element
  component : ∃ B : Subgroup G, B ∈ Chapter1.cComponentsIn P.globalCentralizer ∧
    P.blockCentralizer ≤ B
  commutator : z ∈ ⁅V,
    (pResidual 2 (P.globalCentralizer ⊓ normalizer (V : Set G) : Subgroup G)).map
      (P.globalCentralizer ⊓ normalizer (V : Set G)).subtype⁆

/-- The remaining catalogue exclusion must use these actual component actions. -/
def ClassifiedComponent (z : G) : Prop :=
  ∃ B : Subgroup G, B ≤ P.globalCentralizer ∧ P.blockCentralizer ≤ B ∧
    IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer) ∧
    B = ⁅B, zpowers z⁆ ∧
    HasModelAction115 (B.subgroupOf P.globalCentralizer) z

theorem not_characteristicTwo_of_core_eq
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element) :
    P.globalCentralizer ∉ Chapter1.He G := by
  intro hHe
  have hcentral : P.globalCentralizer ≤ centralizer (zpowers P.element : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hsmall : P.blockCentralizer ≤ zpowers P.element := by
    intro x hx
    rw [← hcore]
    exact hHe ⟨hx.2, hcore.symm ▸ hcentral hx.2⟩
  have hc := Nat.card_le_card_of_injective (inclusion hsmall) (inclusion_injective hsmall)
  rw [P.blockCentralizer_card, Nat.card_zpowers, P.point_order] at hc
  omega

/-- The source Chapter 1 applications, retaining the specified z throughout. -/
theorem classifiedComponent_of_coreComponentInputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    [IsElementaryAbelian 2 V] (hVA : V ≤ A) (hVT : V ≤ (T : Subgroup G))
    (z : G) (hz : F.Vi 1 = zpowers z)
    (hSylow : Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer)
    (hinput : P.CoreComponentInputs z) : P.ClassifiedComponent z := by
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← hz]
    simpa using F.card 1 (by decide)
  have hzmem : z ∈ F.Vi 1 := hz.symm ▸ mem_zpowers z
  have hzT : z ∈ (T : Subgroup G) := hVT (F.le_seed 1 hzmem)
  have hzB0 : z ∈ P.blockCentralizer := P.factor_le_blockCentralizer (hVA (F.le_seed 1 hzmem))
  have hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t := by
    intro t ht
    exact (normalizer_le_centralizer_of_card_two (F.Vi 1)
      (by simpa using F.card 1 (by decide)) (F.invariant 1 ht) z hzmem).symm
  have hlocal : P.globalCentralizer ∈ Chapter1.H G := by
    change P.globalCentralizer.pCoreIn 2 ≠ ⊥
    rw [hinput.core_eq]
    exact zpowers_ne_bot.mpr (by intro he; simpa [he] using P.point_order)
  obtain ⟨B, hB, hKB⟩ := hinput.component
  have hq : IsQuasisimple B :=
    (Chapter1.lemma_1_2_11_involution hG T P.globalCentralizer B z hlocal hSylow hB
      hz2 (hKB hzB0) ⟨hzT, hzB0.2⟩ hzc
      ⟨V, hVA.trans (P.factor_le_blockCentralizer.trans inf_le_right),
        inferInstance, hinput.commutator⟩ (by
        rw [hinput.core_eq, zpowers_eq_closure, centralizer_closure])).resolve_right
      (P.not_characteristicTwo_of_core_eq hinput.core_eq)
  let := hq
  have hcomponent : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer) :=
    ⟨hB.2.subnormal, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hB.1).symm⟩
  obtain ⟨S, hS⟩ := hSylow
  obtain ⟨M₁, hCM₁, hM₁⟩ :=
    Finite.exists_le_maximal (isTwoLocal_involution_centralizer hz2)
  have hdne : zpowers P.element ≠ ⊥ :=
    zpowers_ne_bot.mpr (by intro he; simpa [he] using P.point_order)
  have hdgroup : IsPGroup 2 (zpowers P.element) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, P.point_order]; decide)
  have hdC : zpowers P.element ≤ P.globalCentralizer :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCC : centralizer (zpowers P.element : Set G) = P.globalCentralizer := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hCN : P.globalCentralizer ≤ normalizer (zpowers P.element : Set G) :=
    hCC ▸ _root_.centralizer_le_normalizer _
  have h115 : Chapter1.Lemma115Hypotheses P.globalCentralizer S M₁ z := by
    apply Chapter1.lemma_1_1_6 hdne hdgroup hdC hCC.le hCN S T
      (hS.le.trans inf_le_left) hz2 hzT hzc hM₁ hCM₁
    intro N hN hTN
    exact Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T N hN hTN)
  have hmodel := Chapter1.lemma_1_1_5_three_knownSimple hG P.globalCentralizer S M₁ z h115
    (B.subgroupOf P.globalCentralizer) hcomponent
  refine ⟨B, hB.1, hKB, hcomponent, ?_, hmodel.2.2⟩
  simpa only [map_subgroupOf_eq_of_le hB.1] using hmodel.1

end MarkedPoint
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
