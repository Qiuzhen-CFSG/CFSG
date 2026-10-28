module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Classification
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents

/-!
# Assembly of the marked small MS configuration

The full C.1.32 comparison constructs the A₆/G₂ blocks or a binary SL₃
core quotient, and proves that quotient simple. Specializing the full
C.1.34 implication and the genuine central-omega conclusion of 15.3.8
eliminates cases (4) and (5). For (4), its central E₄ exhausts the omega
center; for (5), centrality of that omega center is already explicit.
Both contradict MS3. Every layer of the five-case input is retained.

The independent B.5.6 comparison selects an actual Irr⁺ constituent
containing V₂. Its central quotient is injective on V₂, and the exact
stabilizer is the original M_L*. In the doubled case the output includes
both actual coordinate summands and their separate transported lines.
Simplicity now discharges the premise of the parent's quotient comparison,
so the output also contains L/O₂(L) ≃ L* compatible with every original
lift and the equality [O₂(L),L] = [O₂(I),L].

The assembly assumes only the genuine earlier local conclusions, the
catalogue-dependent SQTK hypothesis and the authorized universal earlier
FF/MS implications. Those implications are not proved here. It derives
all local module, constituent and block alternatives; the parent retains
the subsequent extension calculation and exclusion in 15.3.31.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.31, printed p.1132 (PDF p.1149), using 15.3.8/11/26–29,
B.5.3–6, pp.104–105, and C.1.31–34, pp.135–137.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open EightGeometry.NaturalModule.Recognition Constituents
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Specialize both full MS classifications at the actual small marking.
The central omega hypothesis is precisely the earlier conclusion 15.3.8. -/
theorem survivingSmallCases_of_source {κ : GroupClass.{u}}
    (earlier : EarlierMSClassifications κ)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hSQTK : IsSQTK κ I)
    (hf : HasCharacteristicTwo I) (hYL : d.Yplus ≤ c.L)
    (hLS : I = c.L ⊔ d.S) (hn : (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (h29 : ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf I).Normal)
    (hfacts : Parabolics.RankOneFacts d I) (hcontrol : SolvableInvariantControl d I)
    (h8 : d.ZS = centralOmegaIn d.S ∧ Nat.card d.ZS = 4)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    SmallMSPair κ c.L d.S ∧ SurvivingSmallCases c.L d.S ∧
      IsSimpleGroup (c.L ⧸ pCore 2 c.L) := by
  have hms := smallMSPair_of_source d c hSQTK hf hLS hn hS h29 hm
  obtain ⟨ha, hs⟩ := classification_of_source earlier d hI c hSQTK hf hYL
    hLS hn hS h29 hfacts hcontrol hm
  refine ⟨hms, ?_, hs⟩
  rcases ha with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · apply Or.inr ∘ Or.inr
    apply linearThree_survivors_of_classification earlier hms (hLS ▸ hS) _ h
    change Nat.card (centralOmegaIn d.S) = 4
    rw [← h8.1]
    exact h8.2

/-- The first paragraph of 15.3.31, as an output for the remaining extension
argument. Every action is on the original U_L and every line uses the original
star map. The quotient equivalence retains compatibility on all lifts. -/
structure SmallMSConclusion (κ : GroupClass.{u})
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) (hLS : I = c.L ⊔ d.S)
    (hf : HasCharacteristicTwo I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) : Prop where
  msPair : SmallMSPair κ c.L d.S
  cases : SurvivingSmallCases c.L d.S
  simple : IsSimpleGroup (c.L ⧸ pCore 2 c.L)
  quotient : ∃ e : (c.L ⧸ pCore 2 c.L) ≃* d.starImage I c.L,
    ∀ l : c.L, e (QuotientGroup.mk' (pCore 2 c.L) l) = componentMap d c l
  core_eq : extensionCore c.L = msQ c.L d.S
  marked :
    let _ := component_internal_elementary d c hf P hP
    Nonempty (MarkedConstituent (componentAction d c hn hLS hf P hP)
      (d.starImage I c.L) (planeSpace d c)
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)))
  summands :
    let _ := component_internal_elementary d c hf P hP
    let ρ := componentAction d c hn hLS hf P hP
    let Lstar := d.starImage I c.L
    let Pstar := (d.starImage I (d.M ⊓ c.L)).subgroupOf Lstar
    IsIrrPlus ρ Lstar ⊤ ∨
      ∃ (e : ActionEquiv (ρ.comp Lstar.subtype) (repeated binaryNatural 2))
        (b : BinaryDoubledLine ((planeSpace d c).map e.linearEquiv.toLinearMap)
          (Pstar.map e.groupEquiv.toMonoidHom)),
        (∀ i : Fin 2, IsIrrPlus (ρ.comp Lstar.subtype) ⊤ (copyEmbedding e i).range ∧
          Nat.card (b.plane.map (copyEmbedding e i)) = 4 ∧
          subspaceStabilizer (ρ.comp Lstar.subtype)
            (b.plane.map (copyEmbedding e i)) = Pstar) ∧
        Disjoint (b.plane.map (copyEmbedding e 0)) (b.plane.map (copyEmbedding e 1))

/-- Construct the full marked MS conclusion from the genuine earlier local
facts and the authorized universal B.5.6/C.1.32/C.1.34 implications. No local
module alternative, constituent, quotient simplicity or block exclusion is
assumed. The final exclusion of the small branch belongs to the parent. -/
theorem markedMS_of_source {κ : GroupClass.{u}}
    (earlier : EarlierMSClassifications κ)
    (ff : ProjectiveLine.CompleteClassificationInput.{u,u} κ)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hSQTK : IsSQTK κ I)
    (hf : HasCharacteristicTwo I) (hYL : d.Yplus ≤ c.L)
    (hLS : I = c.L ⊔ d.S) (hn : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (h29 : ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf I).Normal)
    (hfacts : Parabolics.RankOneFacts d I) (hcontrol : SolvableInvariantControl d I)
    (hline : LineData d I) (hRank : primeRank 3 d.Yplus = 1)
    (hYRank : 2 ≤ primeRank 3 d.Y)
    (h8 : d.ZS = centralOmegaIn d.S ∧ Nat.card d.ZS = 4)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    SmallMSConclusion κ d c hn hLS hf P hP := by
  obtain ⟨hms, ha, hs⟩ := survivingSmallCases_of_source earlier d hI c hSQTK
    hf hYL hLS hn ⟨P, hP⟩ h29 hfacts hcontrol h8 hm
  let _ := hs
  let _ := component_internal_elementary d c hf P hP
  have hVT : d.V ≤ (d.T : Subgroup G) :=
    d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le)
  obtain ⟨hw, hd⟩ := marked_alternative_of_source d c hn hLS hf P hP
    hline hYL hRank hYRank hVT hSQTK ff hm
  refine ⟨hms, ha, hs, ?_, ?_, hw, ?_⟩
  · exact ⟨coreQuotientEquivStar d c hn P hP,
      coreQuotientEquivStar_apply d c hn P hP⟩
  · exact (extensionCore_eq_overgroup d c hYL hn).trans
      (congrArg (fun J : Subgroup G => ⁅J.pCoreIn 2, c.L⁆) hLS)
  · rcases hd with h | ⟨e, ⟨b⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, b, binaryLine_copy_markings _ e _ _ b⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

end
