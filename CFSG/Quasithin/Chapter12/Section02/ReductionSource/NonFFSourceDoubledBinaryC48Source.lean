module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedFixedModule
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC28

/-!
# The C.4.8 source reduction for the complete doubled orbit

The reciprocal witness supplies the genuine C.2.8 input with the whole marked
doubled source orbit as its module.  C.4.8 then chooses an escaping component
of the generalized Fitting subgroup.  In the ordinary branch the original
component contains the seed and the whole orbit.  In the constrained branch,
the p.154 fixed-space construction is realized literally: the orbit lies in
the commutator of the star module with the centralizer of the span two-core,
and the original span normalizes it.

This file establishes source placement and the ordinary/constrained split.  It
does not assert the later parabolic residual marking or the homogeneous module
row classification; those remain explicit premises for the C.4.8 row consumer.

Source: Aschbacher--Smith C.4.8, printed pp.153--154, using C.2.7.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The p.154 fixed-space commutator for the actual C.2.8 witness contains the
whole source orbit and is normalized by its original span. -/
theorem sourceOrbit_binary_witness_constrained_fixed_moved
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let Q := (starV (K.map H.subtype) (J.pCoreIn 2)).map
      (K.map H.subtype ⊔ J.pCoreIn 2).subtype
    let W := ⁅Q ⊓ centralizer (LH.pCoreIn 2 : Set G),LH⁆
    D.sourceOrbit ≤ W ∧ W ≤ Q ∧ LH ≤ normalizer (W : Set G) := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let M := H ⊓ normalizer (L : Set G)
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy LH M = LH :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  dsimp only [LH, M] at hspan
  simpa only [hspan] using hc.constrained_module_fixed_moved K hK hq hout hfK

/-- C.4.8's generalized-Fitting escape, instantiated on the complete source
orbit, yields the ordinary component placement or the constrained p.154 input. -/
theorem sourceOrbit_binary_witness_c48_source_reduction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (hescape : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let M := H ⊓ normalizer (L : Set G)
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧ LH ≤ normalizer (K.map H.subtype : Set G) ∧
      ((IsComponent H K ∧ LH.subgroupOf H ≤ K ∧ D.sourceOrbit.subgroupOf H ≤ K) ∨
       (generalizedFitting K = pCore 2 K ∧
        Input KnownSimple.IsKnownSimple H (J.pCoreIn 2) M (K.map H.subtype) ∧
        let Q := (starV (K.map H.subtype) (J.pCoreIn 2)).map
          (K.map H.subtype ⊔ J.pCoreIn 2).subtype
        let W := ⁅Q ⊓ centralizer (LH.pCoreIn 2 : Set G),LH⁆
        D.sourceOrbit ≤ W ∧ W ≤ Q ∧ LH ≤ normalizer (W : Set G))) := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let M := H ⊓ normalizer (L : Set G)
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy LH M = LH :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  dsimp only [LH, M] at hspan
  have he : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H := by
    intro he
    exact hescape (he.trans (subgroupOf_mono H inf_le_right))
  obtain ⟨K,hK,hq,hout,hLK,hcases⟩ := hc.ordinary_or_constrained_escape he
  refine ⟨K,hK,hq,hout,(by simpa only [hspan] using hLK),?_⟩
  rcases hcases with ho | hfK
  · exact Or.inl ⟨ho,hc.ordinary_component_contains_original K ho,
      (hc.ordinary_module_placement K ho).1.trans inf_le_right⟩
  · exact Or.inr ⟨hfK,hc.constrained_source_input K hK hq hout hfK,
      D.sourceOrbit_binary_witness_constrained_fixed_moved h hd F hF hmodel hw
        hWJ hJC K hK hq hout hfK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
