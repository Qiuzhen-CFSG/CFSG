module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Residual
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrainedFinite
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# The original binary-three section excludes the small constrained rows

The original normalized intersection residual has its literal SL3(2)
quotient. Its inner action with solvable kernel forces all 168 factors into
the selected component's core-central quotient, and hence into its actual
star image. This excludes A5, A6, and the full triple cover of A6 by order.
The cubic center of the triple-cover row is retained explicitly.
Source: Aschbacher--Smith C.2.7 and C.4.3--8, pp.145--154.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
private instance : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
private instance : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The entire order of the original simple section survives in the actual
component core-central quotient. -/
theorem sourceOrbit_binary_witness_constrained_core_order_dvd
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    : 168 ∣ Nat.card (coreCentralQuotient K) := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  obtain ⟨_,_,_,_,_,_,a,_⟩ := D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  have hh := constrained_normalized_simple_order_dvd hc hn
    (Group.IsPerfect.not_isSolvable BinaryLinearThree.Group) q
    (a.surjective.comp (QuotientGroup.mk'_surjective _)) K hK hq hout
  rwa [Matrix.PSL3Two.card_SL] at hh

/-- The full star image retains the original order-168 section. -/
theorem sourceOrbit_binary_witness_constrained_star_order_dvd
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    168 ∣ Nat.card (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)) := by
  have hh := D.sourceOrbit_binary_witness_constrained_core_order_dvd
    h hd F hF hmodel hw hWJ hJC K hK hq hout
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  rw [Nat.card_congr (hc.constrained_star_central_equiv K hK hq hout hfK).toEquiv] at hh
  exact hh.trans (card_quotient_dvd_card _)

/-- Neither A5 nor A6 is the literal star image. -/
theorem sourceOrbit_binary_witness_constrained_not_small_alternating
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) (n : ℕ) (hn : n = 5 ∨ n = 6) :
    ¬ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  have hh := D.sourceOrbit_binary_witness_constrained_star_order_dvd
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK
  rw [Nat.card_congr e.toEquiv] at hh
  rcases hn with rfl | rfl <;>
    rw [nat_card_alternatingGroup] at hh <;> norm_num [Nat.factorial] at hh

/-- The cubic center is included when excluding the triple-six star row. -/
theorem sourceOrbit_binary_witness_constrained_not_triple_six
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
    ¬ (Nonempty (center C ≃* Multiplicative (ZMod 3)) ∧
      Nonempty ((C ⧸ center C) ≃* alternatingGroup (Fin 6))) := by
  dsimp only
  rintro ⟨⟨ec⟩,⟨eq⟩⟩
  let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
  have hc : Nat.card (center C) = 3 := by
    rw [Nat.card_congr ec.toEquiv]
    exact Nat.card_zmod 3
  have hqcard : Nat.card (C ⧸ center C) = 360 := by
    rw [Nat.card_congr eq.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcard : Nat.card C = 1080 := by
    have hh := (center C).card_mul_index
    rw [hc,index_eq_card,hqcard] at hh
    omega
  have hh := D.sourceOrbit_binary_witness_constrained_star_order_dvd
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK
  change 168 ∣ Nat.card C at hh
  rw [hcard] at hh
  norm_num at hh

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
