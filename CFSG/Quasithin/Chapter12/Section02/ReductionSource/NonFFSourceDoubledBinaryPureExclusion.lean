module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureG2Exclusion
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureTrialityExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPureCartan

/-!
# Closing the selected pure-line H1 obstruction

The original non-FF binary orbit with w ≤ 1 yields a minimal centralizer overgroup failing
characteristic two and its actual component. The pure-line Cartan
reduction leaves only G₂ and triality. Their three-rank forces the same component
to be normal in that overgroup, so the original orbit core acts on it. The scalar
exclusions then contradict the pure-line image bound. All hypotheses of these
exclusions are supplied by the original chosen module, including the Sylow
placement, central quotient, faithful sixteen and both marked axes.

This closes the selected-line H1 construction, not the full doubled branch:
the source 4.4.3 argument supplying w ≤ 1 remains to be proved.
Source: Aschbacher–Smith 7.7.3 H1 argument and 7.7.4, printed pp.704–706.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter7 ChapterE BinaryLinearThree
open Stellmacher DoubledBinaryLocalCore DoubledBinaryPlanes
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual selected pure-line component is impossible. No component,
root, multiplier, Sylow-placement or exclusion callback remains. -/
theorem sourceOrbit_binary_false_of_globalW_le_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) (hw : globalW D.sourceOrbit T ≤ 1) : False := by
  obtain ⟨g,hg,t,ht,hnt,hZ,hpure,hpair,hcentral,hPC,hoddC,
    H,hBH,hHC,hNH,hmin,hSQ,hMH,hoddH,hcore,hPH,K,hK,hKM,hgen,hsmall,
    E,hV,hVt,hmark,hno,hsing,v,f,hfv,hZU,hdis,hcard,hmove,hhyper,
    hnorm,hN,hcorank,hCM,hact,hAN,hker,hi,
    ⟨j,hj,hjact,hjcard,hje,P,hPactual,hAQ,hQN,hindex,hcyc,hzK,hjcent,hlarge,hout,
      hPjoin,hQ,hPQ,hS⟩,hrank,n,hn,hmodelK⟩ :=
    D.sourceOrbit_binary_exists_pureLine_component_cartan_reduction h hd F hF hmodel hnon hw
  let W₀ := D.sourceOrbit
  let Z := ⁅offenderNormalizer W₀ g,offenderFixedSpan W₀ g⁆
  let C := centralizer (Z : Set G)
  let Q₀ := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := ambientPlane W₀ E v f
  let A := ⁅W₀,localResidual L U⁆
  let := hK.quasisimple
  have hZW : Z ≤ W₀ := hpair.trans inf_le_left
  have hAW : A ≤ W₀ := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans hmark.1))
  have hQW : (T : Subgroup G) ⊓ centralizer (W₀ : Set G) = Q₀ := by
    simpa only [W₀,Q₀,D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hQH : Q₀ ≤ H := by
    rw [←hQW]
    exact (inf_le_inf_left _ (centralizer_le hZW)).trans (le_sup_right.trans hBH)
  have hQC : Q₀ ≤ centralizer (W₀ : Set G) := by rw [←hQW]; exact inf_le_right
  have hZne : Z ≠ ⊥ := by
    intro he
    have hh : Nat.card Z = 2 := hZ
    rw [he,card_bot] at hh
    omega
  have hpoint := D.sourceOrbit_binary_pureLine_image_card_dvd h hd F hF hmodel
    t ht Z hZne hpure
  have hNW : normalizer (Q₀ : Set G) ≤ normalizer (W₀ : Set G) := by
    rw [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
    exact (D.sourceOrbit_core_normalizer h).2
  rcases hmodelK with hm | hm
  · have hn4 := DoubledBinaryG2Placement.g2_degree_ge_four hn hm _ j.range hjcard hAQ hindex
    have hnK := DoubledBinaryG2Placement.g2_component_normal H K hK hSQ.stronglyQuasithin hn4 hm
    have hQN : Q₀ ≤ normalizer (K : Set G) :=
      hQH.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hnK)
    exact DoubledBinaryPureG2Exclusion.g2_exclusion W₀ Z K A Q₀ hAW
      (hK.1.trans hHC) hAN hQN hQC (isPGroup_pCoreIn 2 _) hNW hpoint
      j hjcard hjact P hPQ hAQ hindex hn hm
  · have hnK := DoubledBinaryTrialityPlacement.triality_component_normal H K hK
      (hSQ.stronglyQuasithin 3 Nat.prime_three (by decide)) hzK hn hm
    have hQN : Q₀ ≤ normalizer (K : Set G) :=
      hQH.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hnK)
    exact DoubledBinaryPureTrialityExclusion.triality_exclusion W₀ Z K A Q₀ hAW
      (hK.1.trans hHC) hAN hQN hQC (isPGroup_pCoreIn 2 _) hNW hpoint
      j hjcard hjact P hPQ hAQ hindex hzK hn hm

/-- Any surviving original non-FF binary doubled orbit must have w > 1. -/
theorem sourceOrbit_binary_one_lt_globalW
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    (hnon : D.SourceOrbitNonFF) : 1 < globalW D.sourceOrbit T := by
  exact lt_of_not_ge (D.sourceOrbit_binary_false_of_globalW_le_one h hd F hF hmodel hnon)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
