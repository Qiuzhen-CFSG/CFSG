module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceLocalSetup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianNoncontainment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneOddControl
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneSetup
public import Theory.Representation.BinaryOffender.Ratio

/-!
# E.2.8 on the original Hermitian chosen orbit

Non-FF makes every original HStar subgroup centralize the Sylow
omega-center. The orbit has a nonzero Sylow fixed subgroup there, and TI
therefore makes H ∩ N_G(L) normalize the orbit. The checked Hermitian
noncontainment theorem and the normal-core intersection identity now give
E.2.8. Even characteristic gives characteristic two of the same H.

Non-FF also gives q > 1 on the literal restricted automizer. Consequently
positive weak closure and the earlier universal E.2 selection/model
clauses construct the selected pair without additional local premises.
Those universal clauses remain explicit. The tensor application in
NonFFSourceNonMathieuHermitianSourceSelection supplies positive weak
closure for n > 1; field four and source 8.2.13 remain open.
Source: Aschbacher–Smith, the introduction to Hypothesis 7.0.2 and
8.2.2, printed pp.695,714–715 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter8.Section02.Offenders.Parabolic.Construction
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  (D : ChosenModule T L V)

/-- TI and the fixed Sylow center normalize the original orbit under the
intersection with any actual H-star group. -/
theorem sourceOrbit_hstar_intersection_normalizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H ⊓ normalizer (L : Set G) ≤ normalizer (D.sourceOrbit : Set G) := by
  let Z := D.sourceOrbit ⊓ centralizer (T : Set G)
  have hZ : Z ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G)
    D.sourceOrbit T.isPGroup' (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
    D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_weakClosure_setup.nontrivial
  have hz := D.sourceOrbit_hstar_omega_le_center h hnon hH
  have hHZ : H ≤ centralizer (Z : Set G) := by
    apply le_centralizer_iff.mpr
    intro z hzZ x hx
    have hzOmega : z ∈ omegaOneCenterAmbient (T : Subgroup G) :=
      (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨D.sourceOrbit_weakClosure_setup.le_sylow hzZ.1,
          elemPow_eq_one_of_isElementaryAbelian (p := 2) z hzZ.1, hzZ.2⟩
    obtain ⟨a, ha, rfl⟩ := hz hzOmega
    exact congrArg H.subtype (mem_center_iff.mp ha ⟨x, hx⟩)
  exact (le_inf inf_le_right (inf_le_left.trans hHZ)).trans
    ((D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).localCentralizer_le_normalizer hZ (show Z ≤ D.sourceOrbit from inf_le_left))

/-- The complete E.2.8 local input on the original Hermitian orbit. -/
theorem sourceOrbit_hermitian_hstar_setup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    HypothesisE28 KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit ∧
      HasCharacteristicTwo H := by
  refine ⟨Chapter8.Section02.HermitianSource.hypothesisE28_of_HStar_outside_twoCore
    h.simpleQTKE T D.sylow_normalizes_component hH D.sourceOrbit_weakClosure_setup.le_sylow
    (normal_subgroupOf_of_le_normalizer D.sourceOrbit_weakClosure_setup.normalizes)
    (D.sourceOrbit_hstar_intersection_normalizes h hmany hV hnon hH)
    (D.sourceOrbit_hermitian_not_le_HStar_core h hs hrow hH), ?_⟩
  exact Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1.1)

/-- Non-FF for the original full automizer gives the strict quadratic ratio
needed by selection on its actual restricted image. -/
theorem sourceOrbit_restricted_quadraticRatio_gt_one
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (X : Subgroup G) :
    1 < quadraticRatio ((automizerRepresentation D.sourceOrbit).comp
      (inducedAutomizer D.sourceOrbit X).subtype) := by
  apply lt_of_not_ge
  intro hq
  have hff := isFFModule_of_quadraticRatio_le_one _ hq
  exact D.sourceOrbit_automizer_nonFF h hnon
    (IsFFModule.map_equivariant _ _ (inducedAutomizer D.sourceOrbit X).subtype
      Subtype.val_injective (LinearEquiv.refl _ _) (fun _ _ => rfl) hff)

/-- The actual H-star witness and local inputs reduce selection solely to
its earlier source clauses and the positive weak-closure parameter. -/
theorem sourceOrbit_hermitian_exists_selected_of_positive
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (earlier : SelectionSources (G := G) KnownSimple.IsKnownSimple)
    (models : SelectionModelSources)
    (hw : 0 < globalW D.sourceOrbit T) :
    ∃ (H I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      HypothesisE28 KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit ∧
      HasCharacteristicTwo H ∧
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S := by
  obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  obtain ⟨I,k,i,S,s⟩ := exists_selected earlier models h28
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar) hw
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  exact ⟨H,I,k,i,S,hH,h28,hchar,s⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
