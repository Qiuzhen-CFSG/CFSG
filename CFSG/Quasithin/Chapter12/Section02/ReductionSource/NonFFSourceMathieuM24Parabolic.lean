module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Source
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuQuadratic
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceLocalSetup
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The genuine E.2.8 setup on the original M24 parabolics

Both M24 code and cocode have strict quadratic ratio greater than two.
Containment of the original orbit in an outside H-star two-core would give
ratio at most two by the reduced-join qrc theorem, including its dual-FF
alternative. The faithful quotient factorization preserves the original
conjugation action and contradicts that strict bound.

The nonzero Sylow-fixed part of the orbit lies in the Sylow omega-center.
Every original H-star group centralizes it; TI therefore makes H intersect
N_G(L) normalize the orbit. The intrinsic two-core/normal-core intersection
identity now supplies every hypothesis of E.2.8 on the same H. Applying this
to the already constructed fixed-three-space supplement also proves that
its chosen H is nonsolvable, since its generation parameter is two.

This removes the noncontainment and local-setup premises of canonical pair
selection. It does not place the displayed conjugate module in that H:
the E.2.9 pair must still be selected there, with all its source markings.
That selection, component recognition, remaining Mathieu rows and the final
ambient J4 isomorphism remain with qt-d-1222-nonff-mathieu.
The private import continues the original orbit coordinate formula only.
Source: Aschbacher--Smith 3.1.8(2), E.2.8 and 8.2.2(1), printed
pp.576,221,714--715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open Sporadic.Mathieu
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Both M24 module rows escape every original outside H-star two-core. -/
theorem sourceOrbit_m24_not_le_HStar_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ D.sourceOrbit ≤ H.pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let M := normalizer (L : Set G)
  let Q := ReducedNormal.intrinsicSubspace J D.orbitSpace
  have hW : (⊤ : Subgroup J) ≤ subspaceStabilizer (ReducedNormal.representation J)
      D.orbitSpace := orbitSpan_invariant _ ⊤ D.space
  have hr : IsPReduced 2 Q := by
    change IsPReduced 2 (ReducedNormal.intrinsicSubspace J D.orbitSpace)
    rw [ReducedNormal.intrinsicSubspace_eq]
    exact ReducedNormal.subspaceImage_isPReduced_of_action_core J D.orbitSpace hW
      (D.orbit_twoCore_eq_bot h.toHypothesis1221)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hj : J ≤ M := sup_le L.le_normalizer D.sylow_normalizes_component
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → J ≤ N → N = M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique
  have hn : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hc := Chapter3.qrcHypotheses_of_reduced_join T M L H
    h.maximal_faithful.2.1.2.1 L.le_normalizer hn hj hH Q hr
    (D.orbit_intrinsic_centralizer h.toHypothesis1221)
  change Chapter3.QrcHypotheses T M J H D.sourceOrbit at hc
  intro hcore
  have hbound : quadraticRatio
      (ChapterD.UniqueFactor.imageRepresentation J D.sourceOrbit hc.module_normalized) ≤ 2 := by
    rcases hc.quadraticRatio_le_two_or_dualFF h.simpleQTKE hm huniq
      D.sourceOrbit_weakClosure_setup.nontrivial hcore with hb | hd
    · exact hb
    · exact hc.quadraticRatio_le_two_of_dualFF h.simpleQTKE hm hd
  let σ := ChapterD.UniqueFactor.imageRepresentation J D.sourceOrbit hc.module_normalized
  let q := (ChapterD.UniqueFactor.actionHom J D.sourceOrbit hc.module_normalized).rangeRestrict
  have he (g : J) (w : Additive D.sourceOrbit) :
      D.sourceOrbitCoordinates.symm (σ (q g) w) =
        D.orbitRepresentation (D.orbitHom g) (D.sourceOrbitCoordinates.symm w) := by
    have hact (v : D.orbitSpace) :
        D.sourceOrbitCoordinates (D.orbitRepresentation (D.orbitHom g) v) =
          σ (q g) (D.sourceOrbitCoordinates v) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (D.sourceOrbitCoordinates_apply (D.orbitRepresentation (D.orbitHom g) v)).trans
        (congrArg (fun x : G => (g : G) * x * (g : G)⁻¹)
          (D.sourceOrbitCoordinates_apply v).symm)
    apply D.sourceOrbitCoordinates.injective
    simpa only [D.sourceOrbitCoordinates.apply_symm_apply] using
      (hact (D.sourceOrbitCoordinates.symm w)).symm
  obtain ⟨f,hfi,hf,_⟩ := faithful_action_factor σ D.orbitRepresentation
    (ChapterD.UniqueFactor.imageRepresentation_injective J D.sourceOrbit hc.module_normalized)
    (subspaceImageRepresentation_injective _ _)
    q (ChapterD.UniqueFactor.actionHom J D.sourceOrbit hc.module_normalized).rangeRestrict_surjective
    D.orbitHom D.sourceOrbitCoordinates.symm he
  have htransport := quadraticRatio_le_of_injective_equivariant σ D.orbitRepresentation
    f hfi D.sourceOrbitCoordinates.symm hf
  exact (not_le_of_gt (MathieuQuadratic.marked_quadraticRatio_gt_two D.orbitRepresentation
    (MathieuMarkings.m24_marking D.orbitRepresentation D.orbitComponent hs hq)))
      (htransport.trans hbound)


/-- The original M24 H-star subgroup satisfies E.2.8, including escape
from its actual normal core, and is of characteristic two. -/
theorem sourceOrbit_m24_hstar_setup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Chapter8.Section02.Offenders.Parabolic.Construction.HypothesisE28
      KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit ∧
        HasCharacteristicTwo H := by
  let Z := D.sourceOrbit ⊓ centralizer (T : Set G)
  have hZ : Z ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G)
    D.sourceOrbit T.isPGroup' (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
    D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_weakClosure_setup.nontrivial
  have hzOmega : Z ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    intro z hz
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨D.sourceOrbit_weakClosure_setup.le_sylow hz.1,
        elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz.1,hz.2⟩
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (D.sourceOrbit_hstar_centralizes_omega h.toHypothesis1221 hnon hH).trans
      (centralizer_le hzOmega)
  have hMV : H ⊓ normalizer (L : Set G) ≤ normalizer (D.sourceOrbit : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hHZ)).trans
      ((D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).localCentralizer_le_normalizer
        hZ (show Z ≤ D.sourceOrbit from inf_le_left))
  refine ⟨Chapter8.Section02.HermitianSource.hypothesisE28_of_HStar_outside_twoCore
    h.simpleQTKE T D.sylow_normalizes_component hH D.sourceOrbit_weakClosure_setup.le_sylow
    (normal_subgroupOf_of_le_normalizer D.sourceOrbit_weakClosure_setup.normalizes) hMV
    (D.sourceOrbit_m24_not_le_HStar_core h
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq hH), ?_⟩
  exact Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1.1)

/-- Apply the genuine E.2.8 setup inside the centralizer supplement of the
same original offender fixed space. All cover and two-core escape inputs
are discharged; selection of a pair within this H is the next source step. -/
theorem sourceOrbit_m24_fixedPlane_parabolic_of_offender
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] MathieuCode.Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      MathieuCode.cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    ∃ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧
      H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      generationParameter H = 2 ∧ ¬ Group.IsSolvable H ∧
      Chapter8.Section02.Offenders.Parabolic.Construction.HypothesisE28
        KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit ∧
      HasCharacteristicTwo H := by
  obtain ⟨_,_,_,_,_,_,H,hH,hHC,hHN,hr,hn⟩ :=
    D.sourceOrbit_m24_fixedPlane_local_of_offender_of_many h hmany hV hq hnon a E hE hg hAT
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_m24_hstar_setup h hmany hV hq hnon hH
  have hns : ¬ Group.IsSolvable H := by
    intro hsol
    let := hsol
    have hb := generationParameter_le_one_of_solvable (G := H)
    rw [hn] at hb
    omega
  exact ⟨H,hH,hHC,hHN,hr,hn,hns,h28,hchar⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
