module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryThompsonRelativePlanes
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCubicFactors

/-!
# Actual Thompson Fitting factors on the doubled orbit

The genuine SQTK cover bounds the B.1.9 cubic family by two. Its original
symmetric-three factors are normalized by the actual local two-residual.
The previously proved paired-plane supplement then puts their full preimages,
and the full preimage of their cubic product, in M. This retains the entire
source orbit and includes the original centralizer kernel.

This completes extraction and containment of the moved Fitting factors.
The comparison with the full three-core, quotient-component exclusions and
final ambient containment remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of 7.7.3, printed p.707, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryOmega
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every actual B.1.9 symmetric factor, and their odd product, have full
preimages in the original normalizer on the chosen doubled orbit. -/
theorem sourceOrbit_binary_pairedPlane_thompson_fitting_factors
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          HasMarking D.sourceOrbit L E ∧
          let U := ambientPlane D.sourceOrbit E v f
          let B := localBase L (T : Subgroup G) U
          let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype = R) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar B (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧ U ≤ H.pCoreIn 2 ∧
              IsSQTK KnownSimple.IsKnownSimple H ∧
              (∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = R) ∧
              H.pCoreIn 2 < (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
              H = elementaryAbelianMaxJ H ⊔ B ∧
              H ⊓ normalizer (L : Set G) ∈ Chapter1.He G ∧
              HasCharacteristicTwo H ∧ generalizedFitting H = pCore 2 H ∧
              Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple H
                ((L ⊔ (T : Subgroup G)).pCoreIn 2) (H ⊓ normalizer (L : Set G)) ∧
              let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
              D.sourceOrbit ≤ Y ∧ ∃ hred : IsPReduced 2 (Y.subgroupOf H),
              centralizer (Y : Set G) ≤ normalizer (L : Set G) ∧
              ¬ elementaryAbelianMaxJ H ≤ centralizer (Y : Set G) ∧
              inducedAutomizer Y (elementaryAbelianMaxJ H) ≠ ⊥ ∧
              DoubledBinaryThompson.ReducedThompsonAlternative (Y.subgroupOf H) hred ∧
              ¬ DoubledBinaryThompsonPlanes.ReducedSymmetricThree (Y.subgroupOf H) hred ∧
              DoubledBinaryThompsonRelativePlanes.RelativePlaneFactorsContained (Y.subgroupOf H) hred
                ((localResidual L U).subgroupOf H)
                ((normalizer (L : Set G)).subgroupOf H) ∧
              let := hred.normal
              let := hred.elementary
              let J := DoubledBinaryThompson.thompsonImage (Y.subgroupOf H)
              let q := ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H)
              let σ := DoubledBinaryThompson.thompsonAction (Y.subgroupOf H)
              (((ChapterB.FittingStructure.planeGenerated σ).map J.subtype).comap q).map
                H.subtype ≤ normalizer (L : Set G) ∧
              (((ChapterB.FittingStructure.fittingMoved σ).map J.subtype).comap q).map
                H.subtype ≤ normalizer (L : Set G)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_small_orbit_plane_factors h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let M := normalizer (L : Set G)
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,?_⟩
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ,⟨P,hP⟩,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,_⟩ := hescape hout
  refine ⟨H,hH,hHC,hUH,hSQ,⟨P,hP⟩,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,?_⟩
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  have hBH : B ≤ H := hH.1.1.2
  have hRH : R ≤ H := le_sup_right.trans hBH
  have hYH : Y ≤ H := conjugateSpanBy_le_self (by
    intro z hz
    exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hL0H : localResidual L U ≤ H := le_sup_left.trans hBH
  have hR' : IsPPerfect 2 ((localResidual L U).subgroupOf H) :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G))).of_surjective
      (subgroupOfEquivOfLe hL0H).symm.toMonoidHom (subgroupOfEquivOfLe hL0H).symm.surjective
  have hkernel : centralizer (Y.subgroupOf H : Set H) ≤ M.subgroupOf H := by
    intro a ha
    apply hcent
    intro y hy
    exact congrArg Subtype.val (ha ⟨y,hYH hy⟩ hy)
  let := hred.normal
  let := hred.elementary
  exact ⟨map_le_iff_le_comap.mpr
    (DoubledBinaryCubicFactors.thompson_planeGenerated_preimage_contained
      (Y.subgroupOf H) hred ((localResidual L U).subgroupOf H) (M.subgroupOf H)
      hSQ hR' hplanes hkernel),
    map_le_iff_le_comap.mpr
    (DoubledBinaryCubicFactors.thompson_fittingMoved_preimage_contained
      (Y.subgroupOf H) hred ((localResidual L U).subgroupOf H) (M.subgroupOf H)
      hSQ hR' hplanes hkernel)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
