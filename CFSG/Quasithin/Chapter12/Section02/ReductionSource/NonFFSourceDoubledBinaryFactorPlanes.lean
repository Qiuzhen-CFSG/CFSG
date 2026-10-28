module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryOuterThreeCore
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFactorPlanes

/-!
# The two-factor quotient escape on the original doubled orbit

A symmetric-three factor in the nonsolvable actual Thompson image is
characteristic, since its two source factors can only be preserved or
interchanged. Its cubic moves a plane in the original reduced orbit: odd
averaging makes passage to the fixed quotient injective on that moved
space. The original residual-plane argument contains the full cubic
preimage in M. The other factors have their two-residuals inside actual
ordinary components, so the two-factor row forces a quotient-component
preimage to escape. Quasisimple generalized Fitting absorbs its three-core,
so only the hyperplane alternative can still contribute an odd-core escape.

This retains the original full orbit, Sylow subgroup, kernel and source
markings. Quotient-component lifting and exclusion, the remaining odd-core
cases, ambient containment and final non-FF assembly remain with
qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of Proposition 7.7.3, printed p.707;
B.5.6(3), printed p.105, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryOmega
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Only the hyperplane alternative can retain an odd-core escape; every
other adequate alternative forces an actual quotient-component escape. -/
theorem sourceOrbit_binary_pairedPlane_component_or_hyperplane_escape
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
              ¬ Group.IsSolvable J ∧
              ((Nonempty (ChapterB.SourceInduction.HyperplaneCase
                    (DoubledBinaryThompson.thompsonAction (Y.subgroupOf H))) ∧
                  ¬ (((pCore 3 J).map J.subtype).comap q).map H.subtype ≤ normalizer (L : Set G)) ∨
                ∃ K : Subgroup J, IsComponent J K ∧
                  IsComponent (ChapterB.InternalThompsonAction.ActionQuotient (Y.subgroupOf H))
                    (K.map J.subtype) ∧
                  ¬ ((K.map J.subtype).comap q).map H.subtype ≤ normalizer (L : Set G))) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_thompson_escape_without_outer_core h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let M := normalizer (L : Set G)
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,?_⟩
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ,⟨P,hP⟩,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,hnsol,hchoice⟩ := hescape hout
  refine ⟨H,hH,hHC,hUH,hSQ,⟨P,hP⟩,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,hnsol,?_⟩
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  let := hred.normal
  let := hred.elementary
  by_cases hd' : Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase
      (DoubledBinaryThompson.thompsonAction (Y.subgroupOf H)))
  ·
    have hBM : B ≤ M := hbase.trans_le (inf_le_left.trans
      (sup_le L.le_normalizer D.sylow_normalizes_component))
    have hJM : ¬ elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ M.subgroupOf H := by
      intro hj
      have hh := map_mono (f := H.subtype) hj
      rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
        ← MonoidHom.range_eq_map,range_subtype] at hh
      have hJH : elementaryAbelianMaxJ H ≤ M :=
        hh.trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
      apply hH.1.2
      rw [hgen]
      exact sup_le hJH hBM
    have hPM : (P : Subgroup H) ≤ M.subgroupOf H :=
      map_le_iff_le_comap.mp (hP.trans_le (le_sup_right.trans hBM))
    have hRH : R ≤ H := le_sup_right.trans hH.1.1.2
    have hYH : Y ≤ H := conjugateSpanBy_le_self (by
      intro z hz
      exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    have hkernel : centralizer (Y.subgroupOf H : Set H) ≤ M.subgroupOf H := by
      intro a ha
      apply hcent
      intro y hy
      exact congrArg Subtype.val (ha ⟨y,hYH hy⟩ hy)
    obtain ⟨K,hK,hKA,hKM⟩ := DoubledBinaryFactorPlanes.twoFactor_thompson_component_escape
      (Y.subgroupOf H) hred P ((localResidual L U).subgroupOf H) (M.subgroupOf H)
      hSQ hplanes hPM hkernel hJM hnsol hd'
    exact Or.inr ⟨K,hK,hKA,fun he => hKM (map_le_iff_le_comap.mp he)⟩
  · rcases hchoice with ⟨h3,ho⟩ | hK
    · let J := DoubledBinaryThompson.thompsonImage (Y.subgroupOf H)
      let q := ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H)
      change ChapterB.SourceInduction.NontrivialAdequateAlternative
        (DoubledBinaryThompson.thompsonAction (Y.subgroupOf H)) at hclass
      cases hclass with
      | quasisimple hq _ =>
        let K := generalizedFitting J
        have hK : IsComponent J K :=
          ⟨(inferInstance : K.Normal).isSubnormal,hq⟩
        let : (elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic :=
          elementaryAbelianMaxJ_top_characteristic
        let : J.Normal :=
          (inferInstance : (elementaryAbelianMaxJ (⊤ : Subgroup H)).Normal).map q
            (QuotientGroup.mk'_surjective _)
        let : IsQuasisimple K := hq
        have hKA : IsComponent (ChapterB.InternalThompsonAction.ActionQuotient (Y.subgroupOf H))
            (K.map J.subtype) := ⟨hK.1.trans' (inferInstance : J.Normal).isSubnormal,
              IsQuasisimple.of_mulEquiv (K.equivMapOfInjective J.subtype J.subtype_injective)⟩
        refine Or.inr ⟨K,hK,hKA,?_⟩
        intro hKM
        apply h3
        have h3K : pCore 3 J ≤ K := (pCore_le_fitting J 3).trans (fitting_le_generalizedFitting J)
        exact (map_mono (comap_mono (map_mono h3K))).trans hKM
      | symmetricThree c => exact (hnot ⟨c⟩).elim
      | twoFactors c => exact (hd' ⟨c⟩).elim
      | outerSixThree c => exact (ho ⟨c⟩).elim
      | hyperplane c => exact Or.inl ⟨⟨c⟩,h3⟩
    · exact Or.inr hK

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
