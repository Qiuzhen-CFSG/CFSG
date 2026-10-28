module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryFactorPlanes
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryHyperplane

/-!
# An escaping quotient component on the original doubled orbit

The remaining hyperplane alternative has its full three-core preimage
inside M, by the original-module plane calculation. Combining this with
the previously checked alternatives removes the last odd-core branch.
Every escaping paired-plane centralizer now supplies an ordinary component
of its literal centralizer quotient whose full preimage escapes M.

The selected seed, full doubled orbit, reduced omega-center closure and
quotient kernel remain distinct. Lifting and excluding this component,
ambient containment and final assembly stay with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of Proposition 7.7.3, printed p.707,
refs/quasithin.pdf.
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

/-- Every escape from M yields an ordinary component of the literal
centralizer quotient whose full preimage escapes M. -/
theorem sourceOrbit_binary_pairedPlane_quotient_component_escape
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
              ∃ K : Subgroup J, IsComponent J K ∧
                  IsComponent (ChapterB.InternalThompsonAction.ActionQuotient (Y.subgroupOf H))
                    (K.map J.subtype) ∧
                  ¬ ((K.map J.subtype).comap q).map H.subtype ≤ normalizer (L : Set G)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_component_or_hyperplane_escape h hd hnon F hF hmodel
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
  rcases hchoice with ⟨hc,h3⟩ | hK
  · have hRH : R ≤ H := le_sup_right.trans hH.1.1.2
    have hYH : Y ≤ H := conjugateSpanBy_le_self (by
      intro z hz
      exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    have hkernel : centralizer (Y.subgroupOf H : Set H) ≤ M.subgroupOf H := by
      intro a ha
      apply hcent
      intro y hy
      exact congrArg Subtype.val (ha ⟨y,hYH hy⟩ hy)
    have hh := DoubledBinaryHyperplane.hyperplane_thompson_threeCore_preimage_contained
      (Y.subgroupOf H) hred ((localResidual L U).subgroupOf H) (M.subgroupOf H)
      hSQ hplanes hkernel hc
    exact (h3 (map_le_iff_le_comap.mpr hh)).elim
  · exact hK

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
