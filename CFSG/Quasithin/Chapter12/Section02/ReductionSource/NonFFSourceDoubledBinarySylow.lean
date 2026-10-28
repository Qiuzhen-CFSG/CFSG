module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryResidualCore

/-!
# Sylow placement and minimal escape on the original binary doubled orbit

Non-FF forces J(T) into Q. Thompson heredity and the original local
uniqueness then control its full ambient normalizer. A paired plane can
therefore be chosen with T₀=C_T(U) Sylow in C_G(U), retaining the original
seed axes and conjugator. On this plane C_{LT}(U)=L₀T₀ and O₂(L₀T₀)=Q.

If its centralizer escapes M, the original minimal escaping SQTK group H
has T₀ Sylow, O₂(H)<Q, H=J(H)L₀T₀, and H∩M of characteristic two.
These prove 7.7.6(1–2) and its local preparation. Proving characteristic
two for H itself, the ambient containment, and final non-FF assembly
remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith 3.2.10(1,8), 7.7.2–6, printed pp.583,704–705.
-/

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore DoubledBinarySylow
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The genuine non-FF source hypotheses control J(T) and every two-overgroup
of it; all normalizers are in the original ambient group. -/
theorem sourceOrbit_nonFF_thompson_normalizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
      ∀ R : Subgroup G, IsPGroup 2 R → elementaryAbelianMaxJ (T : Subgroup G) ≤ R →
        elementaryAbelianMaxJ R = elementaryAbelianMaxJ (T : Subgroup G) ∧
        normalizer (R : Set G) ≤ normalizer (L : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQC : Q = (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) := by
    simpa only [D.sourceOrbit_eq] using (D.doubledOrbit_sylow_centralizer h).symm
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q := by
    rw [hQC]
    exact le_inf (sSup_le fun _ hA => hA.1) (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
  have hQT : Q ≤ (T : Subgroup G) := hQC.trans_le inf_le_left
  have he := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) Q hJQ hQT
  have hQne : Q ≠ ⊥ := by
    intro hz
    exact D.sourceOrbit_weakClosure_setup.nontrivial
      (le_bot_iff.mp (hz ▸ (D.sourceOrbit_core_normalizer h).1))
  have hnQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hNJ : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := by
    rw [← he]
    exact D.normal_subgroup_normalizer_le h.toHypothesis1221
      ((show elementaryAbelianMaxJ Q ≤ Q from sSup_le fun _ hA => hA.1).trans (pCoreIn_le 2 _))
      (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (isPGroup_pCoreIn 2 _) hQne)
      (hnQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q))
  refine ⟨hNJ,?_⟩
  intro R hp hJR
  have heR := thompson_eq_of_overgroup T R hp hJR
  exact ⟨heR,(normalizer_le_normalizer_elementaryAbelianMaxJ R).trans (heR.symm ▸ hNJ)⟩

/-- The source plane with its actual Sylow placement and original local base;
minimal escape gives the strict two-core bound, Thompson generation and the
characteristic-two intersection with M. -/
theorem sourceOrbit_binary_pairedPlane_sylow_escape
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
              H ⊓ normalizer (L : Set G) ∈ Chapter1.He G) := by
  obtain ⟨t,ht,hnt,q,hq,E,a,hE,ha,_,hcov,hV,hVt⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hMW : M ≤ normalizer (D.sourceOrbit : Set G) :=
    (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge
  have hJ := D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon
  have hNJ := (D.sourceOrbit_nonFF_thompson_normalizers h hnon).1
  obtain ⟨v,f,hfv,S,hS⟩ := exists_pairedPlane_sylow D.sourceOrbit M T hTM hMW hJ hNJ E a hcov
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hcore : B.pCoreIn 2 = Q := pairedPlane_localBase_core D.sourceOrbit L T
    D.sylow_normalizes_component D.sourceOrbit_component_normalizes
    D.sourceOrbit_weakClosure_setup.normalizes hQ q hq E hE a ha hcov v f hfv
  have hbase : B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) :=
    localBase_eq_centralizer L U T D.sylow_normalizes_component S hS
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,⟨S,hS⟩,hbase,hcore,?_⟩
  intro hout
  have hUW : U ≤ D.sourceOrbit := ambientPlane_le_orbit D.sourceOrbit E v f
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
  have hU : U ≠ ⊥ := by
    intro hz
    have hc := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hc
    rw [hz,Subgroup.card_bot] at hc
    omega
  have hUC : U ≤ centralizer (U : Set G) :=
    (hUW.trans (le_centralizer D.sourceOrbit)).trans (centralizer_le hUW)
  have hUB : U ≤ B :=
    (le_inf (hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow) hUC).trans le_sup_right
  have hBC : B ≤ centralizer (U : Set G) := hbase.trans_le inf_le_right
  obtain ⟨H,hH,hHC,hUH,hSQ⟩ := minimal_escape h.simpleQTKE U B M hp hU hUB hBC hout
  have hBH : B ≤ H := hH.1.1.2
  have hRH : R ≤ H := (show R ≤ B from le_sup_right).trans hBH
  obtain ⟨P,hP⟩ := sylow_between hHC S (hS.trans_le hRH)
  have hPR : (P : Subgroup H).map H.subtype = R := hP.trans hS
  have hHQ : H.pCoreIn 2 ≤ Q :=
    (core_le_of_sylow_base P (hPR.trans_le le_sup_right) hBH).trans_eq hcore
  have hHQne : H.pCoreIn 2 ≠ Q := by
    intro heq
    apply hH.1.2
    apply le_trans _ (D.sourceOrbit_core_normalizer h).2
    change H ≤ normalizer (Q : Set G)
    rw [← heq]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ R :=
    le_inf (sSup_le fun _ hA => hA.1) (hJ.trans (centralizer_le hUW))
  have hgen : H = elementaryAbelianMaxJ H ⊔ B := minimal_escape_generation T U B M H
    hH hHC hp hU hUB P (hPR.trans_le inf_le_left) (hPR.symm ▸ hJR) hNJ
  have hQM : Q ≤ M := (pCoreIn_le 2 _).trans (sup_le L.le_normalizer hTM)
  have hQH : Q ≤ H := by
    rw [← hQ]
    exact (inf_le_inf_left _ (centralizer_le hUW)).trans hRH
  have hMQ : M.pCoreIn 2 ≤ Q := core_le_of_sylow_base (T.subtype hTM)
    (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]; exact le_sup_right)
    (sup_le L.le_normalizer hTM)
  have hMHne : H ⊓ M ≠ ⊥ := by
    intro hz
    have hUM : U ≤ M := (hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow).trans hTM
    exact hU (le_bot_iff.mp (hz ▸ le_inf (hUB.trans hBH) hUM))
  have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  have hMH : H ⊓ M ∈ Chapter1.He G := Chapter1.lemma_1_1_4_5 T
    (h.simpleQTKE.evenCharacteristic T) h61.maximalTwoLocal hTM hMHne inf_le_right
    (inf_le_left.trans (le_inf (hMQ.trans hQH) (pCoreIn_le 2 M)))
  exact ⟨H,hH,hHC,hUH,hSQ,⟨P,hPR⟩,lt_of_le_of_ne hHQ hHQne,hgen,hMH⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
