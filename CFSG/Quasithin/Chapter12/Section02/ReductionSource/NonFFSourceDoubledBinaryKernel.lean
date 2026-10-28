module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryQuotientComponents
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryKernel
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoreAction

/-!
# Quasisimplicity of the original lifted component and the full-core alternatives

For the actual paired plane, C_{T₀}(Y) is the intersection of the normal
local core Q with C_H(Y): the original doubled orbit W lies in Y, and
C_T(W)=Q. Thus the local base normalizes this Sylow subgroup of the full
action kernel. The nontrivial paired plane lies in it. Minimal escape and
Frattini factorization prove that the kernel is two-closed, which gives
quasisimplicity of the lifted component modulo its own two-core.

The same component now satisfies the genuine C.2.4 dichotomy for the full
original Q. Its moving alternative is a chi-zero block with the specified
Sylow equal to Q intersect C. The quotient component, full preimage, lift,
and full kernel remain distinct; W remains the whole doubled orbit.
The moving-block exclusion, Q normalization, ambient plane containment,
and final non-FF assembly remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of Proposition 7.7.3 and 7.7.7–8,
printed p.707, refs/quasithin.pdf.
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

/-- The original lifted C-component has a quasisimple intrinsic two-core
quotient. The full action kernel is two-closed, and the original Q either
normalizes this lift or meets a chi-zero block in its full Sylow subgroup. -/
theorem sourceOrbit_binary_pairedPlane_quasisimple_lift
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
                  ¬ ((K.map J.subtype).comap q).map H.subtype ≤ normalizer (L : Set G) ∧
                  ∃ C : Subgroup H, C.IsCComponent ∧ C.map q = K.map J.subtype ∧
                    C ⊔ q.ker = (K.map J.subtype).comap q ∧
                    ¬ C.map H.subtype ≤ normalizer (L : Set G) ∧
                    (localResidual L U).subgroupOf H ≤ normalizer (C : Set H) ∧
                    (C.Normal ∨ (normalizer (C : Set H)).index = 2) ∧
                    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = R ∧
                      (conjugateSpanBy C (P : Subgroup H)).Normal ∧
                      H = (conjugateSpanBy C (P : Subgroup H)).map H.subtype ⊔ B ∧
                      (∃ S : Sylow 2 (centralizer (Y.subgroupOf H : Set H)),
                        (S : Subgroup (centralizer (Y.subgroupOf H : Set H))).Normal) ∧
                      IsQuasisimple (C ⧸ pCore 2 C) ∧
                      generalizedFitting C = pCore 2 C ∧
                      (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf H ≤
                          normalizer (C : Set H) ∨
                        (ChapterC.IsChiZeroBlock C ∧ ∃ S : Sylow 2 C,
                          (S : Subgroup C).map C.subtype =
                            ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf H ⊓ C))) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_lifted_component_escape h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,?_⟩
  intro hout
  obtain ⟨H,hH,hHC,hUH,hSQ,hSyl,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,hnsol,hchoice⟩ := hescape hout
  refine ⟨H,hH,hHC,hUH,hSQ,hSyl,hlt,hgen,hMH,hchar,hgf,hpush,
    hWY,hred,hcent,hJ,hJne,hclass,hnot,hplanes,hnsol,?_⟩
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  let := hred.normal
  let := hred.elementary
  let N := centralizer (Y.subgroupOf H : Set H)
  let J := DoubledBinaryThompson.thompsonImage (Y.subgroupOf H)
  let q := ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H)
  obtain ⟨K,hK,hKA,hKM,C,hC,he,hpre,hCM,hLC,horbit,P,hP,hnormal,hgenerate⟩ := hchoice
  refine ⟨K,hK,hKA,hKM,C,hC,he,hpre,hCM,hLC,horbit,P,hP,hnormal,hgenerate,?_⟩
  have hRH : R ≤ H := le_sup_right.trans hH.1.1.2
  have hYH : Y ≤ H := conjugateSpanBy_le_self (by
    intro z hz
    exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hNH : N.map H.subtype = H ⊓ centralizer (Y : Set G) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      refine ⟨a.property,?_⟩
      intro y hy
      exact congrArg Subtype.val (ha ⟨y,hYH hy⟩ hy)
    · rintro ⟨hx,hc⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      intro y hy
      exact Subtype.ext (hc y hy)
  have hNM : N.map H.subtype ≤ M := by rw [hNH]; exact inf_le_right.trans hcent
  have hQB : Q ≤ B := hcore.symm.le.trans (pCoreIn_le 2 B)
  have hQR : Q ≤ R := by
    have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
      simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
    rw [←hQ]
    exact inf_le_inf_left _ (centralizer_le (ambientPlane_le_orbit D.sourceOrbit E v f))
  have hBQ : B ≤ normalizer (Q : Set G) := by
    change B ≤ normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)
    rw [←hcore]
    exact B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hinter : ((P : Subgroup H) ⊓ N).map H.subtype ≤ Q := by
    rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective,hP,hNH]
    have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
      simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
    rw [←hQ]
    exact le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans (inf_le_right.trans (centralizer_le hWY)))
  have hUW : U ≤ D.sourceOrbit := ambientPlane_le_orbit D.sourceOrbit E v f
  have hU : U ≠ ⊥ := by
    intro hz
    have hc := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hc
    rw [hz,Subgroup.card_bot] at hc
    omega
  have hUP : U ≤ (P : Subgroup H).map H.subtype := by
    rw [hP]
    exact le_inf (hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow)
      (hUW.trans ((le_centralizer D.sourceOrbit).trans (centralizer_le hUW)))
  have hUN : U ≤ N.map H.subtype := by
    rw [hNH]
    exact le_inf (hUW.trans (hWY.trans hYH)) (le_centralizer_iff.mp (hYH.trans hHC))
  have hclosed := DoubledBinaryKernel.kernel_twoClosed_of_original_core H B M Q U hH N P
    hNM (hP.symm ▸ hQR) hBQ hinter hU hUP hUN
  refine ⟨hclosed,?_⟩
  have hquasi := DoubledBinaryKernel.lifted_component_twoCore_quasisimple hSQ N C hclosed
    hred.quotient_pCore_eq_bot hC (he.symm ▸ hKA)
  let := hquasi
  refine ⟨hquasi,?_⟩
  exact DoubledBinaryCoreAction.original_core_component_alternative hpush hchar hgf C hC
    (fun hh => hCM (map_le_iff_le_comap.mpr (hh.trans (comap_mono inf_le_right))))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
