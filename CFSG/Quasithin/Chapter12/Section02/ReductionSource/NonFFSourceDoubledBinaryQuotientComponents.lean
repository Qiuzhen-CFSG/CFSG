module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryHyperplane
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryQuotientComponents
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The lifted component and its original Sylow orbit

An escaping ordinary component of the actual Thompson centralizer quotient
lifts to a C-component of the minimal escaping H. The source SQTK generation
argument uses its full preimage; no solvability of the kernel is assumed.
The original two-perfect residual normalizes the lift, and the source
component orbit bound makes its orbit under the original Sylow normal.
Minimality of H, using the same nontrivial central plane, gives generation
by that orbit and the original local base.

The quotient component, its full preimage, and the lifted C-component are
kept separate. The lift's two-core quotient still needs to be proved
quasisimple before applying the subsequent C.2 exclusions. Those exclusions,
ambient plane containment and final assembly remain with
qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of Proposition 7.7.3 immediately before
Lemma 7.7.7, printed p.707, refs/quasithin.pdf.
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

/-- The original escaping quotient component lifts to an escaping C-component
normalized by the original residual. Its Sylow orbit is normal and, with
the original local base, generates the minimal escaping group. -/
theorem sourceOrbit_binary_pairedPlane_lifted_component_escape
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
                      H = (conjugateSpanBy C (P : Subgroup H)).map H.subtype ⊔ B) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_quotient_component_escape h hd hnon F hF hmodel
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
  obtain ⟨K,hK,hKA,hKM⟩ := hchoice
  refine ⟨K,hK,hKA,hKM,?_⟩
  let J := DoubledBinaryThompson.thompsonImage (Y.subgroupOf H)
  let q := ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H)
  have hRH : R ≤ H := le_sup_right.trans hH.1.1.2
  have hYH : Y ≤ H := conjugateSpanBy_le_self (by
    intro z hz
    exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hkernel : q.ker ≤ M.subgroupOf H := by
    dsimp only [q,ChapterB.InternalThompsonAction.actionMk]
    rw [QuotientGroup.ker_mk']
    intro a ha
    apply hcent
    intro y hy
    exact congrArg Subtype.val (ha ⟨y,hYH hy⟩ hy)
  have hLH : localResidual L U ≤ H := le_sup_left.trans hH.1.1.2
  have hLperf : IsPPerfect 2 ((localResidual L U).subgroupOf H) :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G))).of_surjective
      (subgroupOfEquivOfLe hLH).symm.toMonoidHom (subgroupOfEquivOfLe hLH).symm.surjective
  obtain ⟨C,hC,he,hpre,hCM,hLC,horbit⟩ :=
    DoubledBinaryQuotientComponents.escaping_quotient_component_lift_normalized
      hSQ q (QuotientGroup.mk'_surjective _) (M.subgroupOf H)
      ((localResidual L U).subgroupOf H) hLperf hkernel (K.map J.subtype) hKA
      (fun hh => hKM (map_le_iff_le_comap.mpr hh))
  have hCM' : ¬ C.map H.subtype ≤ M := fun hh => hCM (map_le_iff_le_comap.mp hh)
  have hnormal := conjugateSpanBy_sylow_normal C P horbit
  refine ⟨C,hC,he,hpre,hCM',hLC,horbit,P,hP,hnormal,?_⟩
  let C₀ := (conjugateSpanBy C (P : Subgroup H)).map H.subtype
  let X := C₀ ⊔ B
  have hXH : X ≤ H := sup_le (map_subtype_le _) hH.1.1.2
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
  have hUX : U ≤ X := hUB.trans le_sup_right
  have hcoreX : U ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes hp hUX
    ((hXH.trans hHC).trans (Subgroup.centralizer_le_normalizer _))
  apply le_antisymm _ hXH
  apply hH.2 ?_ hXH
  refine ⟨⟨?_,fun x hx => (le_sup_right : B ≤ X) hx⟩,?_⟩
  · intro hz
    exact hU (le_bot_iff.mp (hz ▸ hcoreX))
  · intro hXM
    exact hCM' ((map_mono (le_conjugateSpanBy C (P : Subgroup H))).trans
      (le_sup_left.trans hXM))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
