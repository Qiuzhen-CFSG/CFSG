module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryStarRadicals
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarSix

/-!
# Excluding the actual alternating-six star component

The original orbit lies in Q and in the reduced normal module Y. Hence it
lies in the canonical omega-center of the component join with Q. Its
residual four-space injects into the actual B.5 moved section modulo the
fixed space. In the A₆ case this quotient has dimension four, so Q fixes
all of it. Faithfulness then leaves a Sylow image of order at most two,
contradicting perfectness. Both original quotient kernels are retained;
no block recognition or vanishing-center premise is assumed.

Source: Aschbacher--Smith, the elimination after 7.7.10, printed p.709,
and C.2.7/B.5.1, printed pp.145--147 and99--103, refs/quasithin.pdf.
The other constrained components, ambient containment and doubled rows
remain with the original assembly.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryOmega
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual A₆ star quotient is excluded on the original chosen orbit,
with the component, marked intersection and earlier exclusions retained. -/
theorem sourceOrbit_binary_pairedPlane_six_star_exclusion
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
          let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
          localBase L (T : Subgroup G) U =
            (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          (localBase L (T : Subgroup G) U).pCoreIn 2 = Q ∧
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar (localBase L (T : Subgroup G) U) (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧
              let Y := conjugateSpanBy
                (omegaOneCenterAmbient ((T : Subgroup G) ⊓ centralizer (U : Set G))) H
              D.sourceOrbit ≤ Y ∧ ∃ hred : IsPReduced 2 (Y.subgroupOf H),
              let := hred.normal
              let q := ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H)
              ∃ C : Subgroup H, C.IsCComponent ∧
                IsComponent (ChapterB.InternalThompsonAction.ActionQuotient (Y.subgroupOf H))
                  (C.map (ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H))) ∧
                ¬ C.map H.subtype ≤ normalizer (L : Set G) ∧
                (localResidual L U).subgroupOf H ≤ normalizer (C : Set H) ∧
                (∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype =
                  (T : Subgroup G) ⊓ centralizer (U : Set G) ∧
                  (Q.subgroupOf H).relIndex (P : Subgroup H) = 2) ∧
                let C₀ := C.map H.subtype
                let M₀ := H ⊓ normalizer (L : Set G)
                Input KnownSimple.IsKnownSimple H Q M₀ C₀ ∧
                ¬ ChapterC.IsAlternatingBlock C₀ 5 ∧
                ¬ Chapter1.IsSylowIn 2 Q (C₀ ⊔ Q) ∧
                (localResidual L U).subgroupOf H ≤ C ∧ C.Normal ∧
                H = C₀ ⊔ ((T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
                (ChapterC.IsShort C → 16 < Nat.card (ChapterC.BlockModule C)) ∧
                (ChapterC.IsShort C →
                  let X := (⁅D.sourceOrbit.subgroupOf H,
                    (localResidual L U).subgroupOf H⁆).subgroupOf C
                  ⁅D.sourceOrbit.subgroupOf H,(localResidual L U).subgroupOf H⁆ ≤ C ∧
                  X ≤ ChapterC.blockU C ∧ Disjoint X (center C) ∧
                    Nat.card X = 16 ∧
                    X ≤ centralizer (((Q.subgroupOf H).subgroupOf C) : Set C)) ∧
                (∀ n, 5 ≤ n → n ≤ 8 → ¬ ChapterC.IsAlternatingBlock C n) ∧
                (∀ n, 5 ≤ n → n ≤ 8 → ¬ ChapterC.IsAlternatingBlock C₀ n) ∧
                (∀ n, ¬ ChapterC.IsLinearTwoBlock C n) ∧
                ¬ (ChapterC.IsShort C ∧
                  Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
                  Nat.card (ChapterC.BlockModule C) = 2 ^ 10) ∧
                ¬ ChapterC.IsAlternatingBlock C 7 ∧
                ¬ ChapterC.IsG2TwoBlock C ∧
                ¬ ChapterC.IsExceptionalA7Block C ∧
                ¬ ChapterC.IsAlternatingBlock C 6 ∧
                ¬ ChapterC.IsSL3EvenBlock C 1 ∧
                ¬ ChapterC.IsLinearTwoBlock C 4 ∧
                (((localBase L (T : Subgroup G) U).subgroupOf H).map q).pCoreIn 2 =
                  (Q.subgroupOf H).map q ∧
                ¬ ⁅((localResidual L U).subgroupOf H).map q,
                  (((T : Subgroup G) ⊓ centralizer (U : Set G)).subgroupOf H).map q ⊓ C.map q⁆ ≤
                    (((localResidual L U).subgroupOf H).map q).pCoreIn 2 ∧
                (let I := C.map q ⊓ ((H ⊓ normalizer (L : Set G)).subgroupOf H).map q
                 ¬ IsPPerfect 2 I ∧
                 ¬ IsSp4FourMaximalParabolic (I.subgroupOf (C.map q)) ∧
                 (∀ F' : BinaryField, 1 < F'.degree →
                   ¬ IsLinearMaximalParabolic (I.subgroupOf (C.map q)) 3 F'.Carrier) ∧
                 ∀ F' : BinaryField, 1 < F'.degree →
                   ¬ Nonempty (I ≃* Matrix.PSL3.LinearThree.pointParabolicSL F'.Carrier) ∧
                   ¬ Nonempty (I ≃* Matrix.PSL3.LinearThree.lineParabolicSL F'.Carrier) ∧
                   ¬ Nonempty (I ≃* Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F'.Carrier)) ∧
                   ¬ Nonempty (I ≃* Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F'.Carrier))) ∧
                (let P := (starM C₀ Q M₀).subgroupOf (starImage C₀ Q C₀)
                 ¬ IsPPerfect 2 P ∧ ¬ IsSp4FourMaximalParabolic P ∧
                 (∀ (F' : Type) [Field F'] [Finite F'] (n : ℕ), Nat.card F' = 2 ^ n → 1 < n →
                   ¬ IsLinearMaximalParabolic P 3 F') ∧
                 ∀ F' : BinaryField, 1 < F'.degree →
                   ¬ Nonempty (starImage C₀ Q C₀ ≃*
                     Theory.SpecificGroups.SymplecticFour.Sp F'.Carrier) ∧
                   ¬ Nonempty (starImage C₀ Q C₀ ≃* Matrix.SpecialLinearGroup (Fin 3) F'.Carrier)) ∧
                ¬ (ChapterC.IsExceptionalAhat6Block C₀ ∧
                  ((M₀ ⊓ C₀).subgroupOf C₀).index = 15) ∧
                (starImage C₀ Q Q).subgroupOf (starImage C₀ Q C₀) ≠ ⊥ ∧
                (∃ S : Sylow 2 (starImage C₀ Q C₀),
                  ((starImage C₀ Q Q).subgroupOf (starImage C₀ Q C₀)).relIndex
                    (S : Subgroup (starImage C₀ Q C₀)) ≤ 2) ∧
                (∀ F' : BinaryField,
                  ¬ Nonempty (starImage C₀ Q C₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F'.Carrier)) ∧
                (∀ F' : BinaryField, 1 < F'.degree →
                  ¬ Nonempty (starImage C₀ Q C₀ ≃* Atlas.G2.Model F'.Carrier)) ∧
                ¬ Nonempty (starImage C₀ Q C₀ ≃* alternatingGroup (Fin 6)) ∧
                D.sourceOrbit ≤ (starV C₀ Q).map (C₀ ⊔ Q : Subgroup G).subtype ∧
                Disjoint ⁅D.sourceOrbit,localResidual L U⁆
                  (centralizer (localResidual L U : Set G)) ∧
                Nat.card (⁅D.sourceOrbit,localResidual L U⁆ : Subgroup G) = 16 ∧
                DoubledBinaryStarRadicals.RemainingStarModel (starImage C₀ Q C₀) ∧
                ¬ Nonempty (starImage C₀ Q C₀ ≃* alternatingGroup (Fin 5)) ∧
                KernelConclusion C₀ Q ∧ OffenderConclusion C₀ Q ∧
                (starImage C₀ Q C₀ ⊓ normalizer
                  (starImage C₀ Q (elementaryAbelianMaxJ Q) : Set (StarQuotient C₀ Q)) ≤
                    starM C₀ Q M₀) ∧
                starM C₀ Q M₀ < starImage C₀ Q C₀ ∧
                let ρ := starRepresentation C₀ Q
                let J := offenderSubgroup ρ
                starImage C₀ Q C₀ ≤ J ∧
                Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
                  (ρ.comp J.subtype) ((starImage C₀ Q C₀).subgroupOf J))) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_star_radical_exclusions h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,hmodels,hrest⟩ := hescape hout
  let := hred.normal
  let := hred.elementary
  let U := ambientPlane D.sourceOrbit E v f
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  let C₀ := C.map H.subtype
  let A := localResidual L U
  let X := ⁅D.sourceOrbit,A⁆
  have hBH : localBase L (T : Subgroup G) U ≤ H := hH.1.1.2
  have hRH : R ≤ H := le_sup_right.trans hBH
  have hAH : A ≤ H := le_sup_left.trans hBH
  have hYH : Y ≤ H := conjugateSpanBy_le_self (by
    intro z hz
    exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hHY : H ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYH).mp hred.normal
  let eY := subgroupOfEquivOfLe hYH
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_injective
    eY.symm.toMonoidHom eY.symm.injective
  have hQfix : Q ≤ centralizer (D.sourceOrbit : Set G) := by
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G)
    rw [←D.doubledOrbit_sylow_centralizer h,←D.sourceOrbit_eq]
    exact inf_le_right
  have hWstar := DoubledBinaryStarSix.orbit_le_star_module hi Y D.sourceOrbit
    hHY hWY (D.sourceOrbit_core_normalizer h).1 (le_centralizer_iff.mp hQfix)
  have hAcontained : A ≤ C₀ := by
    intro a ha
    exact ⟨⟨a,hAH ha⟩,hAC ha,rfl⟩
  obtain ⟨hLN,k,hk,a,hE,ha,hcov⟩ := hmark
  obtain ⟨π,hπ,hker⟩ := DoubledBinaryPlaneQuotient.centralizer_quotient
    D.sourceOrbit U (DoubledBinaryPlaneQuotient.ambientPlane_equiv
      D.sourceOrbit L hLN k hk E hE a ha hcov v f hfv)
  let N := normalizer (D.sourceOrbit : Set G) ⊓ centralizer (U : Set G)
  have hAN : A ≤ N := le_inf
    ((map_subtype_le _).trans (inf_le_left.trans hLN))
    ((map_subtype_le _).trans inf_le_right)
  have hXW : X ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp (hAN.trans inf_le_left)
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_injective
    (inclusion hXW) (inclusion_injective hXW)
  have hsplit := DoubledBinarySmallBlocks.residual_coprime_split D.sourceOrbit N A
    inf_le_left hAN π hker (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G)))
  have hdis : Disjoint X (centralizer (A : Set G)) := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    exact (hsplit.le : X ⊓ (D.sourceOrbit ⊓ centralizer (A : Set G)) ≤ ⊥)
      ⟨hx.1,hXW hx.1,hx.2⟩
  have hcard : Nat.card X = 16 :=
    DoubledBinaryIntersection.pairedPlane_residual_card D.sourceOrbit L hLN k E hE v f hfv
      (DoubledBinaryOddCore.pairedPlane_residual_supplement D.sourceOrbit L hLN k hk E hE v f hfv)
  obtain ⟨S,hS⟩ := DoubledBinaryStarSix.component_sylow_index hi P hindex.le
  have hnoSix : ¬ Nonempty (starImage C₀ Q C₀ ≃* alternatingGroup (Fin 6)) := by
    rintro ⟨e⟩
    exact DoubledBinaryStarSix.no_six_star hi D.sourceOrbit A X hWstar hAcontained rfl hdis
      hcard (hXW.trans (le_centralizer_iff.mp hQfix)) S hS e
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,hnoSix,hWstar,hdis,hcard,hmodels,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
