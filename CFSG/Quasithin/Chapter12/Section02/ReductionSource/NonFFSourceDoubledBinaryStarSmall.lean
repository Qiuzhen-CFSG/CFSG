module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryStarSix
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarSmall

/-!
# The alternating-seven and derived binary G₂ star exclusions

Apply the full B.5 moved-section comparison to the original escaping component.
The original residual subgroup of order sixteen embeds in its central quotient;
its subgroup fixed by the original local Sylow has order at least four. The
natural A₇ six-space, exceptional A₇ four-space and derived G₂ six-space each
contradict these bounds. All quotient kernels and the same seed marking remain.

Source: Aschbacher--Smith, elimination after 7.7.10, printed p.709, and
B.4.2/B.5.1, printed pp.86 and99--103, refs/quasithin.pdf.
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

/-- Both remaining small star groups are excluded on the original chosen
orbit, without a whole-component recognition or an additional source premise. -/
theorem sourceOrbit_binary_pairedPlane_small_star_exclusions
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
                ¬ Nonempty (starImage C₀ Q C₀ ≃* alternatingGroup (Fin 7)) ∧
                ¬ Nonempty (starImage C₀ Q C₀ ≃* commutator (Atlas.G2.Model (ZMod 2))) ∧
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
    D.sourceOrbit_binary_pairedPlane_six_star_exclusion h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,
    hnoSix,hWstar,hdis,hcard,hmodels,hrest⟩ := hescape hout
  let := hred.normal
  let U := ambientPlane D.sourceOrbit E v f
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let C₀ := C.map H.subtype
  let A := localResidual L U
  let X := ⁅D.sourceOrbit,A⁆
  have hBH : localBase L (T : Subgroup G) U ≤ H := hH.1.1.2
  have hAH : A ≤ H := le_sup_left.trans hBH
  have hAK : A ≤ C₀ := by
    intro a ha
    exact ⟨⟨a,hAH ha⟩,hAC ha,rfl⟩
  have hAW : A ≤ normalizer (D.sourceOrbit : Set G) :=
    (map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes)
  have hXW : X ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp hAW
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_injective
    (inclusion hXW) (inclusion_injective hXW)
  have hQfix : X ≤ centralizer (Q : Set G) := by
    apply hXW.trans
    apply le_centralizer_iff.mp
    change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G)
    rw [←D.doubledOrbit_sylow_centralizer h,←D.sourceOrbit_eq]
    exact inf_le_right
  obtain ⟨hLN,k,hk,a,hE,ha,hcov⟩ := hmark
  have he := DoubledBinaryPlaneQuotient.ambientPlane_equiv
    D.sourceOrbit L hLN k hk E hE a ha hcov v f hfv
  have hn : R ≤ normalizer (X : Set G) :=
    DoubledBinarySylowFixed.localSylow_normalizes_movement
      D.sourceOrbit L (T : Subgroup G) U D.sylow_normalizes_component
      D.sourceOrbit_weakClosure_setup.normalizes
  have hr := DoubledBinarySylowFixed.centralizer_index_le_two D.sourceOrbit U R
    (inf_le_left.trans D.sourceOrbit_weakClosure_setup.normalizes) inf_le_right
    (T.isPGroup'.to_le inf_le_left) he
  have hfixed := DoubledBinarySylowFixed.four_le_fixed_card D.sourceOrbit X R hXW hn hcard hr
  let Z := X ⊓ centralizer (R : Set G)
  have hZcard : 4 ≤ Nat.card Z := by
    have hz : ((centralizer (R : Set G)).subgroupOf X).map X.subtype = Z := by
      rw [subgroupOf_map_subtype,inf_comm]
    rwa [←card_map_of_injective X.subtype_injective,hz] at hfixed
  obtain ⟨S,hS,hSR⟩ := DoubledBinaryStarSmall.component_sylow_inside hi P hindex.le
  have hSR' : (S : Subgroup C₀).map C₀.subtype ≤ R := by
    rw [hP] at hSR
    exact hSR
  have hZS : Z ≤ centralizer ((S : Subgroup C₀).map C₀.subtype : Set G) :=
    inf_le_right.trans (centralizer_le hSR')
  have hex := DoubledBinaryStarSmall.no_small_star hi D.sourceOrbit A X
    hWstar hAK rfl hdis hcard hQfix S hS Z inf_le_left hZcard hZS
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,hnoSix,
    (fun h7 => hex (Or.inl h7)),(fun hg2 => hex (Or.inr hg2)),
    hWstar,hdis,hcard,hmodels,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
