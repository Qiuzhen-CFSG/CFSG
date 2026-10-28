module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryThreeQuotient
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeCore
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSInputs

/-!
# The full binary-three commutator core on the chosen paired-plane orbit

The original local base is the odd-index two-core witness and the original
characteristic-normalizer control gives MS3. These construct the genuine
binary MS input on the same KQ. Its recognized order-64 moving central
omega subgroup excludes a nonabelian commutator core through the actual
characteristic replacement. The whole core is therefore exactly that moved
subgroup and consists of two equal natural modules, with literal component
conjugation. Both original quotient kernels and all earlier markings survive.

This supplies the whole commutator-core step on printed p.709. The remaining
cubic-factor outer contradiction and ambient containment are still required;
no abelianness of the whole ambient two-core is asserted.
Source: Aschbacher--Smith, proof after 7.7.10 and C.1.31--34,
refs/quasithin.pdf, pp.709 and 135--137.
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

/-- The whole original commutator core is elementary of order 64,
with two equal natural copies and the literal component action. -/
theorem sourceOrbit_binary_pairedPlane_whole_core
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
                (toStarImage C₀ Q).ker = pCore 2 C₀ ∧
                Nonempty ((C₀ ⧸ pCore 2 C₀) ≃* starImage C₀ Q C₀) ∧
                (∃ S : Sylow 2 C₀,
                  (Q.subgroupOf C₀).relIndex (S : Subgroup C₀) ≤ 2 ∧
                  (S : Subgroup C₀).map C₀.subtype ≤
                    (T : Subgroup G) ⊓ centralizer (U : Set G) ∧
                  ∀ (m : ℕ) (e : starImage C₀ Q C₀ ≃*
                    Matrix.SpecialLinearGroup (Fin (m+1)) (ZMod 2)),
                  let f := (e.trans (BinaryLinear.OuterCyclic.slEquivLinear (m+1))).toMonoidHom.comp
                    (toStarImage C₀ Q)
                  ∃ (b : BinaryLinear.InvariantNodeActions.Basis m) (cuts : Set (Fin m)),
                    cuts.Nonempty ∧ cuts ≠ Set.univ ∧
                    (S : Subgroup C₀).map f = BinaryLinear.InvariantNodeActions.cutStabilizer b Set.univ ∧
                    (M₀.subgroupOf C₀).map f = BinaryLinear.InvariantNodeActions.cutStabilizer b cuts ∧
                    M₀.subgroupOf C₀ = (BinaryLinear.InvariantNodeActions.cutStabilizer b cuts).comap f ∧
                    f.ker = pCore 2 C₀ ∧
                    (M₀.subgroupOf C₀).index = (BinaryLinear.InvariantNodeActions.cutStabilizer b cuts).index) ∧
                ¬ Nonempty (starImage C₀ Q C₀ ≃* alternatingGroup (Fin 5)) ∧
                KernelConclusion C₀ Q ∧ OffenderConclusion C₀ Q ∧
                (starImage C₀ Q C₀ ⊓ normalizer
                  (starImage C₀ Q (elementaryAbelianMaxJ Q) : Set (StarQuotient C₀ Q)) ≤
                    starM C₀ Q M₀) ∧
                starM C₀ Q M₀ < starImage C₀ Q C₀ ∧
                let ρ := starRepresentation C₀ Q
                let J := offenderSubgroup ρ
                starImage C₀ Q C₀ ≤ J ∧
                ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
                  (ρ.comp J.subtype) ((starImage C₀ Q C₀).subgroupOf J),
                  DoubledBinaryModuleRecognition.BinaryMovedConclusion c ∧
                  DoubledBinaryMarkedParabolic.Conclusion C
                    ((localResidual L U).subgroupOf H)
                    (((T : Subgroup G) ⊓ centralizer (U : Set G)).subgroupOf H) ∧
                  ¬ Nonempty (starImage C₀ Q C₀ ≃*
                    Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
                  ¬ Nonempty (starImage C₀ Q C₀ ≃*
                    Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
                  (Nonempty (starImage C₀ Q C₀ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
                    Nonempty (center (starImage C₀ Q C₀) ≃* Multiplicative (ZMod 3)) ∧
                    Nonempty ((starImage C₀ Q C₀ ⧸ center (starImage C₀ Q C₀)) ≃*
                      alternatingGroup (Fin 6))) ∧
                  DoubledBinaryTripleSix.BinaryThreeConclusion c ∧
                  DoubledBinaryThreeQuotient.Conclusion C
                    ((localResidual L U).subgroupOf H) (Q.subgroupOf H)
                    (((T : Subgroup G) ⊓ centralizer (U : Set G)).subgroupOf H) ∧
                  H = C₀ ⊔ Q ∧
                  starKernel C₀ Q = pCore 2 (C₀ ⊔ Q : Subgroup G) ∧
                  64 ≤ Nat.card (center (⁅H.pCoreIn 2,C₀⁆ : Subgroup G)) ∧
                  DoubledBinaryThreeCore.WholeCoreConclusion KnownSimple.IsKnownSimple C₀ Q ∧
                  IsElementaryAbelian 2 (⁅H.pCoreIn 2,C₀⁆ : Subgroup G) ∧
                  Nat.card (⁅H.pCoreIn 2,C₀⁆ : Subgroup G) = 64) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_full_three h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,
    hnoSix,hnoSevenStar,hnoG2Star,hWstar,hdis,hcard,hmodels,hker,he,
    ⟨S,hS,hSR,hflags⟩,hnoFive,hkernel,hoffender,hthompson,hproper,hCJ,c,hm,hcon,
    hnoFiveStar,hnoFourStar,hremaining,hthree,hfull,hHjoin,hstarKernel,hcenterH⟩ := hescape hout
  let := hred.normal
  let U := ambientPlane D.sourceOrbit E v f
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let C₀ := C.map H.subtype
  let B := localBase L (T : Subgroup G) U
  have hBH : B ≤ H := hH.1.1.2
  have hBM : B ≤ H ⊓ normalizer (L : Set G) := by
    refine le_inf hBH ?_
    change localBase L (T : Subgroup G) (ambientPlane D.sourceOrbit E v f) ≤ _
    rw [hbase]
    exact inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hPB : (P : Subgroup H) ≤ B.subgroupOf H := by
    intro p hp
    have hRB : (T : Subgroup G) ⊓ centralizer (U : Set G) ≤ B := le_sup_right
    exact hRB (hP ▸ mem_map_of_mem H.subtype hp)
  have hr := ChapterC.C27Source.msOddIndexRadical_of_first_core hi B hBH hBM P hPB hcore.symm
  obtain ⟨F',hF',hrep⟩ := hthree.2.2.2
  have hwhole := DoubledBinaryThreeCore.whole_core_conclusion hi hr hthree.2.1.some
    hCJ c.sectionData F' hF' hrep
  have hambient := DoubledBinaryThreeCore.ambient_core_conclusion hwhole
  change IsElementaryAbelian 2 (⁅(C₀ ⊔ Q).pCoreIn 2,C₀⁆ : Subgroup G) ∧
    Nat.card (⁅(C₀ ⊔ Q).pCoreIn 2,C₀⁆ : Subgroup G) = 64 at hambient
  rw [←hHjoin] at hambient
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,
    hnoSix,hnoSevenStar,hnoG2Star,hWstar,hdis,hcard,hmodels,hker,he,
    ⟨S,hS,hSR,hflags⟩,hnoFive,hkernel,hoffender,hthompson,hproper,hCJ,c,hm,hcon,
    hnoFiveStar,hnoFourStar,hremaining,hthree,hfull,hHjoin,hstarKernel,hcenterH,hwhole,hambient⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
