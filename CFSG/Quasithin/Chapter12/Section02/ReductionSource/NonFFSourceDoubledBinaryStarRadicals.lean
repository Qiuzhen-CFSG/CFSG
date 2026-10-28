module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryExceptionalSix
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarRadicals

/-!
# Rank-one and nonbinary G₂ exclusions on the original star component

The actual source radical Q has index two in the chosen Sylow of H.
Its intersection with the perfect star component is therefore nontrivial
and still has index at most two in a component Sylow. The full rank-one
radical classification makes Q Sylow in KQ. In nonbinary G₂, the alternative
parabolic radical has Sylow index q > 2, so the same Sylow conclusion holds.
Both contradict the already established original non-Sylow condition. The
previous exclusions then give an exhaustive list of the remaining star models.

This keeps the original orbit, seed planes, component and both quotient
kernels. The other constrained models, ambient containment and binary endgame
remain obligations of the doubled-branch assembly.
Source: Aschbacher--Smith 7.7.9--10, pp.708--709, and C.2.7, pp.145--147,
refs/quasithin.pdf.
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

/-- The original star radical has a nontrivial half-Sylow intersection;
all rank-one and nonbinary G₂ star components are excluded. -/
theorem sourceOrbit_binary_pairedPlane_star_radical_exclusions
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
    D.sourceOrbit_binary_pairedPlane_exceptionalSix_exclusion h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hrest⟩ := hescape hout
  have hnontrivial := DoubledBinaryStarRadicals.star_intersection_ne_bot hi P hindex.le
  have hsmall := DoubledBinaryStarRadicals.star_intersection_sylow_index hi P hindex.le
  have hnoRankOne : ∀ F' : BinaryField,
      ¬ Nonempty (starImage (C.map H.subtype) ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (C.map H.subtype) ≃* Matrix.SpecialLinearGroup (Fin 2) F'.Carrier) := by
    rintro F' ⟨e⟩
    exact hnotSylow (DoubledBinaryStarRadicals.rankOne_star_core_sylow hi P hindex.le F' e)
  have hnoG2Large : ∀ F' : BinaryField, 1 < F'.degree →
      ¬ Nonempty (starImage (C.map H.subtype) ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (C.map H.subtype) ≃* Atlas.G2.Model F'.Carrier) := by
    rintro F' hF' ⟨e⟩
    exact hnotSylow (DoubledBinaryStarRadicals.g2_star_core_sylow hi P hindex.le F' hF' e)
  have hmodels := DoubledBinaryStarRadicals.remaining_star_models hi P hindex.le
    hnotSylow hrest.1 (fun F' hn => (hstar.2.2.2 F' hn).2)
      (fun F' hn => (hstar.2.2.2 F' hn).1)
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,hmodels,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
