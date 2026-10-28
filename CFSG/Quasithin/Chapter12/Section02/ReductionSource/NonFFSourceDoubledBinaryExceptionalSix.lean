module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryStarIntersection
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryExceptionalSix

/-!
# Excluding the original exceptional triple-six source intersection

The original chosen component contains the residual sixteen in its intrinsic
commutator module. Transport this subgroup to the ambient component used by
C.2.7, keeping its full central kernel. The actual paired-plane centralizer
acts through S₃, with kernel the centralizer of the whole doubled orbit.
That kernel centralizes the residual sixteen. The exceptional block's
faithful SL₃(F₄) restriction excludes a cubic in this kernel, contradicting
the index-fifteen clause of C.2.7(c).

All previous component and star exclusions remain on the same original
conjugator, seed axes, orbit and chosen component. This rules out the actual
exceptional source alternative; it does not assert that the block predicate
alone gives a fixed-space contradiction or that the full C.2.7 classification
has already been assembled. Ambient containment and the binary endgame remain
with the doubled-branch owner.

Source: Aschbacher--Smith C.2.7(3)(c), printed p.145, and the proof after
7.7.10, pp.708--709, refs/quasithin.pdf.
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

/-- The exceptional triple-six block and its literal index-fifteen
intersection cannot occur on the original chosen component. -/
theorem sourceOrbit_binary_pairedPlane_exceptionalSix_exclusion
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
    D.sourceOrbit_binary_pairedPlane_star_parabolic_exclusions h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hrest⟩ := hescape hout
  let := hred.normal
  let U := ambientPlane D.sourceOrbit E v f
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let C₀ := C.map H.subtype
  let M₀ := H ⊓ normalizer (L : Set G)
  have hnoExceptional : ¬ (ChapterC.IsExceptionalAhat6Block C₀ ∧
      ((M₀ ⊓ C₀).subgroupOf C₀).index = 15) := by
    rintro ⟨hb,h15⟩
    let e : C ≃* C₀ := C.equivMapOfInjective H.subtype H.subtype_injective
    let W := D.sourceOrbit.subgroupOf H
    let A := (localResidual L U).subgroupOf H
    let X := (⁅W,A⁆).subgroupOf C
    obtain ⟨hXC,hXU,hXZ,hXcard,hXQ⟩ := hmodule (hb.1.of_mulEquiv e.symm)
    let X₀ := X.map e.toMonoidHom
    have hUmap : (ChapterC.blockU C).map e.toMonoidHom = ChapterC.blockU C₀ := by
      rw [ChapterC.blockU,map_commutator,pCore_map_iso,
        map_top_of_surjective _ e.surjective,ChapterC.blockU]
    have hX₀U : X₀ ≤ ChapterC.blockU C₀ := hUmap ▸ map_mono hXU
    have hX₀card : 16 ≤ Nat.card X₀ := by
      rw [card_map_of_injective e.injective]
      exact hXcard.ge
    have hNamb : normalizer (L : Set G) ≤ normalizer (D.sourceOrbit : Set G) :=
      (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).symm.le
    have hAN : localResidual L U ≤ normalizer (D.sourceOrbit : Set G) :=
      ((map_subtype_le _).trans inf_le_left).trans (L.le_normalizer.trans hNamb)
    have hAW : A ≤ normalizer (W : Set H) :=
      (comap_mono hAN).trans (le_normalizer_comap H.subtype)
    have hXW : X₀.map C₀.subtype ≤ D.sourceOrbit := by
      rintro z ⟨y,⟨x,hx,rfl⟩,rfl⟩
      exact le_normalizer_iff_commutator_le_left.mp hAW hx
    obtain ⟨hLN,k,hk,a,hE,ha,hcov⟩ := hmark
    obtain ⟨π₀,hπ₀,hker₀⟩ := DoubledBinaryPlaneQuotient.centralizer_quotient
      D.sourceOrbit U (DoubledBinaryPlaneQuotient.ambientPlane_equiv
        D.sourceOrbit L hLN k hk E hE a ha hcov v f hfv)
    let N₀ := normalizer (D.sourceOrbit : Set G) ⊓ centralizer (U : Set G)
    let B := (M₀ ⊓ C₀).subgroupOf C₀
    let j : B →* N₀ := (C₀.subtype.comp B.subtype).codRestrict N₀
      (fun b => ⟨hNamb b.property.1.2,hHC b.property.1.1⟩)
    let π := π₀.comp j
    have hker : ∀ x : π.ker, (x.val : C₀) ∈ centralizer (X₀ : Set C₀) := by
      intro x
      have hc : (j x.val : G) ∈ centralizer (D.sourceOrbit : Set G) := by
        have hh : j x.val ∈ π₀.ker := x.property
        rw [hker₀] at hh
        exact hh
      intro z hz
      apply Subtype.ext
      exact hc z (hXW (mem_map_of_mem C₀.subtype hz))
    exact DoubledBinaryExceptionalSix.no_exceptional_index_fifteen
      hb B X₀ hX₀U hX₀card π hker h15
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
