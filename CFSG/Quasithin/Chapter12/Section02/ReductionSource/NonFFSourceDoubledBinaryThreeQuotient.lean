module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryTripleSix
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeQuotient
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSInputs

/-!
# The whole escaping quotient on the original paired-plane orbit

The actual cubic residual, original Sylow and local base identify a
rank-one parabolic in the surviving binary-three quotient. Its node cannot
be fixed by an outer actor, so the whole escaping group has the same
SL₃(2) quotient as its component. The original local base contains a Sylow,
hence its two-core Q contains O₂(H), giving H = KQ with all quotient maps
and kernels retained. Q has index 42, and the local base has index seven. The literal star kernel is the whole two-core, and the recognized
moved subgroup gives |Z([O₂(H),K])| ≥ 64 before any central quotient.

This establishes the group and radical data needed for the source's
whole-core and cubic-factor argument. Recognition of the whole two-core,
the outer contradiction and ambient containment remain necessary.
Source: Aschbacher--Smith, proof after 7.7.10, printed p.709,
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

/-- The full original escaping group has the binary-three quotient, with
its exact kernel and original radical; no source premise is added. -/
theorem sourceOrbit_binary_pairedPlane_full_three
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
                  64 ≤ Nat.card (center (⁅H.pCoreIn 2,C₀⁆ : Subgroup G))) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_linearThree h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,
    hnoSix,hnoSevenStar,hnoG2Star,hWstar,hdis,hcard,hmodels,hker,he,
    ⟨S,hS,hSR,hflags⟩,hnoFive,hkernel,hoffender,hthompson,hproper,hCJ,c,hm,hcon,
    hnoFiveStar,hnoFourStar,hremaining,hthree⟩ := hescape hout
  let := hred.normal
  let U := ambientPlane D.sourceOrbit E v f
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let C₀ := C.map H.subtype
  let B := localBase L (T : Subgroup G) U
  let AH := (localResidual L U).subgroupOf H
  have hBH : B ≤ H := hH.1.1.2
  have hAH : localResidual L U ≤ H := le_sup_left.trans hBH
  have hRH : R ≤ H := le_sup_right.trans hBH
  have hB0 : AH ⊔ (P : Subgroup H) = B.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAH,hP,map_subgroupOf_eq_of_le hBH]
    rfl
  have hPA : (P : Subgroup H) ≤ normalizer (AH : Set H) := by
    have hn : (H ⊓ normalizer (L : Set G)).subgroupOf H ≤ normalizer (AH : Set H) :=
      (comap_mono (DoubledBinaryPushingUp.localResidual_normalizes L U H hHC)).trans
      (le_normalizer_comap H.subtype)
    apply le_trans ?_ hn
    intro p hp
    exact ⟨p.property,D.sylow_normalizes_component ((hP ▸ mem_map_of_mem H.subtype hp).1)⟩
  obtain ⟨hLN,k,hks,a,hE,ha,hcov⟩ := hmark
  obtain ⟨seed⟩ := hmodel
  let model := seed.groupEquiv.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv
  have hseed : (centralizer (V : Set G)).subgroupOf L = pCore 2 L :=
    D.seedComparison.centralizer_eq_twoCore
      (D.seedComparison.projection_injective_of_linearThree h.quasisimple model)
  have hVW : V ≤ D.sourceOrbit := by
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  let J0 := L ⊓ centralizer (U : Set G)
  obtain ⟨πL,hπL,hkL⟩ := DoubledBinaryResidualMovement.localBase_quotient
    D.sourceOrbit L J0 hLN k hks E hE a ha hcov v f hfv (inf_le_left.trans hLN) inf_le_right le_rfl
  let j : J0 →* L := inclusion inf_le_left
  have hj : Function.Injective j := inclusion_injective inf_le_left
  have hπkernel : IsPGroup 2 πL.ker := by
    apply (pCore_isPGroup.comap_of_injective j hj).to_le
    intro x hx
    rw [hkL] at hx
    change j x ∈ pCore 2 L
    rw [←hseed]
    exact centralizer_le hVW hx
  have hcJ := DoubledBinaryResidualMovement.residual_cubic_quotient πL hπL hπkernel
  let eA : pResidual 2 J0 ≃* AH :=
    ((pResidual 2 J0).equivMapOfInjective J0.subtype J0.subtype_injective).trans
      (subgroupOfEquivOfLe hAH).symm
  have hcA : Nat.card (AH ⧸ pCore 2 AH) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv).symm.trans hcJ
  let := hnormal
  let eC : C ≃* C₀ := C.equivMapOfInjective H.subtype H.subtype_injective
  let e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).trans hthree.2.1.some
  have hgenP : C ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hP,←MonoidHom.range_eq_map,range_subtype]
    exact hgen.symm
  have hSP : (P : Subgroup H) ≤ B.subgroupOf H := by
    rw [←hB0]
    exact le_sup_right
  have hQeq : (B.subgroupOf H).pCoreIn 2 = Q.subgroupOf H := by
    rw [pCoreIn_subgroupOf 2 B H hBH]
    exact congrArg (fun X : Subgroup G => X.subgroupOf H) hcore
  have hQ : pCore 2 H ≤ Q.subgroupOf H := by
    rw [←hQeq]
    exact pCore_le_map_pCore_of_prime_not_dvd_index (B.subgroupOf H)
      (fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hSP)))
  have hQP : Q.subgroupOf H ≤ (P : Subgroup H) := by
    rw [←hQeq]
    rintro p ⟨x,hx,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (P.subtype hSP) hx
  have hfull := DoubledBinaryThreeQuotient.conclusion_of_cubic_base
    C AH (Q.subgroupOf H) P hPA hcA hAC hgenP hQ hQP hindex e
  have hHjoin : H = C₀ ⊔ Q := by
    obtain ⟨_,_,_,_,_,_,_,_,_,hjoin,_⟩ := hfull
    have hh := congrArg (map H.subtype) hjoin
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hi.setup.radical_le,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm
  have hP0 : (P : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRH]
  have hfull' : DoubledBinaryThreeQuotient.Conclusion C AH (Q.subgroupOf H)
      (R.subgroupOf H) := hP0 ▸ hfull
  have hstarKernel := DoubledBinaryThreeQuotient.star_kernel_eq_twoCore hi.normalizes
    (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))) hkernel hthree.2.1.some
  obtain ⟨F',hF',hrep⟩ := hthree.2.2.2
  have hcenter := DoubledBinaryThreeQuotient.moved_center_card hCJ c.sectionData F' hF' hrep
  have hcenterH : 64 ≤ Nat.card (center (⁅H.pCoreIn 2,C₀⁆ : Subgroup G)) := by
    change 64 ≤ Nat.card (center (⁅(C₀ ⊔ Q).pCoreIn 2,C₀⁆ : Subgroup G)) at hcenter
    rwa [←hHjoin] at hcenter
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,
    hnoSix,hnoSevenStar,hnoG2Star,hWstar,hdis,hcard,hmodels,hker,he,
    ⟨S,hS,hSR,hflags⟩,hnoFive,hkernel,hoffender,hthompson,hproper,hCJ,c,hm,hcon,
    hnoFiveStar,hnoFourStar,hremaining,hthree,hfull',hHjoin,hstarKernel,hcenterH⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
