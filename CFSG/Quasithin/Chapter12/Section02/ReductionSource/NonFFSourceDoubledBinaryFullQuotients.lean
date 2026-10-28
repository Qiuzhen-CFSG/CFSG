module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryStarSmall
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFullQuotients

/-!
# Full core quotients and marked intersections on the original doubled orbit

The surviving star catalogue now identifies the literal map from K/O₂(K)
as an isomorphism, including the triple-six center. The original orbit in
the star module puts the full star kernel inside M. Each binary linear
row then has M ∩ K as the exact inverse image of a proper partial flag;
the full flag is marked by a Sylow inside the original T₀, with its
half-Sylow radical bound retained. No core is discarded and no full block
recognition is inferred from these group quotients.

Source: Aschbacher--Smith, proof after 7.7.10, printed pp.708--709,
C.2.7, pp.145--147, and I.1.2--3, p.407, refs/quasithin.pdf.
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

/-- The remaining original components have exactly their two-core as star
kernel. Every binary linear row has its actual intersection marked as the
full preimage of a partial flag sharing the original component Sylow. -/
theorem sourceOrbit_binary_pairedPlane_full_quotients
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
                Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
                  (ρ.comp J.subtype) ((starImage C₀ Q C₀).subgroupOf J))) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,hescape⟩ :=
    D.sourceOrbit_binary_pairedPlane_small_star_exclusions h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,
    hnoSix,hnoSevenStar,hnoG2Star,hWstar,hdis,hcard,hmodels,hrest⟩ := hescape hout
  let := hred.normal
  let U := ambientPlane D.sourceOrbit E v f
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let C₀ := C.map H.subtype
  let M₀ := H ⊓ normalizer (L : Set G)
  have hinj := DoubledBinaryFullQuotients.comparison_injective_of_remaining
    hi hmodels hnoSix hnoSevenStar hnoG2Star
  have hker := DoubledBinaryFullQuotients.star_kernel_eq_core hi hinj
  let e : (C₀ ⧸ pCore 2 C₀) ≃* starImage C₀ Q C₀ :=
    MulEquiv.ofBijective (coreToStar hi.normalizes) ⟨hinj,coreToStar_surjective hi.normalizes⟩
  have hcent : C₀ ⊓ centralizer (D.sourceOrbit : Set G) ≤ M₀ := by
    refine le_inf (inf_le_left.trans hi.component.1) ?_
    exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (D.sourceOrbit : Set G)).trans
      (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).le)
  obtain ⟨S,hS,hSR⟩ := DoubledBinaryStarSmall.component_sylow_inside hi P hindex.le
  have hSM : (S : Subgroup C₀).map C₀.subtype ≤ M₀ := by
    refine le_inf (hSR.trans (map_subtype_le _)) ?_
    rw [hP] at hSR
    exact hSR.trans (inf_le_left.trans D.sylow_normalizes_component)
  let A := localResidual L U
  have hAH : A ≤ H := le_sup_left.trans hH.1.1.2
  have hAK : A ≤ C₀ := by
    intro a ha
    exact ⟨⟨a,hAH ha⟩,hAC ha,rfl⟩
  have hAM : A ≤ M₀ := le_inf hAH
    ((map_subtype_le _).trans (inf_le_left.trans L.le_normalizer))
  have hp : IsPPerfect 2 A := isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G))
  have hm : ⁅D.sourceOrbit,A⁆ ≠ ⊥ := by
    intro hz
    rw [hz,card_bot] at hcard
    omega
  have hflags := fun m (a : starImage C₀ Q C₀ ≃*
      Matrix.SpecialLinearGroup (Fin (m+1)) (ZMod 2)) =>
    DoubledBinaryFullQuotients.binary_flag_intersection hi hinj D.sourceOrbit hWstar hcent A hAK hAM hp hm S hSM a
  have hSR' : (S : Subgroup C₀).map C₀.subtype ≤ R := by rwa [hP] at hSR
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    hpar,hstar,hnoExceptional,hnontrivial,hsmall,hnoRankOne,hnoG2Large,hnoSix,
    hnoSevenStar,hnoG2Star,hWstar,hdis,hcard,hmodels,hker,⟨e⟩,⟨S,hS,hSR',hflags⟩,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
