module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryFixedLineBlocks
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryParabolicSection

/-!
# Nonbinary parabolic exclusions on the original reduced intersection

Keep the selected component, original cubic residual, full doubled orbit,
and both quotient kernels. The residual is normal in the local normalizer
intersection and its image still has two-core quotient of order dividing
three. The original component Sylow moves that quotient, so the literal
intersection C* ∩ M_H* is not two-perfect. Consequently it is isomorphic
to none of the four nonbinary SL₃ or Sp₄ maximal parabolics. The actual C.2.7 linear-three
and Sp₄(4) parabolic predicates are excluded as well.

No parabolic marking or extra movement hypothesis is assumed. The remaining
component classification must still identify the relevant intersection with
one of those models before the corresponding family is eliminated.

Source: Aschbacher--Smith, proof after Lemma 7.7.10, printed p.708,
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

/-- The original reduced component intersection has a nontrivial two-group
quotient, excluding all four nonbinary maximal-parabolic isomorphisms. -/
theorem sourceOrbit_binary_pairedPlane_parabolic_section_exclusions
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
    D.sourceOrbit_binary_pairedPlane_fixedLine_block_exclusions h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,hrest⟩ := hescape hout
  let := hred.normal
  let U := ambientPlane D.sourceOrbit E v f
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let A := (localResidual L U).subgroupOf H
  let M := (H ⊓ normalizer (L : Set G)).subgroupOf H
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  let q := ChapterB.InternalThompsonAction.actionMk (Y.subgroupOf H)
  let I := C.map q ⊓ M.map q
  have hAH : localResidual L U ≤ H := le_sup_left.trans hH.1.1.2
  have hn : M ≤ normalizer (A : Set H) :=
    (comap_mono (DoubledBinaryPushingUp.localResidual_normalizes L U H hHC)).trans
      (le_normalizer_comap H.subtype)
  have hnI : I ≤ normalizer (A.map q : Set _) :=
    inf_le_right.trans ((map_mono hn).trans (le_normalizer_map q))
  have hRM : R.subgroupOf H ≤ M := by
    intro r hr
    exact ⟨r.property,D.sylow_normalizes_component hr.1⟩
  have hSI : (R.subgroupOf H).map q ⊓ C.map q ≤ I :=
    le_inf inf_le_right (inf_le_left.trans (map_mono hRM))
  obtain ⟨hLN,k,hks,a,hE,ha,hcov⟩ := hmark
  obtain ⟨m⟩ := hmodel
  let model := m.groupEquiv.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv
  have hseed : (centralizer (V : Set G)).subgroupOf L = pCore 2 L :=
    D.seedComparison.centralizer_eq_twoCore
      (D.seedComparison.projection_injective_of_linearThree h.quasisimple model)
  have hVW : V ≤ D.sourceOrbit := by
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  let J0 := L ⊓ centralizer (U : Set G)
  obtain ⟨πL,hπL,hkL⟩ := DoubledBinaryResidualMovement.localBase_quotient
    D.sourceOrbit L J0 hLN k hks E hE a ha hcov v f hfv
    (inf_le_left.trans hLN) inf_le_right le_rfl
  let j : J0 →* L := inclusion inf_le_left
  have hj : Function.Injective j := inclusion_injective inf_le_left
  have hkernel : IsPGroup 2 πL.ker := by
    apply (pCore_isPGroup.comap_of_injective j hj).to_le
    intro x hx
    rw [hkL] at hx
    change j x ∈ pCore 2 L
    rw [←hseed]
    exact centralizer_le hVW hx
  have hcJ := DoubledBinaryResidualMovement.residual_cubic_quotient πL hπL hkernel
  let eA : pResidual 2 J0 ≃* A :=
    ((pResidual 2 J0).equivMapOfInjective J0.subtype J0.subtype_injective).trans
      (subgroupOfEquivOfLe hAH).symm
  have hcA : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv).symm.trans hcJ
  have hcImage := DoubledBinaryParabolicSection.image_cubic_quotient
    (q.subgroupMap A) (q.subgroupMap_surjective A) hcA
  have hnot : ¬ IsPPerfect 2 I :=
    DoubledBinaryParabolicSection.not_twoPerfect_of_cubic_movement (A.map q) I
      ((R.subgroupOf H).map q ⊓ C.map q) hcImage hnI hSI hmove
  have hpar := DoubledBinaryParabolicSection.no_nonbinary_parabolic hnot
  let eI : I.subgroupOf (C.map q) ≃* I := subgroupOfEquivOfLe inf_le_left
  have hnotI : ¬ IsPPerfect 2 (I.subgroupOf (C.map q)) := by
    intro hp
    exact hnot (hp.of_surjective eI.toMonoidHom eI.surjective)
  have hsp := DoubledBinaryParabolicSection.no_sp4Four_maximalParabolic _ hnotI
  have hsl (F' : BinaryField) (hn : 1 < F'.degree) :=
    DoubledBinaryParabolicSection.no_linearThree_maximalParabolic _ hnotI F'.card_eq hn
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,
    hnoLinear,hnoTen,hnoSeven,hnoG2,hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,
    ⟨hnot,hsp,hsl,hpar⟩,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
