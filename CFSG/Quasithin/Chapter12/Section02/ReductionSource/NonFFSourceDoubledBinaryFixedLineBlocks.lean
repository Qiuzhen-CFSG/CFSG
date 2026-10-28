module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinarySixSpaceBlocks
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFixedLineBlocks
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# Remaining fixed-line blocks on the chosen doubled orbit

Keep the original Sylow, radical Q, residual, full orbit, and selected lifted
component. The order-sixteen residual commutator is Sylow invariant and Q
centralizes it. Since Q has index two in the original Sylow, the commutator
has at least four Sylow-fixed elements. Its embedding in the block module
retains the full central quotient kernel.

The fixed-line bounds now exclude the natural A₈ six-space, every single
natural binary linear block, and both ten-dimensional SL₅(2) irreducibles.
Combining the earlier exclusions gives every ordinary alternating block
of degrees five through eight, also on the literal ambient image used by
C.2.7. The exceptional triple-six, other constrained rows, ambient
containment, binary endgame, and original non-FF contradiction remain open.

Source: Aschbacher--Smith, proof of Proposition 7.7.3 after Lemma 7.7.10,
printed p.709, refs/quasithin.pdf.
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

/-- Exclude every ordinary alternating block of degrees five through eight and
every single natural binary linear block, and the ten-dimensional SL₅(2)
irreducible block on the original selected component. -/
theorem sourceOrbit_binary_pairedPlane_fixedLine_block_exclusions
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
    D.sourceOrbit_binary_pairedPlane_sixSpace_exclusions h hd hnon F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hbase,hcore,?_⟩
  dsimp only
  intro hout
  obtain ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoSeven,hnoG2,
    hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,hrest⟩ := hescape hout
  let := hred.normal
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let Y := conjugateSpanBy (omegaOneCenterAmbient R) H
  let A := (localResidual L U).subgroupOf H
  let W := D.sourceOrbit.subgroupOf H
  let X := ⁅W,A⁆
  change B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) at hbase
  have hBH : B ≤ H := hH.1.1.2
  have hRH : R ≤ H := le_sup_right.trans hBH
  have hAH : localResidual L U ≤ H := le_sup_left.trans hBH
  have hYH : Y ≤ H := conjugateSpanBy_le_self (by
    intro z hz
    exact hRH ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hWH : D.sourceOrbit ≤ H := hWY.trans hYH
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hWH
  have hLN : L ≤ normalizer (D.sourceOrbit : Set G) := hmark.1
  have hBN : B ≤ normalizer (D.sourceOrbit : Set G) := by
    rw [hbase]
    exact inf_le_left.trans (sup_le hLN D.sourceOrbit_weakClosure_setup.normalizes)
  have hAW : A ≤ normalizer (W : Set H) :=
    (comap_mono (show localResidual L U ≤ normalizer (D.sourceOrbit : Set G) from
      le_sup_left.trans hBN)).trans (le_normalizer_comap H.subtype)
  have hXW : X ≤ W := le_normalizer_iff_commutator_le_left.mp hAW
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.of_injective
    (inclusion hXW) (inclusion_injective hXW)
  have hQeq : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hmap : X.map H.subtype = ⁅D.sourceOrbit,localResidual L U⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hWH,map_subgroupOf_eq_of_le hAH]
  have hn : R ≤ normalizer ((⁅D.sourceOrbit,localResidual L U⁆ : Subgroup G) : Set G) :=
    DoubledBinarySylowFixed.localSylow_normalizes_movement
      D.sourceOrbit L (T : Subgroup G) U D.sylow_normalizes_component
      D.sourceOrbit_weakClosure_setup.normalizes
  have hPX : (P : Subgroup H) ≤ normalizer (X : Set H) := by
    have hXpre : X = (⁅D.sourceOrbit,localResidual L U⁆).comap H.subtype := by
      rw [←hmap,comap_map_eq_self_of_injective H.subtype_injective]
    rw [hXpre]
    intro p hp
    apply le_normalizer_comap H.subtype
    have hpR := mem_map_of_mem H.subtype hp
    rw [hP] at hpR
    exact hn hpR
  have hXQ : X ≤ centralizer (Q.subgroupOf H : Set H) := by
    intro x hx q hq
    apply Subtype.ext
    have hc : ((q : H) : G) ∈ centralizer (D.sourceOrbit : Set G) :=
      (hQeq.symm ▸ (show ((q : H) : G) ∈ Q from hq)).2
    exact (hc x (hXW hx)).symm
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_subnormal C hC.subnormal
  have hfixed (hb : ChapterC.IsShort C) :
      ∃ Z : Subgroup C, Z ≤ ChapterC.blockU C ∧ Disjoint Z (center C) ∧
        4 ≤ Nat.card Z ∧ Z ≤ centralizer (S : Set C) := by
    obtain ⟨hXC,hDU,hDZ,hXcard,_⟩ := hmodule hb
    have hcard : Nat.card X = 16 := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hXC).toEquiv] at hXcard
    have hsquare := card_le_centralizer_card_sq_of_relIndex_two X (Q.subgroupOf H)
      (P : Subgroup H) hPX hXQ hindex
    rw [hcard] at hsquare
    change 16 ≤ Nat.card ((centralizer (P : Set H)).subgroupOf X) ^ 2 at hsquare
    let Z := X ⊓ centralizer (P : Set H)
    have hZcard : 4 ≤ Nat.card Z := by
      have he : ((centralizer (P : Set H)).subgroupOf X).map X.subtype = Z := by
        rw [subgroupOf_map_subtype,inf_comm]
      rw [←card_map_of_injective X.subtype_injective,he] at hsquare
      nlinarith
    have hZC : Z ≤ C := inf_le_left.trans hXC
    refine ⟨Z.subgroupOf C,
      (comap_mono (show Z ≤ X from inf_le_left)).trans hDU,
      hDZ.mono_left (comap_mono (show Z ≤ X from inf_le_left)),?_,?_⟩
    · rwa [Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv]
    · intro z hz s hs
      apply Subtype.ext
      have hsP : (s : H) ∈ (P : Subgroup H) := by
        change s ∈ (S : Subgroup C) at hs
        rw [hS] at hs
        exact hs
      exact hz.2 s hsP
  have hnoEight : ¬ ChapterC.IsAlternatingBlock C 8 := by
    intro hb
    obtain ⟨Z,hZU,hZZ,hZcard,hZS⟩ := hfixed hb.2.1
    have hbnd := DoubledBinaryFixedLineBlocks.eight_block_sylow_fixed_card
      hb S Z hZU hZZ hZS
    omega
  have hnoLinear (n : ℕ) : ¬ ChapterC.IsLinearTwoBlock C n := by
    intro hb
    obtain ⟨Z,hZU,hZZ,hZcard,hZS⟩ := hfixed hb.2.1
    have hbnd := DoubledBinaryFixedLineBlocks.binary_linear_block_sylow_fixed_card
      hb S Z hZU hZZ hZS
    omega
  have hnoTen : ¬ (ChapterC.IsShort C ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
      Nat.card (ChapterC.BlockModule C) = 2 ^ 10) := by
    rintro ⟨hb,⟨m⟩,hc⟩
    obtain ⟨Z,hZU,hZZ,hZcard,hZS⟩ := hfixed hb
    have hbnd := DoubledBinaryFixedLineBlocks.linear_five_ten_block_sylow_fixed_card
      hb m hc S Z hZU hZZ hZS
    omega
  have hnoAlt (n : ℕ) (hn : 5 ≤ n) (hn8 : n ≤ 8) : ¬ ChapterC.IsAlternatingBlock C n := by
    interval_cases n
    · intro hb
      have hbig := hlarge hb.2.1
      rw [hb.module_card_odd (by decide)] at hbig
      norm_num at hbig
    · exact hnoA6
    · exact hnoSeven
    · exact hnoEight
  have hnoAltAmbient (n : ℕ) (hn : 5 ≤ n) (hn8 : n ≤ 8) :
      ¬ ChapterC.IsAlternatingBlock (C.map H.subtype) n := by
    intro hb
    exact hnoAlt n hn hn8
      (hb.of_mulEquiv (C.equivMapOfInjective H.subtype H.subtype_injective).symm)
  exact ⟨H,hH,hHC,hWY,hred,C,hC,hCimage,hCM,hLC,⟨P,hP,hindex⟩,
    hi,hno,hnotSylow,hAC,hnormal,hgen,hlarge,hmodule,hnoAlt,hnoAltAmbient,hnoLinear,hnoTen,hnoSeven,hnoG2,
    hnoA7,hnoA6,hnoL3,hnoL4,hcoreImage,hmove,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
