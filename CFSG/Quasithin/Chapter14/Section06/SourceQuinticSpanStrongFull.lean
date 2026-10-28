module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticElementaryNormalBound
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanKernel
import all CFSG.Quasithin.Chapter14.Section06.SourceQuinticHyperplanes
import all CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelRadicals

/-!
# One selected quintic span with the full geometric and kernel interface

The original critical conjugator is retained throughout the reciprocal size
calculation and the full-centralizer calculation. The path bound makes this
same span have order 32. In particular its core commutator lies in the original
quintic span, with both the middle-core product and nonzero reciprocal
commutator still available for the derived-core argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The full span interface for the same original critical conjugator. -/
theorem source_quintic_second_kernel_span_strong_full
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    ∃ g ∈ X,
      let Ustar := U.map (MulAut.conj g).toMonoidHom
      let Qstar := (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
      let R := U ⊓ Qstar
      let Rstar := Ustar ⊓ H.pCoreIn 2
      let W := conjugateSpanBy R X
      Ustar ≤ X.pCoreIn 2 ∧ ¬ Ustar ≤ H.pCoreIn 2 ∧
        localModule T M ≤ U ⊓ Ustar ∧
        (T : Subgroup G) ≤ normalizer ((U ⊓ Ustar : Subgroup G) : Set G) ∧
        (H.pCoreIn 2 ⊓ X.pCoreIn 2) ⊔ (Qstar ⊓ X.pCoreIn 2) = X.pCoreIn 2 ∧
        ⁅U ⊓ Ustar,X.pCoreIn 2⁆ = localModule T M ∧ U = ⁅U,H⁆ ∧
        IsElementaryAbelian 2 W ∧ W ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 ∧
        X ≤ normalizer (W : Set G) ∧ W ⊓ U = R ∧ W ⊓ Ustar = Rstar ∧
        Rstar ≤ W ∧ ⁅Rstar,U⁆ ≠ ⊥ ∧
        Nat.card R = 16 ∧ Nat.card Rstar = 16 ∧ Nat.card W = 32 ∧
        ⁅W,U⁆ = centralInvolutions T ∧ U ⊓ centralizer (W : Set G) = R ∧
        (W ⊓ C).relIndex W = 2 ∧ 2 * Nat.card (W ⊓ C : Subgroup G) = Nat.card W ∧
        W ⊓ C = R ∧ ⁅W,H.pCoreIn 2⁆ ≤ U := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  obtain ⟨g,hg,hDQ,hescape,hVI,hTI,hprod,hIQ,hUH,hWel,hWQ,hXW,hWU,hRW,hWUstar,hmove⟩ :=
    source_quintic_second_kernel_span hG T hempty hM hu hmany hcard e H hH hi
  let c := (MulAut.conj g).toMonoidHom
  let D := U.map c
  let Y := Q.map c
  let R := U ⊓ Y
  let Rstar := D ⊓ Q
  let W := conjugateSpanBy R X
  let : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map c
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hQXT : X.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow X (T.subtype hTX)).trans_eq (map_subgroupOf_eq_of_le hTX)
  have hDH : D ≤ H := hDQ.trans (hQXT.trans hH.1.1.2)
  let B := D.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hDH
  let : IsElementaryAbelian 2 (B.map q) := IsElementaryAbelian.map q
  have himage : Nat.card (B.map q) = 2 := by
    have hbound := quintic_elementary_bound
      (Section02.SolvableAmalgam.source_index_five_models
        hG T hempty hM hu hmany hcard e H hH.1 hi) (B.map q)
    have hpos : 0 < Nat.card (B.map q) := Nat.card_pos
    have hne : Nat.card (B.map q) ≠ 1 := by
      intro hone
      have hBQ : B ≤ pCore 2 H := by
        rw [←QuotientGroup.ker_mk' (pCore 2 H)]
        exact (Subgroup.map_eq_bot_iff B).mp (card_eq_one.mp hone)
      apply hescape
      intro d hd
      exact ⟨⟨d,hDH hd⟩,hBQ hd,rfl⟩
    omega
  have hindex : Rstar.relIndex D = 2 := by
    have hiq := relIndex_ker B q
    rw [QuotientGroup.ker_mk',himage] at hiq
    have hh := relIndex_map_map_of_injective (pCore 2 H) B H.subtype_injective
    rw [map_subgroupOf_eq_of_le hDH] at hh
    change Q.relIndex D = (pCore 2 H).relIndex B at hh
    exact (inf_relIndex_left D Q).trans (hh.trans hiq)
  have hDcard : Nat.card D = 32 :=
    (card_map_of_injective (MulAut.conj g).injective).trans
      (source_quintic_span_card_and_core_radical hG T hempty hM hu hmany hcard e H hH hi).1
  have hRstarcard : Nat.card Rstar = 16 := by
    have hh := relIndex_mul_card_of_le (show Rstar ≤ D from inf_le_left)
    rw [hindex,hDcard] at hh
    omega
  have hRmap : R.map c = Rstar := by
    have hWg : W.map (MulAut.conj g).toMonoidHom = W :=
      mem_normalizer_iff_map_conj_eq.mp (hXW hg)
    calc
      R.map c = (W ⊓ U).map c := by rw [hWU]
      _ = W.map c ⊓ U.map c := map_inf _ _ _ (MulAut.conj g).injective
      _ = W ⊓ D := by
        change W.map (MulAut.conj g).toMonoidHom ⊓
          U.map (MulAut.conj g).toMonoidHom = W ⊓ D
        rw [hWg]
      _ = Rstar := hWUstar
  have hRcard : Nat.card R = 16 := by
    have hh := card_map_of_injective (K := R) (f := c) (MulAut.conj g).injective
    rw [hRmap,hRstarcard] at hh
    exact hh.symm
  have hWnotU : ¬ W ≤ U := by
    intro hle
    exact hmove (commutator_eq_bot_iff_le_centralizer.mpr
      ((hRW.trans hle).trans (le_centralizer U)))
  have hWcard : 32 ≤ Nat.card W := by
    have hRle : R ≤ W := le_conjugateSpanBy _ _
    have hh := relIndex_mul_card_of_le hRle
    rw [hRcard] at hh
    have hpos : 0 < R.relIndex W := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hne : R.relIndex W ≠ 1 := by
      intro hone
      exact hWnotU ((relIndex_eq_one.mp hone).trans inf_le_left)
    omega
  let C := H ⊓ centralizer (U : Set G)
  let Z := centralInvolutions T
  let : IsElementaryAbelian 2 W := hWel
  have hWupper : Nat.card W ≤ 32 := source_quintic_elementary_normal_core_card
    hG T hempty hM hu hmany hcard e H hH hi W hWQ hXW
  have hWexact : Nat.card W = 32 := Nat.le_antisymm hWupper hWcard
  have hUQ : U ≤ Q := by
    obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
      hG T hempty hM hu hmany hcard e
    let := he
    obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
    have hh := hl.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [Section02.rankTwoSeed_eq_localModule] using hh
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hH.1.1.2)).trans_eq
      (map_subgroupOf_eq_of_le hH.1.1.2)
  have hcomm : ⁅U,Q⁆ = Z :=
    (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
  have hWZ : ⁅W,U⁆ ≤ Z := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (hWQ.trans inf_le_left)).trans hcomm.le
  have hnonzero : ⁅W,U⁆ ≠ ⊥ := by
    intro hz
    exact hmove (bot_unique ((commutator_mono hRW le_rfl).trans hz.le))
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hWcomm : ⁅W,U⁆ = Z := by
    apply eq_of_le_of_card_ge hWZ
    rw [hZcard]
    have hp : 0 < Nat.card (⁅W,U⁆ : Subgroup G) := Nat.card_pos
    have hn : Nat.card (⁅W,U⁆ : Subgroup G) ≠ 1 :=
      fun h => hnonzero (card_eq_one.mp h)
    omega
  have hZW : Z ≤ W := hWcomm ▸
    le_normalizer_iff_commutator_le_left.mp ((hUQ.trans (hQT.trans le_sup_right)).trans hXW)
  have hRle : R ≤ W := le_conjugateSpanBy _ _
  have hWR : ⁅W,R⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((le_centralizer W).trans (centralizer_le hRle))
  have hRindex : R.relIndex U = 2 := by
    have hh := relIndex_mul_card_of_le (show R ≤ U from inf_le_left)
    rw [hRcard,
      (source_quintic_span_card_and_core_radical hG T hempty hM hu hmany hcard e H hH hi).1] at hh
    omega
  have hUC : U ⊓ centralizer (W : Set G) = R :=
    centralizer_hyperplane_eq U R W Z inf_le_left hRindex
      ((commutator_comm R W).trans hWR) ((commutator_comm U W).trans hWcomm) hZcard
  have hrow : (centralizer (U : Set G)).relIndex W = 2 :=
    binary_row_index_two W U R Z inf_le_left hRindex hWR hWcomm hZW hZcard
  have hWC : W ⊓ C = W ⊓ centralizer (U : Set G) := by
    change W ⊓ (H ⊓ centralizer (U : Set G)) = _
    rw [←inf_assoc,inf_eq_left.mpr ((hWQ.trans inf_le_left).trans (pCoreIn_le 2 H))]
  have hindex : (W ⊓ C).relIndex W = 2 := by
    rw [hWC,inf_relIndex_left]
    exact hrow
  have hkernelcard : 2 * Nat.card (W ⊓ C : Subgroup G) = Nat.card W := by
    have hh := relIndex_mul_card_of_le (show W ⊓ C ≤ W from inf_le_left)
    rwa [hindex] at hh
  have hsmall (hsize : Nat.card W ≤ 32) : W ⊓ C = R ∧ ⁅W,Q⁆ ≤ U := by
    let : IsElementaryAbelian 2 U :=
      (Section02.SolvableAmalgam.source_index_five_closure_structure
        hG T hempty hM hu hmany hcard e H hH.1 hi).1
    have hUCle : U ≤ C := le_inf (hUQ.trans (pCoreIn_le 2 H)) (le_centralizer U)
    have hRWC : R ≤ W ⊓ C := le_inf hRle (inf_le_left.trans hUCle)
    have hRsize : Nat.card R = 16 := hRcard
    have hWCeq : W ⊓ C = R :=
      (eq_of_le_of_card_ge hRWC (by rw [hRsize]; omega)).symm
    obtain ⟨_,hN,hE,_⟩ := source_quintic_full_kernel_elementary_quotient
      hG T hempty hM hu hmany hcard e H hH hi
    let := hN
    let := hE
    have hQQ : ⁅Q,Q⁆ ≤ C := by
      have hh : _root_.commutator Q ≤ C.subgroupOf Q :=
        (Subgroup.Normal.quotient_commutative_iff_commutator_le
          (N := C.subgroupOf Q)).mp inferInstance
      have hm := map_mono (f := Q.subtype) hh
      rw [map_subtype_commutator,subgroupOf_map_subtype] at hm
      exact hm.trans inf_le_left
    refine ⟨hWCeq,?_⟩
    calc
      ⁅W,Q⁆ ≤ W ⊓ C := le_inf
        (le_normalizer_iff_commutator_le_left.mp ((hQT.trans le_sup_right).trans hXW))
        ((commutator_mono (hWQ.trans inf_le_left) le_rfl).trans hQQ)
      _ = R := hWCeq
      _ ≤ U := inf_le_left
  obtain ⟨hWCeq,hWQcomm⟩ := hsmall hWupper
  exact ⟨g,hg,hDQ,hescape,hVI,hTI,hprod,hIQ,hUH,hWel,hWQ,hXW,hWU,hWUstar,
    hRW,hmove,hRcard,hRstarcard,hWexact,hWcomm,hUC,hindex,hkernelcard,hWCeq,hWQcomm⟩

end CFSG.Quasithin.Chapter14.Section06
