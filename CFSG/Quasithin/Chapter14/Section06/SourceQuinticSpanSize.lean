module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSecondKernelSpan
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSpanOrder
import all CFSG.Quasithin.Chapter14.Section06.SourceQuinticHyperplanes

/-!
# Orders of the original reciprocal intersections

The escaping elementary span has image of order two in the whole quintic
quotient. Its core intersection therefore has order sixteen. Conjugation by
the same selected element preserves W and carries W intersect UH to
W intersect UHstar, giving the reciprocal order without replacing the
conjugator. Nonzero reciprocal movement makes W strictly larger than either
order-sixteen intersection, so W has order at least thirty-two.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_quintic_second_kernel_span_size
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
    ∃ g ∈ X,
      let Ustar := U.map (MulAut.conj g).toMonoidHom
      let Qstar := (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom
      let R := U ⊓ Qstar
      let Rstar := Ustar ⊓ H.pCoreIn 2
      let W := conjugateSpanBy R X
      IsElementaryAbelian 2 W ∧ W ≤ H.pCoreIn 2 ⊓ X.pCoreIn 2 ∧
        X ≤ normalizer (W : Set G) ∧ W ⊓ U = R ∧ W ⊓ Ustar = Rstar ∧
        Rstar ≤ W ∧ ⁅Rstar,U⁆ ≠ ⊥ ∧
        Nat.card R = 16 ∧ Nat.card Rstar = 16 ∧ 32 ≤ Nat.card W := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  obtain ⟨g,hg,hDQ,hescape,_,_,_,_,_,hWel,hWQ,hXW,hWU,hRW,hWUstar,hmove⟩ :=
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
  exact ⟨g,hg,hWel,hWQ,hXW,hWU,hWUstar,hRW,hmove,hRcard,hRstarcard,hWcard⟩

end CFSG.Quasithin.Chapter14.Section06
