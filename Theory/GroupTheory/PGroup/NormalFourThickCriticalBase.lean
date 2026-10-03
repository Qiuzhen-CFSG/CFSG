module

public import Theory.GroupTheory.PGroup.CriticalSubgroupOverAbelian
public import Theory.GroupTheory.PGroup.NormalFourInvariantAbelianBase
public import Theory.GroupTheory.PGroup.ClassTwoThreeInvolutionExponent

/-!
# The critical-subgroup reduction for a thick characteristic abelian base

A maximal characteristic abelian subgroup of the centralizer of a normal four
is the center of a critical subgroup. If all critical involutions lie in the
candidate, fusion on the four restricts to the critical subgroup. The
class-two three-involution theorem then forces a nonabelian critical subgroup
to have elementary center, contradicting a candidate of order greater than four.
Thus the candidate is self-centralizing. The involution containment is an
explicit hypothesis here; the normal-eight obstruction is only used in the
original ambient group.

Source: the critical-subgroup construction in Gorenstein, *Finite Groups*,
Theorem 5.3.11, and the three-involution argument toward Janko–Thompson,
Math. Z. 113 (1970), 1.4, printed p.386 and §6, printed p.395.
-/

open Subgroup
open scoped commutatorElement

namespace Subgroup

/-- Involution containment in the prescribed thick center makes the maximal
characteristic abelian candidate self-centralizing. -/
public theorem candidate_selfCentralizing_of_critical_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (A : Subgroup (centralizer (W : Set P))) [A.Characteristic] [IsMulCommutative A]
    (hWA : W ≤ A.map (centralizer (W : Set P)).subtype)
    (hmax : ∀ A' : Subgroup (centralizer (W : Set P)), A'.Characteristic →
      IsMulCommutative A' → A ≤ A' → A' = A)
    (hlarge : 4 < Nat.card A)
    (hinv : ∀ K : Subgroup (centralizer (W : Set P)), IsCriticalPSubgroup 2 K →
      (center K).map K.subtype = A → ∀ x : K, x ^ 2 = 1 → (x : centralizer (W : Set P)) ∈ A) :
    centralizer (A : Set (centralizer (W : Set P))) ≤ A := by
  classical
  let C := centralizer (W : Set P)
  let D := A.map C.subtype
  let : D.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsMulCommutative D := Subgroup.map_isMulCommutative (H := A) C.subtype
  have hO := omega_one_eq_normal_four_of_no_normal_eight hno W D hW hWA
  have hAmem (x : A) (hx : (x : C) ^ 2 = 1) : ((x : C) : P) ∈ W := by
    apply hO.le
    refine ⟨⟨x, mem_map_of_mem C.subtype x.property⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val hx
  obtain ⟨K, hK, hKA⟩ := (hP.to_subgroup C).exists_criticalPSubgroup_with_center A hmax
  let : K.Characteristic := hK.characteristic
  have hAK : A ≤ K := hKA ▸ map_subtype_le (center K)
  have hmem (x : K) (hx : x ^ 2 = 1) : ((x : C) : P) ∈ W :=
    hAmem ⟨x, hinv K hK hKA x hx⟩ (congrArg Subtype.val hx)
  have hcentral (x : K) (hx : x ^ 2 = 1) : x ∈ center K := by
    have hh : (x : C) ∈ (center K).map K.subtype := hKA.symm ▸ hinv K hK hKA x hx
    obtain ⟨z, hz, he⟩ := hh
    exact (Subtype.ext he : z = x) ▸ hz
  have hKtrans : ∀ x y : K, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut K, a x = y := by
    intro x y hx hy
    obtain ⟨a, ha⟩ := htrans x y
      (hmem x (by simpa only [hx] using pow_orderOf_eq_one x))
      (hmem y (by simpa only [hy] using pow_orderOf_eq_one y))
      ((orderOf_coe x).trans hx) ((orderOf_coe y).trans hy)
    exact ⟨MulAut.characteristic K a, Subtype.ext ha⟩
  have hWK (w : W) : (⟨w, le_centralizer W w.property⟩ : C) ∈ K := by
    obtain ⟨a, ha, he⟩ := hWA w.property
    have he' : a = (⟨w, le_centralizer W w.property⟩ : C) := Subtype.ext he
    exact he' ▸ hAK ha
  have hthree : Nat.card {x : K // orderOf x = 2} = 3 := by
    let e : {x : K // orderOf x = 2} ≃ {w : W // w ≠ 1} :=
      { toFun := fun x => ⟨⟨x.val, hmem x.val (by
          simpa only [x.property] using pow_orderOf_eq_one x.val)⟩,
          fun he => (orderOf_eq_prime_iff.mp x.property).2
            (Subtype.ext (Subtype.ext (congrArg (fun w : W => (w : P)) he)))⟩
        invFun := fun w => ⟨⟨⟨w.val, le_centralizer W w.val.property⟩, hWK w.val⟩,
          orderOf_eq_prime (by
            apply Subtype.ext
            apply Subtype.ext
            exact elemPow_eq_one_of_isElementaryAbelian _ w.val.property)
            (fun he => w.property (Subtype.ext (congrArg (fun x : K => ((x : C) : P)) he)))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let : Fintype W := Fintype.ofFinite W
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, hW]
    simp
  have hab : IsMulCommutative K := by
    by_contra hnab
    have hclass : _root_.commutator K ≤ center K := by
      apply Subgroup.commutator_le.mpr
      intro x _ y _
      obtain ⟨z, hz, he⟩ := hK.commutator_le
        (commutator_mem_commutator (mem_top (x : C)) y.property)
      exact (Subtype.ext he : z = ⁅x, y⁆) ▸ hz
    have hexp := ((hP.to_subgroup C).to_subgroup K).exponent_four_of_class_two_of_transitive_three_involutions
      hnab hcentral hthree hKtrans hclass
    obtain ⟨_, _, hel, _⟩ := ((hP.to_subgroup C).to_subgroup K).special_of_exponent_four_of_transitive_involutions
      hnab hcentral hKtrans hexp
    let : IsElementaryAbelian 2 (center K) := hel
    let : IsElementaryAbelian 2 ((center K).map K.subtype) := IsElementaryAbelian.map_subtype
    have hAW : D ≤ W := by
      rintro _ ⟨a, ha, rfl⟩
      apply hAmem ⟨a, ha⟩
      exact elemPow_eq_one_of_isElementaryAbelian (A := (center K).map K.subtype) a (hKA.symm ▸ ha)
    have hc : Nat.card A ≤ 4 := calc
      Nat.card A = Nat.card D := (card_map_of_injective C.subtype_injective).symm
      _ ≤ Nat.card W := card_le_of_le hAW
      _ = 4 := hW
    exact (not_le_of_gt hlarge) hc
  let : IsMulCommutative K := hab
  have hKeq : K = A := hmax K inferInstance inferInstance hAK
  simpa only [hKeq, hKA] using hK.centralizer_eq.le

/-- Conjugation by the four-centralizer moves critical involutions only by
an element of the normal four. This does not assert centrality of the involution. -/
public theorem critical_involution_displacement_mem_four {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (A : Subgroup (centralizer (W : Set P))) [A.Characteristic] [IsMulCommutative A]
    (hWA : W ≤ A.map (centralizer (W : Set P)).subtype)
    (K : Subgroup (centralizer (W : Set P))) (hK : IsCriticalPSubgroup 2 K)
    (hKA : (center K).map K.subtype = A)
    (x : K) (hx : x ^ 2 = 1) (g : centralizer (W : Set P)) :
    ((⁅g, (x : centralizer (W : Set P))⁆ : centralizer (W : Set P)) : P) ∈ W := by
  let C := centralizer (W : Set P)
  let D := A.map C.subtype
  let : D.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsMulCommutative D := Subgroup.map_isMulCommutative (H := A) C.subtype
  have hO := omega_one_eq_normal_four_of_no_normal_eight hno W D hW hWA
  obtain ⟨z, hz, he⟩ := hK.commutator_le
    (commutator_mem_commutator (mem_top g) x.property)
  have hcomm : (x : C) * ⁅g, (x : C)⁆ = ⁅g, (x : C)⁆ * (x : C) := by
    rw [← he]
    exact congrArg Subtype.val (mem_center_iff.mp hz x)
  have hpow : ⁅g, (x : C)⁆ ^ 2 = 1 := by
    have hh : ⁅g, (x : C) ^ 2⁆ = ⁅g, (x : C)⁆ ^ 2 := by
      rw [pow_two, commutatorElement_mul_right_eq_mul_conj, mul_assoc _ (x : C), hcomm,
        ← mul_assoc, mul_inv_cancel_right, pow_two]
    have hxC : (x : C) ^ 2 = 1 := congrArg Subtype.val hx
    rw [hxC, commutatorElement_one_right] at hh
    exact hh.symm
  have hm : ⁅g, (x : C)⁆ ∈ A := hKA ▸ ⟨z, hz, he⟩
  apply hO.le
  refine ⟨⟨((⁅g, (x : C)⁆ : C) : P), mem_map_of_mem C.subtype hm⟩, subset_closure ?_, rfl⟩
  apply Subtype.ext
  simpa using congrArg Subtype.val hpow

end Subgroup
