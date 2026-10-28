module
public import Theory.GroupTheory.CyclicFourCentralSquares
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Involution fusion over a cyclic center of order four

If the derived subgroup lies in the squares of a cyclic center of order
 four, two noncentral involutions with the same central-quotient image
 are conjugate. Their ratio is the unique central involution. A
 noncommuting element supplies that same involution as a commutator.

Source application: Aschbacher--Smith, 14.3.32(2) and its use in
 14.3.33(3), printed pp.1003--1005.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {A : Type*} [Group A] [Finite A] [IsCyclic (center A)]

/-- Noncentral involutions in one coset of the actual cyclic center fuse. -/
theorem isConj_involutions_of_cyclic_four_center
    (hZ : Nat.card (center A) = 4)
    (hderived : _root_.commutator A ≤ centralSquares A)
    (a b : A) (ha : a ∉ center A) (ha2 : a^2=1) (hb2 : b^2=1)
    (hab : QuotientGroup.mk' (center A) a = QuotientGroup.mk' (center A) b) :
    IsConj a b := by
  by_cases he : a=b
  · exact he ▸ IsConj.refl a
  let d := a⁻¹*b
  have hdZ : d ∈ center A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center A) (a⁻¹*b) = 1
    rw [map_mul,map_inv,hab,inv_mul_cancel]
  have hda : Commute d a := (mem_center_iff.mp hdZ a).symm
  have had : a*d=b := by dsimp [d]; group
  have hc : Commute a b := by rw [←had]; exact Commute.mul_right (Commute.refl a) hda.symm
  have hd2 : d^2=1 := by
    change (a⁻¹*b)^2=1
    rw [hc.inv_left.mul_pow,inv_pow,ha2,hb2,inv_one,mul_one]
  have hd : d ∈ centralSquares A := (mem_centralSquares_iff hZ d).mpr ⟨hdZ,hd2⟩
  have hd1 : d ≠ 1 := by intro hh; exact he (inv_mul_eq_one.mp hh)
  have hn : ∃ c : A, c*a ≠ a*c := by
    by_contra! hh
    exact ha (mem_center_iff.mpr hh)
  obtain ⟨c,hc⟩ := hn
  have hcomm : ⁅c,a⁆ ∈ centralSquares A := hderived (commutator_mem_commutator (mem_top c) (mem_top a))
  have hcomm1 : ⁅c,a⁆ ≠ 1 := fun hh => hc (commutatorElement_eq_one_iff_mul_comm.mp hh)
  obtain ⟨z,_,hall⟩ := (Nat.card_eq_two_iff' (1 : centralSquares A)).mp (centralSquares_card hZ)
  have he : ⁅c,a⁆ = d := congrArg Subtype.val
    ((hall ⟨⁅c,a⁆,hcomm⟩ (fun hh => hcomm1 (congrArg Subtype.val hh))).trans
      (hall ⟨d,hd⟩ (fun hh => hd1 (congrArg Subtype.val hh))).symm)
  apply isConj_iff.mpr
  refine ⟨c,?_⟩
  calc
    c*a*c⁻¹ = ⁅c,a⁆*a := by simp only [commutatorElement_def]; group
    _ = d*a := by rw [he]
    _ = a*d := hda.eq
    _ = b := had
end Theory.GroupTheory
