module

public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index

/-!
# Extraspecial normal closures of elementary abelian subgroups

Let E be the normal closure of an elementary abelian two-subgroup A. If E/Z(E)
is abelian, it is elementary abelian: each generating conjugate of A has exponent
two, and exponent two is preserved under products in the abelian quotient.

If A is self-centralizing in E, then Z(E) lies in A. Thus an order-two fixed
subgroup C_A(E) identifies the whole center. When |A| > 2 the central quotient
is nontrivial, so E is extraspecial.

This is the intrinsic group-theoretic step in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript (1 March 2004), Lemma 8.2.12,
printed p.722. The action, order and plus-type calculations are separate inputs
in that application; this criterion does not assert them.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup
variable {C : Type*} [Group C]

/-- An abelian central quotient of a normal closure of an elementary two-group
is elementary abelian. -/
public theorem normalClosure_centerQuotient_elementary (A : Subgroup C) [IsElementaryAbelian 2 A]
    (hab : IsMulCommutative ((normalClosure (A : Set C)) ⧸
      center (normalClosure (A : Set C)))) :
    IsElementaryAbelian 2 ((normalClosure (A : Set C)) ⧸
      center (normalClosure (A : Set C))) := by
  let E := normalClosure (A : Set C)
  let q := QuotientGroup.mk' (center E)
  let := hab
  have hp (x : C) (hx : x ∈ E) : q ⟨x, hx⟩ ^ 2 = 1 := by
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      have hx2 : x ^ 2 = 1 := by
        have ha2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
        simpa only [ha2, isConj_one_right] using hax.pow 2
      have : (⟨x, Subgroup.conjugatesOfSet_subset_normalClosure hx⟩ : E) ^ 2 = 1 :=
        Subtype.ext hx2
      rw [← map_pow, this, map_one]
    | one => change q 1 ^ 2 = 1; rw [map_one, one_pow]
    | mul x y hx hy ihx ihy =>
      change (q ⟨x, hx⟩ * q ⟨y, hy⟩) ^ 2 = 1
      rw [mul_pow, ihx, ihy, one_mul]
    | inv x hx ih =>
      change (q ⟨x, hx⟩)⁻¹ ^ 2 = 1
      rw [inv_pow, ih, inv_one]
  refine { toIsMulCommutative := hab, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  induction x using QuotientGroup.induction_on with
  | H x => exact hp x x.property

/-- If the seed is self-centralizing in its normal closure and has exactly two
fixed points there, an abelian central quotient makes that closure extraspecial.
The seed has order greater than two, excluding an abelian closure. -/
public theorem normalClosure_isExtraspecial_of_local_centralizers [Finite C] (A : Subgroup C)
    [IsElementaryAbelian 2 A]
    (hab : IsMulCommutative ((normalClosure (A : Set C)) ⧸
      center (normalClosure (A : Set C))))
    (hself : centralizer (A.subgroupOf (normalClosure (A : Set C)) :
      Set (normalClosure (A : Set C))) ≤ A.subgroupOf (normalClosure (A : Set C)))
    (hfixed : Nat.card (A.subgroupOf (normalClosure (A : Set C)) ⊓
      center (normalClosure (A : Set C)) : Subgroup (normalClosure (A : Set C))) = 2)
    (hlarge : 2 < Nat.card A) : IsExtraspecial 2 (normalClosure (A : Set C)) := by
  let E := normalClosure (A : Set C)
  let W := A.subgroupOf E
  have hZE : center E ≤ W := (center_le_centralizer (W : Set E)).trans hself
  have hc : Nat.card (center E) = 2 := by
    change Nat.card (W ⊓ center E : Subgroup E) = 2 at hfixed
    rwa [inf_eq_right.mpr hZE] at hfixed
  refine ⟨hc, normalClosure_centerQuotient_elementary A hab, QuotientGroup.nontrivial_iff.mpr ?_⟩
  intro htop
  change center E = ⊤ at htop
  have hcardE : Nat.card E = 2 := by simpa only [htop, card_top] using hc
  have hcardW : Nat.card W = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe (le_normalClosure (H := A))).toEquiv
  have hle := Nat.card_le_card_of_injective W.subtype W.subtype_injective
  rw [hcardW, hcardE] at hle
  exact (not_le_of_gt hlarge) hle


end Subgroup
