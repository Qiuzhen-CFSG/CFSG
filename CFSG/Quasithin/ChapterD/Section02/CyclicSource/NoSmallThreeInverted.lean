module
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportOrders
public import Theory.GroupTheory.Fitting.Core
/-!
# Inverted elements without small cubic supports

The support bound and full-support identities determine every nontrivial
three-core element inverted by a small-support involution. Its order is
three, its support has order sixteen, and the involution fixes its entire
fixed-point complement. This is Aschbacher–Smith D.2.26(1), p.191.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterD

variable {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
  [IsElementaryAbelian 2 V] [MulDistribMulAction G V]

/-- The no-three-support part of D.2.26. An order-three cyclic factor of the
odd Fitting core inverted by a small-support involution has full support.
The equality and centralizer clauses are the literal full-support identities
of D.2.11(3), specialized to this source factor. -/
theorem cyclic_no_three_support_D_2_26
    (x t : G) (hx : x ≠ 1) (hx3 : orderOf x = 3)
    (hxP : x ∈ pCore 3 G) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (htcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 4)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Nat.card (commutatorAction X V) ≠ 4) :
    Nat.card (commutatorAction (Subgroup.zpowers x) V) = 16 ∧
      commutatorAction (Subgroup.zpowers t) V =
        commutatorSubgroup (Subgroup.zpowers t) V
          (commutatorAction (Subgroup.zpowers x) V) ∧
      (∀ v ∈ FixedPoints.subgroup (Subgroup.zpowers x) V, t • v = v) ∧
      ∀ y : G, Commute y x →
        (∀ v ∈ commutatorAction (Subgroup.zpowers x) V, y • v = v) → Commute y t := by
  have hodd : Odd (orderOf x) := by rw [hx3]; decide
  have hsupport := invertedOddElement_support_card_four_or_sixteen
    x t hx hodd ht hinv htcard.le hfaith
  have hXle : Subgroup.zpowers x ≤ pCore 3 G := zpowers_le.mpr hxP
  have hXcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hx3]
  have hnot4 : Nat.card (commutatorAction (Subgroup.zpowers x) V) ≠ 4 := by
    intro h4
    exact hNo (Subgroup.zpowers x) hXle hXcard h4
  have h16 : Nat.card (commutatorAction (Subgroup.zpowers x) V) = 16 := by
    rcases hsupport with h4 | h16
    · exact (hnot4 h4).elim
    · exact h16
  have hfull := invertedOddElement_full_support x t hodd ht hinv
    (by rw [h16, htcard]; norm_num) hfaith
  exact ⟨h16, hfull.1, hfull.2.1, hfull.2.2⟩

end CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.ChapterD
open Subgroup
variable {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
  [IsElementaryAbelian 2 V] [MulDistribMulAction G V]

/-- The no-small-three reduction also determines the order of every
nonidentity element of the three-core inverted by a source involution. -/
theorem inverted_threeCore_no_small_support
    (x t : G) (hx : x ≠ 1) (hxP : x ∈ pCore 3 G) (ht : IsInvolution t)
    (hinv : t * x * t⁻¹ = x⁻¹)
    (htcard : Nat.card (commutatorAction (zpowers t) V) = 4)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Nat.card (commutatorAction X V) ≠ 4) :
    orderOf x = 3 ∧ Nat.card (commutatorAction (zpowers x) V) = 16 ∧
      commutatorAction (zpowers t) V =
        commutatorSubgroup (zpowers t) V (commutatorAction (zpowers x) V) ∧
      (∀ v ∈ FixedPoints.subgroup (zpowers x) V, t • v = v) ∧
      ∀ y : G, Commute y x →
        (∀ v ∈ commutatorAction (zpowers x) V, y • v = v) → Commute y t := by
  have hP : IsPGroup 3 (pCore 3 G) := pCore_isPGroup
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have ho : Odd (orderOf x) :=
    (show Odd (Nat.card (pCore 3 G)) by rw [hn]; exact (by decide : Odd 3).pow).of_dvd_nat
      ((pCore 3 G).orderOf_dvd_natCard hxP)
  have hdiv : 3 ∣ orderOf x := by
    have hd := hP.dvd_orderOf (g := (⟨x,hxP⟩ : pCore 3 G))
      (fun he => hx (congrArg Subtype.val he))
    simpa only [← Subgroup.orderOf_coe] using hd
  have hx3 : orderOf x = 3 := by
    rcases invertedOddElement_order_three_or_five_of_small_involution_support
      x t hx ho ht hinv htcard.le hfaith with h3 | h5
    · exact h3
    · rw [h5] at hdiv
      norm_num at hdiv
  exact ⟨hx3,cyclic_no_three_support_D_2_26 x t hx hx3 hxP ht hinv htcard hfaith hNo⟩

end CFSG.Quasithin.ChapterD
