module

public import Stellmacher.Recognition.SuzukiThreeSquareAction
public import Stellmacher.Recognition.SuzukiThreeSmallInvolutionCount
public import Stellmacher.Recognition.SuzukiThreeLargeInvolutionCount
import Mathlib.Tactic

/-!
# The involution census in the centralising-swap branch

The small and large Bruhat cells contain nine and 54 involutions respectively.
The torus involution already has a conjugacy class of size 63, so this class
exhausts all involutions. The class-size formula then gives centralizer order
96 for every involution. The unique-involution interface for the cyclic
two-point stabilizer is re-exported from the centralizer calculation.

Source: Suzuki (1965), Section II, Lemmas 1–3.
-/

namespace Stellmacher.Recognition

/-- The numerical end of Suzuki's involution census. -/
public theorem suzuki_three_census_arithmetic
    (s e : Nat) (hs : s ∣ 27) (hs27 : s ≠ 27)
    (he : e = 0 ∨ e = 1 ∨ e = 2)
    (hcount : 28 = (s + 1) * (1 + e * s)) :
    s = 3 ∧ e = 2 := by
  obtain ⟨k, hk, rfl⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp (show s ∣ 3 ^ 3 from hs)
  interval_cases k <;> norm_num at * <;> omega

namespace SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

private theorem commute_of_centralizing_swap (t k : G)
    (hk : t⁻¹ * k * t = k) : Commute k t := by
  change k * t = t * k
  calc
    _ = t * (t⁻¹ * k * t) := by group
    _ = _ := by rw [hk]

include h

/-- The two Bruhat cells together contain exactly 63 involutions. -/
public theorem involution_card_of_centralizing_swap [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (ht : t ^ 2 = 1)
    (hta : t • a = b) (htb : t • b = a)
    (hcentral : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G)) :
    Nat.card {x : G // orderOf x = 2} = 63 := by
  classical
  let : Finite G := h.finite_group
  have hc := Nat.card_congr (Equiv.sumCompl
    (fun x : {x : G // orderOf x = 2} => x.val ∈ stabilizer G a))
  rw [Nat.card_sum,
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun x : G => orderOf x = 2) (fun x => x ∈ stabilizer G a)),
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun x : G => orderOf x = 2) (fun x => x ∉ stabilizer G a)),
    h.stabilizer_involution_card b hb t ht hta htb
      (fun k => (commute_of_centralizing_swap t _ (hcentral k)).symm),
    h.large_involution_card_of_centralizing_swap b hb t ht hta htb hcentral] at hc
  exact hc.symm

private theorem involution_isConj_torus [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (ht : t ^ 2 = 1)
    (hta : t • a = b) (htb : t • b = a)
    (hcentral : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (j : stabilizer (stabilizer G a) b) (hj : orderOf (j : G) = 2)
    (x : G) (hx : orderOf x = 2) : IsConj x (j : G) := by
  let : Finite G := h.finite_group
  let J := (ConjClasses.mk (j : G)).carrier
  let f : J → {x : G // orderOf x = 2} := fun y => ⟨y.val, by
    have hy : IsConj y.val (j : G) := ConjClasses.mk_eq_mk_iff_isConj.mp
      (ConjClasses.mem_carrier_iff_mk_eq.mp y.property)
    obtain ⟨g, hg⟩ := isConj_iff.mp hy
    have he := (MulAut.conj g).orderOf_eq y.val
    change orderOf (g * y.val * g⁻¹) = orderOf y.val at he
    rw [hg] at he
    exact he.symm.trans hj⟩
  have hinj : Function.Injective f := by
    intro y z he
    exact Subtype.ext (congrArg (fun w : {x : G // orderOf x = 2} => w.val) he)
  have hcard : Nat.card J = Nat.card {x : G // orderOf x = 2} := by
    rw [h.involution_card_of_centralizing_swap b hb t ht hta htb hcentral]
    exact h.torus_involution_conjugacyClass_card b hb t hta htb j hj
      (commute_of_centralizing_swap t _ (hcentral j))
  obtain ⟨y, hy⟩ := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩).surjective
    ⟨x, hx⟩
  have he : y.val = x := congrArg Subtype.val hy
  exact he ▸ ConjClasses.mk_eq_mk_iff_isConj.mp
    (ConjClasses.mem_carrier_iff_mk_eq.mp y.property)

/-- All involutions are conjugate when the involutory point swap centralizes
the two-point stabilizer. -/
public theorem involutions_isConj_of_centralizing_swap [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (ht : t ^ 2 = 1)
    (hta : t • a = b) (htb : t • b = a)
    (hcentral : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨j, hj, _⟩ := h.twoPoint_exists_unique_involution b hb
  exact (h.involution_isConj_torus b hb t ht hta htb hcentral j hj x hx).trans
    (h.involution_isConj_torus b hb t ht hta htb hcentral j hj y hy).symm

/-- Every involution has centralizer order 96 when the involutory point swap
centralizes the two-point stabilizer. -/
public theorem involution_centralizer_card_of_centralizing_swap [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (ht : t ^ 2 = 1)
    (hta : t • a = b) (htb : t • b = a)
    (hcentral : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (x : G) (hx : orderOf x = 2) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = 96 := by
  obtain ⟨j, hj, _⟩ := h.twoPoint_exists_unique_involution b hb
  have he := ConjClasses.mk_eq_mk_iff_isConj.mpr
    (h.involution_isConj_torus b hb t ht hta htb hcentral j hj x hx)
  have hc := ConjClasses.nat_card_carrier_mul_card_centralizer x
  rw [he, h.torus_involution_conjugacyClass_card b hb t hta htb j hj
    (commute_of_centralizing_swap t _ (hcentral j)), h.group_card] at hc
  omega

end SuzukiThreeHypotheses

end Stellmacher.Recognition
