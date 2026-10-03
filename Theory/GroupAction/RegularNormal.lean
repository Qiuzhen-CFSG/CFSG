module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.SolvableNormalSup
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Group

/-!
# Regular normal subgroups of doubly transitive groups

A nontrivial regular normal subgroup of a finite doubly transitive group is
an elementary abelian p-group. The point stabilizer is transitive on its
nonidentity elements by conjugation, so Cauchy's theorem gives a common prime
order. The nontrivial center of a finite p-group then forces commutativity.
If the point stabilizer is solvable, the ambient group is solvable as well.

Source: the regular-normal-subgroup argument used in Huppert--Blackburn,
*Finite Groups III*, XI.6.1. This module isolates that argument independently
of the Zassenhaus recognition theorems.
-/

namespace MulAction

/-- A nontrivial regular normal subgroup of a finite doubly transitive group
is elementary Abelian. -/
public theorem regular_normal_elementaryAbelian
    {N X : Type*} [Group N] [Finite N] [MulAction N X]
    (htwo : MulAction.IsMultiplyPretransitive N X 2)
    (a : X) (M : Subgroup N) (hMnormal : M.Normal) (hMne : M ≠ ⊥)
    (hMregular :
      ∀ x y : X, ∃! m : M, (m : N) • x = y) :
    ∃ p : ℕ, Nat.Prime p ∧ IsElementaryAbelian p M := by
  classical
  let : M.Normal := hMnormal
  have hmove (m : M) (hm : m ≠ 1) : (m : N) • a ≠ a := by
    intro hma
    obtain ⟨m0, hm0, huniq⟩ := hMregular a a
    have hmm0 : m = m0 := huniq m hma
    have h1m0 : (1 : M) = m0 := huniq 1 (by simp)
    exact hm (hmm0.trans h1m0.symm)
  have hconj_transitive :
      ∀ x y : M, x ≠ 1 → y ≠ 1 →
        ∃ d : N, d * (x : N) * d⁻¹ = (y : N) := by
    intro x y hx hy
    obtain ⟨d, hda, hdxy⟩ :=
      MulAction.is_two_pretransitive_iff.mp htwo
        (hmove x hx) (hmove y hy)
    let xconj : M :=
      ⟨d * (x : N) * d⁻¹,
        hMnormal.conj_mem (x : N) x.property d⟩
    have hdia : d⁻¹ • a = a := by
      calc
        d⁻¹ • a = d⁻¹ • (d • a) := by rw [hdxy]
        _ = a := inv_smul_smul d a
    have hxconj_act : (xconj : N) • a = (y : N) • a := by
      change (d * (x : N) * d⁻¹) • a = (y : N) • a
      rw [mul_smul, mul_smul, hdia]
      exact hda
    obtain ⟨m0, hm0, huniq⟩ := hMregular a ((y : N) • a)
    have hxm0 : xconj = m0 := huniq xconj hxconj_act
    have hym0 : y = m0 := huniq y rfl
    exact ⟨d, congrArg Subtype.val (hxm0.trans hym0.symm)⟩
  let : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hMne
  have hMcard_ne_one : Nat.card M ≠ 1 :=
    ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hMcard_ne_one
  let : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hzne : z ≠ 1 := by
    intro hz
    have : p = 1 := by simpa [hz] using hzorder.symm
    exact hp.ne_one this
  have hprime_order (x : M) (hx : x ≠ 1) : orderOf x = p := by
    obtain ⟨d, hd⟩ := hconj_transitive x z hx hzne
    have hsemi : SemiconjBy d (x : N) (z : N) := by
      change d * (x : N) = (z : N) * d
      calc
        d * (x : N) = (d * (x : N) * d⁻¹) * d := by group
        _ = (z : N) * d := by rw [hd]
    calc
      orderOf x = orderOf (x : N) :=
        (orderOf_injective M.subtype M.subtype_injective x).symm
      _ = orderOf (z : N) := SemiconjBy.orderOf_eq d hsemi
      _ = orderOf z := orderOf_injective M.subtype M.subtype_injective z
      _ = p := hzorder
  have hMp : IsPGroup p M := (IsPGroup.iff_orderOf).2 (by
    intro x
    by_cases hx : x = 1
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [hprime_order x hx]⟩)
  have hMcomm : IsMulCommutative M := by
    let : Nontrivial (Subgroup.center M) := hMp.center_nontrivial
    obtain ⟨zc, hzc⟩ := exists_ne (1 : Subgroup.center M)
    let zM : M := zc
    have hzM_ne : zM ≠ 1 := by
      intro hzM
      apply hzc
      exact Subtype.ext hzM
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    by_cases hx : x = 1
    · simp [hx]
    obtain ⟨d, hd⟩ := hconj_transitive x zM hx hzM_ne
    let ydy : M :=
      ⟨d * (y : N) * d⁻¹,
        hMnormal.conj_mem (y : N) y.property d⟩
    have hz_comm : zM * ydy = ydy * zM :=
      ((Subgroup.mem_center_iff.mp zc.property) ydy).symm
    have hz_comm_N :
        (zM : N) * (d * (y : N) * d⁻¹) =
          (d * (y : N) * d⁻¹) * (zM : N) := by
      simpa [ydy, zM] using congrArg Subtype.val hz_comm
    apply Subtype.ext
    change (x : N) * (y : N) = (y : N) * (x : N)
    calc
      (x : N) * (y : N) =
          d⁻¹ * (zM : N) * d * (y : N) := by
            rw [← hd]
            group
      _ = d⁻¹ * ((zM : N) * (d * (y : N) * d⁻¹)) * d := by
            group
      _ = d⁻¹ * ((d * (y : N) * d⁻¹) * (zM : N)) * d := by
            rw [hz_comm_N]
      _ = (y : N) * (d⁻¹ * (zM : N) * d) := by
            group
      _ = (y : N) * (x : N) := by
            rw [← hd]
            group
  have hMelem : IsElementaryAbelian p M := by
    refine
      { toIsMulCommutative := hMcomm
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_ }
    intro x
    by_cases hx : x = 1
    · simp [hx]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hprime_order x hx]
  exact ⟨p, hp, hMelem⟩

/-- A finite doubly transitive group with a nontrivial regular normal
subgroup and a solvable point stabilizer is solvable. -/
public theorem isSolvable_of_regular_normal_of_isSolvable_stabilizer
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (htwo : IsMultiplyPretransitive G X 2)
    (a : X) [Group.IsSolvable (stabilizer G a)]
    (R : Subgroup G) (hRnormal : R.Normal) (hRne : R ≠ ⊥)
    (hRregular : ∀ x y : X, ∃! r : R, (r : G) • x = y) :
    Group.IsSolvable G := by
  obtain ⟨p, _hp, hR⟩ := regular_normal_elementaryAbelian
    htwo a R hRnormal hRne hRregular
  let : IsElementaryAbelian p R := hR
  let : Group.IsSolvable R := Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  let : R.Normal := hRnormal
  apply Group.isSolvable_of_normal_sup_eq_top R (stabilizer G a)
  apply top_unique
  intro g _
  obtain ⟨r, hr, _⟩ := hRregular a (g • a)
  have hfix : (r : G)⁻¹ * g ∈ stabilizer G a := by
    rw [mem_stabilizer_iff, mul_smul, ← hr, inv_smul_smul]
  have hprod : (r : G) * ((r : G)⁻¹ * g) ∈ R ⊔ stabilizer G a :=
    (R ⊔ stabilizer G a).mul_mem
      (Subgroup.mem_sup_left r.property) (Subgroup.mem_sup_right hfix)
  simpa using hprod

end MulAction
