module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.ActionConstruction.Choice
public import Theory.GroupTheory.CyclicTwoSubgroups.Cardinality

/-!
# The maximizing involution action on the rotations

For the chosen generator `y` and maximizing candidate `w`, either `w` centralizes
all of the commuting Sylow subgroup, or `y` has order greater than four and
conjugation by `w` sends `y` to `y*z`, with the original central involution `z`.

The cyclic two-group subgroup chain turns the maximizing cardinality comparison
into `C_Y(t*w) ≤ C_Y(w)`. The element `y * y^(t*w)` is fixed by `t*w`, hence also
by `w` and by `t`. The known four-centralizer and uniqueness of the cyclic
involution make this element either `1` or `z`. Composing with the already
proved inversion or semidihedral action of `t` gives the two actions for `w`.
When `y` has order four, the noncentralizing action cannot be maximizing.

This proves the action alternative used in Aschbacher--Smith, combined
manuscript of 1 March 2004, Lemma 16.3.12, printed pp.1181--1182 / PDF
pp.1198--1199. The dihedral-factor and Thompson-subgroup assemblies are separate.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation.ActionConstruction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}
variable (d : Prepared T z t L) (a : RotationChoice d)

omit [Finite G] in
private theorem fixed_iff (x v : G) : x⁻¹ * v * x = v ↔ Commute v x := by
  constructor
  · intro h
    change v * x = x * v
    have he := congrArg (fun r => x * r) h
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he
  · intro h
    calc
      _ = x⁻¹ * (v * x) := mul_assoc _ _ _
      _ = x⁻¹ * (x * v) := congrArg (x⁻¹ * ·) h.eq
      _ = v := inv_mul_cancel_left _ _

private theorem other_fixed_le :
    zpowers a.y ⊓ involutionCentralizer (t * a.w) ≤
      zpowers a.y ⊓ involutionCentralizer a.w := by
  exact le_of_card_le_of_le_zpowers_two_pow (a.order ▸ pow_orderOf_eq_one a.y) _ _ inf_le_left inf_le_left
    (a.maximizing _ (a.other_candidate d))

private theorem reflection_fixed {x : G} (hx : x ∈ zpowers a.y)
    (hxt : Commute x t) : x = 1 ∨ x = z := by
  let := (EnlargementSieve.four_group d.counterexample).1
  have hxE : x ∈ zpowers z ⊔ zpowers t := d.shape.centralizer_eq ▸
    ⟨a.rotation_le hx, mem_centralizer_singleton_iff.mpr hxt.eq⟩
  have hd := orderOf_dvd_of_pow_eq_one
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hxE)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact Or.inl (orderOf_eq_one_iff.mp h1)
  · right
    exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨x, hx⟩ : zpowers a.y)) (y := (⟨z, a.z_mem d⟩ : zpowers a.y))
      ((orderOf_coe _).symm.trans h2)
      ((orderOf_coe _).symm.trans d.counterexample.localSetup.involution))

private theorem other_action :
    (t * a.w)⁻¹ * a.y * (t * a.w) = a.y⁻¹ ∨
      (t * a.w)⁻¹ * a.y * (t * a.w) = a.y⁻¹ * z := by
  let b := t * a.w
  have hb2 : b * b = 1 := by
    have ho : orderOf b = 2 := candidate_order d (a.other_candidate d)
    simpa only [ho, pow_two] using pow_orderOf_eq_one b
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbY : b⁻¹ * a.y * b ∈ zpowers a.y :=
    (mem_normalizer_iff''.mp (a.candidate_normalizes d (a.other_candidate d)) a.y).mp
      (mem_zpowers _)
  have hc : Commute a.y (b⁻¹ * a.y * b) := by
    obtain ⟨i, hi⟩ := hbY
    rw [← hi]
    exact Commute.self_zpow _ _
  let q := a.y * (b⁻¹ * a.y * b)
  have hqY : q ∈ zpowers a.y := mul_mem (mem_zpowers _) hbY
  have hqb : Commute q b := (fixed_iff b q).mp (by
    calc
      _ = (b⁻¹ * a.y * b) * (b⁻¹ * (b⁻¹ * a.y * b) * b) := by dsimp [q]; group
      _ = (b⁻¹ * a.y * b) * a.y := by
        congr 1
        rw [hbi]
        calc
          b * (b * a.y * b) * b = (b * b) * a.y * (b * b) := by group
          _ = a.y := by rw [hb2]; simp
      _ = q := hc.eq.symm)
  have hqw : Commute q a.w := mem_centralizer_singleton_iff.mp
    (other_fixed_le d a ⟨hqY, mem_centralizer_singleton_iff.mpr hqb.eq⟩).2
  have hqt : Commute q t := by
    have h := hqb.mul_right hqw.inv_right
    simpa only [b, mul_inv_cancel_right] using h
  rcases reflection_fixed d a hqY hqt with hq | hq
  · left
    exact eq_inv_of_mul_eq_one_right hq
  · right
    have h := congrArg (a.y⁻¹ * ·) hq
    simpa only [q, inv_mul_cancel_left] using h

private theorem action_cases : a.w⁻¹ * a.y * a.w = a.y ∨
    a.w⁻¹ * a.y * a.w = a.y * z := by
  let b := t * a.w
  have ht2 : t * t = 1 := by
    simpa only [d.counterexample.involution, pow_two] using pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hzb : Commute z b :=
    (mem_centralizer_singleton_iff.mp
      (d.counterexample.localSetup.sylow_centralizes
        (candidate_mem_and_centralizes d (a.other_candidate d)).1)).symm
  have hbz : b⁻¹ * z * b = z := (fixed_iff b z).mpr hzb
  have hz2 : z * z = 1 := by
    simpa only [d.counterexample.localSetup.involution, pow_two] using pow_orderOf_eq_one z
  have hyz : Commute a.y z := by
    obtain ⟨k, hk⟩ := a.z_mem d
    exact (congrArg (fun v : G => Commute a.y v) hk).mp (Commute.self_zpow a.y k)
  have hcompose : a.w⁻¹ * a.y * a.w = b⁻¹ * (t⁻¹ * a.y * t) * b := by
    dsimp [b]
    rw [mul_inv_rev, hti]
    calc
      _ = a.w⁻¹ * ((t * t) * a.y * (t * t)) * a.w := by rw [ht2]; simp
      _ = _ := by group
  have hinv (v : G) : b⁻¹ * v⁻¹ * b = (b⁻¹ * v * b)⁻¹ := by group
  have hmul (v r : G) : b⁻¹ * (v * r) * b =
      (b⁻¹ * v * b) * (b⁻¹ * r * b) := by group
  rcases a.reflection_action d with ⟨_, ht⟩ | ⟨_, ht⟩ <;>
    rcases other_action d a with hb | hb
  · left
    rw [hcompose, ht, hinv, hb, inv_inv]
  · right
    rw [hcompose, ht, hinv, hb, mul_inv_rev,
      inv_eq_of_mul_eq_one_right hz2, inv_inv, hyz.eq]
  · right
    rw [hcompose, ht, hmul, hinv, hb, hbz, inv_inv]
  · left
    rw [hcompose, ht, hmul, hinv, hb, hbz, mul_inv_rev,
      inv_eq_of_mul_eq_one_right hz2, inv_inv, ← hyz.eq, mul_assoc, hz2, mul_one]

private theorem order_four_fixes (ho : orderOf a.y = 4) : a.w⁻¹ * a.y * a.w = a.y := by
  have he : a.exponent = 2 := by
    have hlo := a.exponent_ge
    have hup : a.exponent < 3 := by
      by_contra hn
      have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ a.exponent by omega)
      rw [← a.order, ho] at h
      norm_num at h
    omega
  have hz : a.y ^ 2 = z := by simpa only [he, Nat.reduceSub, pow_one] using a.halfTurn d
  have hneg : a.y⁻¹ * z = a.y := by
    calc
      _ = a.y⁻¹ * a.y ^ 2 := congrArg (a.y⁻¹ * ·) hz.symm
      _ = a.y := by group
  have ht : t⁻¹ * a.y * t = a.y⁻¹ := by
    rcases a.reflection_action d with ⟨_, ht⟩ | ⟨_, ht⟩
    · exact ht
    · have hc : Commute a.y t := (fixed_iff t a.y).mp (ht.trans hneg)
      rcases reflection_fixed d a (mem_zpowers _) hc with h1 | h1
      · have h := congrArg orderOf h1
        rw [ho, orderOf_one] at h
        contradiction
      · have h := congrArg orderOf h1
        rw [ho, d.counterexample.localSetup.involution] at h
        contradiction
  rcases other_action d a with hb | hb
  · have hh : (t * a.w)⁻¹ * a.y * (t * a.w) =
        (a.w⁻¹ * a.y * a.w)⁻¹ := by
      calc
        _ = a.w⁻¹ * (t⁻¹ * a.y * t) * a.w := by group
        _ = a.w⁻¹ * a.y⁻¹ * a.w := by rw [ht]
        _ = _ := by group
    exact inv_injective (hh.symm.trans hb)
  · have hc : Commute a.y (t * a.w) := (fixed_iff _ _).mp (hb.trans hneg)
    exact (fixed_iff _ _).mpr (mem_centralizer_singleton_iff.mp
      (other_fixed_le d a ⟨mem_zpowers _, mem_centralizer_singleton_iff.mpr hc.eq⟩).2)

/-- The maximizing involution has the source centralizing or modular action. -/
theorem maximizing_action_cases :
    a.w ∈ Subgroup.centralizer (commutingSylow T L : Set G) ∨
      (4 < orderOf a.y ∧ a.w⁻¹ * a.y * a.w = a.y * z) := by
  rcases action_cases d a with hfix | htwist
  · exact Or.inl (a.centralizes_of_fixes d hfix)
  · by_cases hlarge : 4 < orderOf a.y
    · exact Or.inr ⟨hlarge, htwist⟩
    · have hlo : 4 ≤ orderOf a.y := a.order ▸
        Nat.pow_le_pow_right (by decide : 0 < 2) a.exponent_ge
      exact Or.inl (a.centralizes_of_fixes d (order_four_fixes d a (by omega)))

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation.ActionConstruction
