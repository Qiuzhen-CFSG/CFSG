module
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers
import Mathlib.Tactic.Group

/-!
# Centerlessness of the concrete Rudvalis model

The ambient centralizer of the certified 2A centralizer has order at most two.
It contains the marked involution, which is not central: a checked conjugation
sends it to b², while the standard relations a²=1, b⁴=1 and (ab)¹³=1 rule out
centrality of b². Hence every nonidentity element of the model center would
have to equal a noncentral marked involution, a contradiction.

This uses only the existing word alignment and centralizer bound, without
assuming simplicity of the concrete carrier. Its source consumer is the
marked Rudvalis fixed-group exclusion in Aschbacher--Smith 14.2.15, printed
pp.985--986. The generator and ATLAS certificate sources are recorded in
Model.Basic and Model.LowCentralizers.
-/

public section

open Subgroup
namespace Rudvalis.LowCentralizers
open SylowOvergroups
open SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate

private theorem square_not_central_of_relations {G : Type*} [Group G]
    (a b : G) (ha2 : a ^ 2 = 1) (hb4 : b ^ 4 = 1)
    (hab13 : (a * b) ^ 13 = 1) (hb2 : b ^ 2 ≠ 1) : b ^ 2 ∉ center G := by
  intro h
  have ha : a⁻¹ = a := by
    calc
      a⁻¹ = a⁻¹ * a ^ 2 := by rw [ha2, mul_one]
      _ = a := by group
  have hc : a * b ^ 2 = b ^ 2 * a := mem_center_iff.mp h a
  have he : b * a = (a * b)⁻¹ * b ^ 2 := by
    rw [mul_inv_rev, ha]
    calc
      b * a = b⁻¹ * (b ^ 2 * a) := by group
      _ = b⁻¹ * (a * b ^ 2) := by rw [hc]
      _ = b⁻¹ * a * b ^ 2 := (mul_assoc _ _ _).symm
  have hd : MulAut.conj b (a * b) = b * a := by
    change b * (a * b) * b⁻¹ = b * a
    group
  have hp : (b * a) ^ 13 = 1 := by
    rw [← hd, ← map_pow, hab13, map_one]
  have hcomm : Commute (a * b) (b ^ 2) := mem_center_iff.mp h (a * b)
  rw [he, hcomm.inv_left.mul_pow, inv_pow, hab13, inv_one, one_mul,
    ← pow_mul] at hp
  have hb : b ^ 2 = 1 := by
    calc
      b ^ 2 = (b ^ 4) ^ 6 * b ^ 2 := by rw [hb4, one_pow, one_mul]
      _ = b ^ 26 := by group
      _ = 1 := hp
  exact hb2 hb

private theorem b_square_not_central : b ^ 2 ∉ center Model := by
  apply square_not_central_of_relations a b a_sq b_fourth ab_thirteenth
  intro hb
  have hn := orderOf_dvd_of_pow_eq_one hb
  rw [orderOf_b] at hn
  norm_num at hn

private theorem conjugation_fixes_central {G : Type*} [Group G] (g z : G)
    (hz : z ∈ center G) : MulAut.conj g z = z := by
  change g * z * g⁻¹ = z
  rw [mem_center_iff.mp hz g, mul_assoc, mul_inv_cancel, mul_one]

private theorem marked_not_central : centralInvolution ∉ center Model := by
  intro hz
  have he := conjugation_fixes_central squareConjugator centralInvolution hz
  have hz' : centralInvolution = b ^ 2 := he.symm.trans squareConjugator_alignment
  exact b_square_not_central (Eq.mp (congrArg (fun t : Model => t ∈ center Model) hz') hz)

private theorem center_eq_bot_of_small_centralizer {G : Type*} [Group G]
    (H : Subgroup G) [Finite (centralizer (H : Set G))] (z : G)
    (hzH : z ∈ centralizer (H : Set G)) (hzc : z ∉ center G)
    (hcard : Nat.card (centralizer (H : Set G)) ≤ 2) : center G = ⊥ := by
  classical
  let A := centralizer (H : Set G)
  let zA : A := ⟨z, hzH⟩
  have hz1 : z ≠ 1 := fun h => hzc (h ▸ (one_mem (center G)))
  have hz : zA ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  let : Nontrivial A := ⟨⟨zA, 1, hz⟩⟩
  have hc : Nat.card A = 2 := by
    have hpos := Nat.card_pos (α := A)
    have hnotone : Nat.card A ≠ 1 := by
      intro hone
      let hsub := (Nat.card_eq_one_iff_unique.mp hone).1
      exact hz (hsub.elim zA 1)
    have hu := hcard
    change Nat.card A ≤ 2 at hu
    omega
  obtain ⟨w, hw, huniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  apply (eq_bot_iff_forall (center G)).mpr
  intro x hx
  by_contra hn
  have hxA : x ∈ A := mem_centralizer_iff.mpr (fun y _ => mem_center_iff.mp hx y)
  let xA : A := ⟨x, hxA⟩
  have hxne : xA ≠ 1 := fun h => hn (congrArg Subtype.val h)
  have hxe : xA = zA := (huniq xA hxne).trans (huniq zA hz).symm
  have he : x = z := congrArg Subtype.val hxe
  exact hzc (he ▸ hx)

private theorem centralizes_own_centralizer {G : Type*} [Group G] (z : G)
    (H : Subgroup G) (hH : H = centralizer ({z} : Set G)) :
    z ∈ centralizer (H : Set G) := by
  apply mem_centralizer_iff.mpr
  intro x hx
  rw [hH] at hx
  exact mem_centralizer_singleton_iff.mp hx

/-- The concrete Rudvalis model has trivial center. -/
theorem model_center_eq_bot : center Model = ⊥ := by
  apply center_eq_bot_of_small_centralizer max6 centralInvolution
    _ marked_not_central max6_doubleCentralizer_card_le_two
  exact centralizes_own_centralizer centralInvolution max6 max6_eq_centralizer

end Rudvalis.LowCentralizers
