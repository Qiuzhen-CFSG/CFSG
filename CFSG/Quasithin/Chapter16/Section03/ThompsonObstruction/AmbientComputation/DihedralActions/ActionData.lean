module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.Contracts

/-!
# Rotation and action outputs for the Thompson calculation

This intermediate output contains the two actions in source 16.3.12, but no
claim about the maximum elementary family or its generated subgroup.
Its construction and the elementary-family calculation are separate obligations.
The faithful action fixes the even rotations, so either alternative centralizes R.

Adapted from the saved DihedralActions proof work. Source: Aschbacher--Smith,
combined manuscript of 1 March 2004, printed pp.1181--1182 / PDF pp.1198--1199.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup
variable {G : Type*} [Group G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

structure ActionData (d : Prepared T z t L) where
  y : G
  rotation_le : zpowers y ≤ commutingSylow T L
  rotation_characteristic : ((zpowers y).subgroupOf (commutingSylow T L)).Characteristic
  rotation_index : (zpowers y).relIndex (commutingSylow T L) = 2
  rotation_order : ∃ n : ℕ, 2 ≤ n ∧ orderOf y = 2 ^ n
  reflection_generation : zpowers y ⊔ zpowers t = commutingSylow T L
  reflection_action :
    ((∃ n : ℕ, 2 ≤ n ∧ Nonempty (commutingSylow T L ≃* DihedralGroup (2 ^ n))) ∧
      t⁻¹ * y * t = y⁻¹) ∨
    ((∃ (n : ℕ) (hn : 4 ≤ n),
      Nonempty (commutingSylow T L ≃* Semidihedral.StandardModel n hn)) ∧
      t⁻¹ * y * t = y⁻¹ * z)
  w : G
  candidate : w = d.marked.u ∨ w = t * d.marked.u
  maximizing : ∀ x : G, x = d.marked.u ∨ x = t * d.marked.u →
    Nat.card ↥(zpowers y ⊓ involutionCentralizer x) ≤
      Nat.card ↥(zpowers y ⊓ involutionCentralizer w)
  involution : orderOf w = 2
  R : Subgroup G
  R_le : R ≤ commutingSylow T L
  dihedral : ∃ n : ℕ, 2 ≤ n ∧ Nonempty (R ≃* DihedralGroup (2 ^ n))
  center_eq : ambientCenter R = zpowers z
  alternative :
    (w ∈ centralizer (commutingSylow T L : Set G) ∧
      ((R = commutingSylow T L ∧ ∃ n : ℕ, 2 ≤ n ∧
        Nonempty (commutingSylow T L ≃* DihedralGroup (2 ^ n))) ∨
       (R = omegaOneAmbient (commutingSylow T L) ∧
        R.relIndex (commutingSylow T L) = 2 ∧ ∃ (n : ℕ) (hn : 4 ≤ n),
        Nonempty (commutingSylow T L ≃* Semidihedral.StandardModel n hn)))) ∨
    (4 < orderOf y ∧ w⁻¹ * y * w = y * z ∧ R = zpowers (y ^ 2) ⊔ zpowers t)

theorem candidate_commutes_reflection (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) : Commute w t := by
  rcases hw with rfl | rfl
  · exact u_commutes_t d
  · exact (Commute.refl t).mul_left (u_commutes_t d)

theorem ActionData.centralizes_R (d : Prepared T z t L) (a : ActionData d) :
    a.w ∈ centralizer (a.R : Set G) := by
  rcases a.alternative with h | ⟨_, hy, hR⟩
  · exact centralizer_le a.R_le h.1
  · have hyz : Commute a.y z :=
      mem_centralizer_singleton_iff.mp
        (d.counterexample.localSetup.sylow_centralizes
          ((a.rotation_le (mem_zpowers _)).1))
    have hz : z ^ 2 = 1 := d.counterexample.localSetup.involution ▸ pow_orderOf_eq_one z
    have hy2 : a.w⁻¹ * a.y ^ 2 * a.w = a.y ^ 2 := by
      calc
        _ = (a.w⁻¹ * a.y * a.w) ^ 2 := by simp only [pow_two]; group
        _ = (a.y * z) ^ 2 := by rw [hy]
        _ = a.y ^ 2 := by rw [hyz.mul_pow, hz, mul_one]
    have hcomm : a.y ^ 2 * a.w = a.w * a.y ^ 2 := by
      have h := congrArg (fun x => a.w * x) hy2
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h
    have hle : a.R ≤ centralizer ({a.w} : Set G) := by
      rw [hR]
      exact sup_le
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcomm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (candidate_commutes_reflection d a.candidate).symm))
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (hle hx))
end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
