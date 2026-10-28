module
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms
public import Theory.SpecificGroups.Suzuki.SylowIntersections

/-!
# Sylow intersections at the binary Suzuki parameter

The concrete Sz(2) group has order twenty. Its Sylow two-subgroups have
order four and hence are abelian; their prime index forces any distinct
pair to generate the whole group. An element in their intersection
therefore lies in the center, which is trivial in the faithful C5:C4
coordinates. Combining this with the positive-parameter TI theorem
covers every Suzuki parameter without a new finite certificate.

The consumer is the two-neighbor core placement at the start of DGS85
(12.7), printed p.184, including its binary endpoint.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace BenderSuzuki.MatrixGroups

/-- Distinct Sylow two-subgroups of the concrete Sz(2) model are disjoint. -/
theorem smallSuzuki_sylow_eq_of_inf_ne_bot
    (P Q : Sylow 2 (SuzukiMatrixGroup 0))
    (hi : (P : Subgroup (SuzukiMatrixGroup 0)) ⊓ Q ≠ ⊥) : P = Q := by
  have hcard : Nat.card (SuzukiMatrixGroup 0) = 20 :=
    (Nat.card_congr FiveFour.suzukiZeroEquiv.toEquiv).symm.trans FiveFour.card
  have hc (R : Sylow 2 (SuzukiMatrixGroup 0)) : Nat.card R = 4 := by
    rw [R.card_eq_multiplicity,hcard]
    decide +kernel
  have hiP : (P : Subgroup (SuzukiMatrixGroup 0)).index = 5 := by
    have hh := (P : Subgroup (SuzukiMatrixGroup 0)).index_mul_card
    rw [hc P,hcard] at hh
    omega
  by_contra hpq
  have hgen : (P : Subgroup (SuzukiMatrixGroup 0)) ⊔ Q = ⊤ := by
    have hd := index_dvd_of_le (show (P : Subgroup (SuzukiMatrixGroup 0)) ≤
      (P : Subgroup (SuzukiMatrixGroup 0)) ⊔ Q from le_sup_left)
    rw [hiP] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h1 | h5
    · exact index_eq_one.mp h1
    · have hr := relIndex_mul_index (show (P : Subgroup (SuzukiMatrixGroup 0)) ≤
        (P : Subgroup (SuzukiMatrixGroup 0)) ⊔ Q from le_sup_left)
      rw [h5,hiP] at hr
      have hr1 : (P : Subgroup (SuzukiMatrixGroup 0)).relIndex
          ((P : Subgroup (SuzukiMatrixGroup 0)) ⊔ Q) = 1 := by omega
      have hQP : (Q : Subgroup (SuzukiMatrixGroup 0)) ≤ P :=
        le_sup_right.trans (relIndex_eq_one.mp hr1)
      exact (hpq (Sylow.ext (Q.is_maximal' P.isPGroup' hQP))).elim
  apply hi
  apply bot_unique
  intro x hx
  have hcentral (R : Sylow 2 (SuzukiMatrixGroup 0)) (hxR : x ∈ (R : Subgroup _)) :
      (R : Subgroup (SuzukiMatrixGroup 0)) ≤ centralizer ({x} : Set _) := by
    let : IsMulCommutative R :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hc R)
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨y,hy⟩ : R) (⟨x,hxR⟩ : R)))
  have ht := sup_le (hcentral P hx.1) (hcentral Q hx.2)
  rw [hgen] at ht
  have hZ : x ∈ center (SuzukiMatrixGroup 0) := mem_center_iff.mpr fun y =>
    mem_centralizer_singleton_iff.mp (ht (mem_top y))
  rwa [suzukiZero_center_eq_bot] at hZ

/-- The Suzuki TI property includes the binary parameter. -/
theorem suzuki_sylow_eq_of_inf_ne_bot_all (n : ℕ)
    (P Q : Sylow 2 (SuzukiMatrixGroup n))
    (hi : (P : Subgroup (SuzukiMatrixGroup n)) ⊓ Q ≠ ⊥) : P = Q := by
  cases n with
  | zero => exact smallSuzuki_sylow_eq_of_inf_ne_bot P Q hi
  | succ n => exact suzuki_sylow_eq_of_inf_ne_bot _ (Nat.succ_pos _) P Q hi

end BenderSuzuki.MatrixGroups
