module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization.Quotient
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Small-order and Suzuki exclusions for the PSL₃(4) cover

The actual PSL₃(4) quotient has order 20160. Divisibility therefore excludes
A₅, A₆, their central three-covers and PSL₃(2); the Suzuki order is prime to
three. These arguments do not identify groups merely by equal order.

Source: the smaller groups in A.3.12, printed pp.47--48, and its application
in the proof of 15.3.38 on printed p.1136.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
open Chapter1.Section02.LocalModels
variable {X : Type*} [Group X]

theorem no_alternating_small (hc : 20160 ∣ Nat.card X)
    {n : ℕ} (hn : n = 5 ∨ n = 6) : ¬ IsAlternating X n := by
  rintro ⟨e⟩
  rw [Nat.card_congr e.toEquiv] at hc
  rcases hn with rfl | rfl <;>
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc <;> norm_num [Nat.factorial] at hc

theorem no_alternating_threeCover (hc : 20160 ∣ Nat.card X) :
    ¬ IsAlternatingCover X 6 := by
  rintro ⟨_, ⟨ez⟩, ⟨eq⟩⟩
  have hz : Nat.card (center X) = 3 := by rw [Nat.card_congr ez.toEquiv]; simp
  have hq : Nat.card (X ⧸ center X) = 360 := by
    rw [Nat.card_congr eq.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have he := (center X).card_mul_index
  rw [index_eq_card, hz, hq] at he
  rw [← he] at hc
  norm_num at hc

theorem no_psl_three_two (hc : 20160 ∣ Nat.card X) :
    ¬ ClassicalGroup.IsPSL X 3 2 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective, hF] at hc
  norm_num at hc

theorem no_suzuki (hc : 20160 ∣ Nat.card X) {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  have hdiv : 3 ∣ Nat.card X := dvd_trans (by norm_num) hc
  rw [Nat.card_congr e.toEquiv] at hdiv
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hdiv

/-- A bounded center bounds the whole cover once its actual quotient is marked. -/
theorem marked_card_le {H : Type*} [Group H] (B : Subgroup H)
    (c : ProjectiveMarking B 4) (hZ : center B = pCore 2 B)
    (hc : Nat.card (center B) ≤ 4) : Nat.card B ≤ 80640 := by
  have he := (pCore 2 B).card_mul_index
  rw [index_eq_card, marked_quotient_card B c, ← hZ] at he
  omega

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
