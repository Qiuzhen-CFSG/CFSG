module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.ModelTypes

/-!
# The first class in the local symmetric model

The three marked involutions in `C₂ × S₄` are conjugate. Each has centralizer
of order sixteen and is the unique marked involution in the center of that
centralizer. These small kernel-checked calculations supply the normalizer
argument placing the local centralizer in a Sylow subgroup of `C_G(t)`.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, opening of Lemma 4.2.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer

open Subgroup

private def firstFour (x : Model 4) : Prop :=
  x * x = 1 ∧ x ≠ 1 ∧ x.1 = 1 ∧ Equiv.Perm.sign x.2 = 1

private instance (x : Model 4) : Decidable (firstFour x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private theorem firstFour_iff (x : Model 4) : firstFour x ↔ FirstClass x := by
  simp [firstFour, FirstClass, orderOf_eq_prime_iff, pow_two, and_assoc]

set_option maxRecDepth 4096 in
private theorem centralizer_card_check : ∀ x : Model 4, firstFour x →
    (Finset.univ.filter (fun y : Model 4 => x * y = y * x)).card = 16 := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem center_marking_check : ∀ x y : Model 4,
    firstFour x → firstFour y →
    (∀ k : Model 4, x * k = k * x → y * k = k * y) → y = x := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem conjugacy_check : ∀ x y : Model 4, firstFour x → firstFour y →
    ∃ k : Model 4, k * x * k⁻¹ = y := by
  decide +kernel

/-- The local centralizer of a marked involution has order sixteen. -/
public theorem FirstClass.card_centralizer_four {x : Model 4} (hx : FirstClass x) :
    Nat.card (centralizer ({x} : Set (Model 4))) = 16 := by
  have he : (centralizer ({x} : Set (Model 4)) : Set (Model 4)) =
      ↑(Finset.univ.filter (fun y : Model 4 => x * y = y * x)) := by
    ext y
    simp only [SetLike.mem_coe, mem_centralizer_singleton_iff,
      Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
  change Nat.card ↥((centralizer ({x} : Set (Model 4))) : Set (Model 4)) = 16
  rw [he, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  exact centralizer_card_check x ((firstFour_iff x).mpr hx)

/-- A marked involution is the only marked element centralizing its
entire centralizer. This is the fusion-sensitive part of Sylow placement. -/
public theorem FirstClass.eq_of_centralizes_centralizer_four {x y : Model 4}
    (hx : FirstClass x) (hy : FirstClass y)
    (hc : ∀ k : Model 4, k ∈ centralizer ({x} : Set (Model 4)) →
      y * k = k * y) : y = x := by
  apply center_marking_check x y ((firstFour_iff x).mpr hx) ((firstFour_iff y).mpr hy)
  intro k hk
  exact hc k (mem_centralizer_singleton_iff.mpr hk.symm)

/-- All three first-class elements are conjugate within the local model. -/
public theorem FirstClass.exists_conjugator_four {x y : Model 4}
    (hx : FirstClass x) (hy : FirstClass y) :
    ∃ k : Model 4, k * x * k⁻¹ = y :=
  conjugacy_check x y ((firstFour_iff x).mpr hx) ((firstFour_iff y).mpr hy)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
