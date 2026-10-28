module
public import Theory.GroupTheory.SubgroupTransport.Restriction

/-!
# Intersections along a partial group isomorphism

For an isomorphism between two subgroups of one group, iterated images of
the top subgroup form a descending chain. Intersecting its forward and
backward chains gives a two-coordinate array. The partial isomorphism shifts
the coordinates, and intersections take their coordinatewise maxima.

This proves the intersection identities in Niles, *Pushing-up in finite
groups* (1979), Lemmas 2.5 and 2.6, directly in the original group. It does
not require extending the partial isomorphism to an ambient automorphism.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

/-- Forward range intersections for the literal partial isomorphism. -/
@[expose] noncomputable def forwardChain (φ : S ≃* T) (n : ℕ) : Subgroup G :=
  (image φ)^[n] ⊤

@[simp] theorem forwardChain_zero (φ : S ≃* T) : forwardChain φ 0 = ⊤ := rfl

theorem forwardChain_succ (φ : S ≃* T) (n : ℕ) :
    forwardChain φ (n + 1) = image φ (forwardChain φ n) :=
  Function.iterate_succ_apply' _ _ _

/-- The image only depends on the intersection with the domain. -/
theorem image_domain_inf (φ : S ≃* T) (R : Subgroup G) :
    image φ (R ⊓ S) = image φ R := by
  apply congrArg (Subgroup.map (ambientHom φ))
  ext x
  exact and_iff_left x.property

@[simp] theorem image_top (φ : S ≃* T) : image φ ⊤ = T := by
  rw [← image_domain_inf, top_inf_eq, image_self]

@[simp] theorem forwardChain_one (φ : S ≃* T) : forwardChain φ 1 = T := image_top φ

/-- Inverse transport followed by transport recovers the range intersection. -/
theorem image_inverse_image (φ : S ≃* T) (R : Subgroup G) :
    image φ (image φ.symm R) = R ⊓ T := by
  rw [← image_domain_inf φ.symm R]
  exact image_symm φ.symm _ inf_le_right

theorem forwardChain_antitone (φ : S ≃* T) : Antitone (forwardChain φ) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => exact le_top
  | succ n ih =>
    calc
      forwardChain φ (n + 1 + 1) = image φ (forwardChain φ (n + 1)) :=
        forwardChain_succ φ (n + 1)
      _ ≤ image φ (forwardChain φ n) := image_mono φ ih
      _ = forwardChain φ (n + 1) := (forwardChain_succ φ n).symm

theorem forwardChain_succ_le_range (φ : S ≃* T) (n : ℕ) :
    forwardChain φ (n + 1) ≤ T := by
  simpa only [forwardChain_one] using forwardChain_antitone φ (show 1 ≤ n + 1 by omega)

/-- Two-sided interval cells. The printed row r has a + b = r + 1. -/
@[expose] noncomputable def intervalCell (φ : S ≃* T) (a b : ℕ) : Subgroup G :=
  forwardChain φ a ⊓ forwardChain φ.symm b

@[simp] theorem intervalCell_zero_left (φ : S ≃* T) (b : ℕ) :
    intervalCell φ 0 b = forwardChain φ.symm b := top_inf_eq _

@[simp] theorem intervalCell_zero_right (φ : S ≃* T) (a : ℕ) :
    intervalCell φ a 0 = forwardChain φ a := inf_top_eq _

@[simp] theorem intervalCell_initial_left (φ : S ≃* T) : intervalCell φ 0 1 = S := by
  simp

@[simp] theorem intervalCell_initial_right (φ : S ≃* T) : intervalCell φ 1 0 = T := by
  simp

@[simp] theorem intervalCell_intersection (φ : S ≃* T) : intervalCell φ 1 1 = S ⊓ T := by
  simp only [intervalCell, forwardChain_one, inf_comm]

theorem intervalCell_le_domain (φ : S ≃* T) (a b : ℕ) : intervalCell φ a (b + 1) ≤ S :=
  inf_le_right.trans (forwardChain_succ_le_range φ.symm b)

theorem intervalCell_le_range (φ : S ≃* T) (a b : ℕ) : intervalCell φ (a + 1) b ≤ T :=
  inf_le_left.trans (forwardChain_succ_le_range φ a)

/-- The actual partial isomorphism shifts every permitted cell. -/
theorem image_intervalCell (φ : S ≃* T) (a b : ℕ) :
    image φ (intervalCell φ a (b + 1)) = intervalCell φ (a + 1) b := by
  rw [intervalCell, image_inf, ← forwardChain_succ φ a, forwardChain_succ φ.symm b,
    image_inverse_image]
  rw [← inf_assoc]
  exact inf_eq_left.mpr (inf_le_left.trans (forwardChain_succ_le_range φ a))

private theorem forwardChain_inf (φ : S ≃* T) (a b : ℕ) :
    forwardChain φ a ⊓ forwardChain φ b = forwardChain φ (max a b) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, inf_eq_right.mpr (forwardChain_antitone φ hab)]
  · rw [max_eq_left hba, inf_eq_left.mpr (forwardChain_antitone φ hba)]

/-- The full interval-intersection formula is coordinatewise maximum. -/
theorem intervalCell_inf (φ : S ≃* T) (a b c d : ℕ) :
    intervalCell φ a b ⊓ intervalCell φ c d = intervalCell φ (max a c) (max b d) := by
  unfold intervalCell
  calc
    _ = (forwardChain φ a ⊓ forwardChain φ c) ⊓
        (forwardChain φ.symm b ⊓ forwardChain φ.symm d) := by ac_rfl
    _ = _ := by rw [forwardChain_inf, forwardChain_inf]

/-- Every intermediate entry of a row contains the intersection of its endpoints. -/
theorem intervalCell_inf_le_between (φ : S ≃* T) {a b c d e f : ℕ}
    (hae : a ≤ e) (hec : e ≤ c) (hfb : f ≤ b) (hdf : d ≤ f) :
    intervalCell φ a b ⊓ intervalCell φ c d ≤ intervalCell φ e f := by
  rw [intervalCell_inf, max_eq_right (hae.trans hec), max_eq_left (hdf.trans hfb)]
  exact inf_le_inf (forwardChain_antitone φ hec) (forwardChain_antitone φ.symm hfb)

/-- Consecutive same-row entries intersect in the next row. -/
theorem intervalCell_adjacent_inf (φ : S ≃* T) (a b : ℕ) :
    intervalCell φ a (b + 1) ⊓ intervalCell φ (a + 1) b =
      intervalCell φ (a + 1) (b + 1) := by
  rw [intervalCell_inf, max_eq_right (Nat.le_succ a), max_eq_left (Nat.le_succ b)]

end Theory.GroupTheory.SubgroupTransport
