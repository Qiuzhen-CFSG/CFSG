module
public import Theory.SpecificGroups.Triality.BinaryWeakRank
public import Theory.SpecificGroups.SymplecticFour.TwoPower

/-!
# Binary triality does not act faithfully on symplectic four-space

The genuine long-root/short-root product belongs to the actual binary
unipotent subgroup and has nontrivial fourth power. The dimension-four
unipotency bound therefore excludes a faithful characteristic-two action.
The carrier and root word are unchanged through the faithful central quotient.

Source: Aschbacher--Smith G.4.1, printed p.342; the root-word certificate
is provided by `Triality.Standard.BinaryWeakRank.rootProduct_fourth_ne`.
-/

@[expose] public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour.NativeTriality
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.EvenInvolutionGeometry
variable {F : Type*} [Field F] [CharP F 2]

/-- The genuine binary triality carrier has a two-element with nontrivial fourth power. -/
theorem exists_two_power_fourth_ne (n : ℕ) (hn : 0 < n) :
    ∃ x : BinaryCarrier n hn, (∃ k : ℕ, x ^ (2 ^ k) = 1) ∧ x ^ 4 ≠ 1 := by
  let x : BinaryCarrier n hn := longRoot n hn 1 * shortRoot n hn 1
  have hx : x ∈ unipotent (binaryParameters n hn) :=
    Subgroup.mul_mem _ (longRoot_mem_unipotent n hn 1)
      (shortRoot_mem_unipotent n hn 1)
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp
    (unipotent_isPGroup_binary (binaryParameters n hn) rfl))
      (⟨x, hx⟩ : unipotent (binaryParameters n hn))
  refine ⟨x, ⟨k, ?_⟩, BinaryWeakRank.rootProduct_fourth_ne n hn⟩
  exact congrArg Subtype.val hk

/-- The actual binary triality carrier has no faithful Sp₄ action in characteristic two. -/
theorem model_not_injective (n : ℕ) (hn : 0 < n)
    (j : BinaryCarrier n hn →* Sp F) : ¬Function.Injective j := by
  intro hj
  obtain ⟨x, ⟨k, hk⟩, hx⟩ := exists_two_power_fourth_ne n hn
  apply hx
  apply hj
  rw [map_pow, map_one]
  exact TwoPower.pow_four_eq_one_of_pow_two_pow_eq_one (j x) k (by rw [← map_pow, hk, map_one])

end Theory.SpecificGroups.SymplecticFour.NativeTriality
