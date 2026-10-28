module
public import Theory.Representation.BinaryConjugationSection.DisplacementBound
public import Theory.Representation.BinaryConjugationSection.FixedImage
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Order-two commutator bounds in sections without transvections

An order-two bound on the commutator of an actor subgroup with a literal
binary section bounds every displacement rank by one. If the action has
no transvections, all those displacements vanish. The section's exact
coordinate kernel then contains the original group commutator.

Source application: the remaining critical-pair case of Aschbacher–Smith
14.7.6, printed pp.1044–1045, refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] [Finite G] {H U Z : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W}

/-- In a binary section without transvections, a commutator bounded by an
order-two subgroup lies in the literal section kernel. -/
theorem commutator_le_kernel_of_card_two_of_no_transvections
    (s : BinaryConjugationSection H U Z ρ)
    (hno : ∀ x : H, fixedCodim ρ (zpowers x) ≠ 1)
    (B P : Subgroup G) (hBH : B ≤ H) (hP : Nat.card P = 2)
    (hc : ⁅B,U⁆ ≤ P) : ⁅B,U⁆ ≤ Z := by
  let : Finite W := Finite.of_surjective (fun u : U => (s.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  apply s.commutator_le_of_imageSpace_fixed B U hBH le_rfl
  intro v _ x
  have hr := s.displacement_rank_le_of_commutator_bound B P ⊥ bot_le hc 1
    (by simpa only [relIndex_bot_left,hP,pow_one] using (le_refl (2 : ℕ))) x x.property
  have hn := hno x
  rw [fixedCodim_zpowers_eq_displacement_rank] at hn
  change Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) ≠ 1 at hn
  have hzero : Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) = 0 := by omega
  have hz : ρ x - 1 = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero)
  have he : ρ x = 1 := sub_eq_zero.mp hz
  change ρ x v = v
  rw [he]
  rfl
end Representation.BinaryConjugationSection
