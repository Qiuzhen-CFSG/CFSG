module
public import Theory.SpecificGroups.PSL3Four.AutomorphismTwoPart
public import Theory.Mathieu.M23.Properties.AutomorphismTwoPart
public import Theory.Representation.Suzuki.SteinbergRegularActors
/-!
# The exceptional automizer bound for the original Suzuki root kernel

The two-group kernel of the original root projection acts faithfully on the
exceptional component. Its literal injection into that component's automorphism
group gives order at most 256 from the actual PSL₃(4) or M₂₃ marking. Applying
this bound to the existing twisted-root theorem fixes the whole Steinberg
isotypic part, retaining the rank of the original actor A.

The source assembly constructs the projection, faithful kernel restriction and
multiplicity coordinates; these are not inferred from a chosen summand.
Source: Aschbacher–Smith 13.6.27 and the terminal paragraph, pp.934–935.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open BenderSuzuki.MatrixGroups Representation
open Representation.BinaryOffender.NaturalTensor

/-- The numerical root-kernel premise follows from its actual exceptional
component action, without changing the original elementary actor. -/
theorem root_kernel_card_le_256_of_exceptional_action
    {A P K : Type*} [Group A] [Group P] [Group K]
    (hA : IsPGroup 2 A) (φ : A →* P)
    (f : φ.ker →* MulAut K) (hf : Function.Injective f)
    (hK : Nonempty (K ≃* Matrix.PSL3Four.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M23)) :
    Nat.card φ.ker ≤ 256 := by
  rcases hK with h | h
  · obtain ⟨e⟩ := h
    exact Matrix.PSL3Four.twoGroup_card_le_256_of_equiv e (hA.to_subgroup _) f hf
  · obtain ⟨e⟩ := h
    exact (Sporadic.Mathieu.m23_twoGroup_card_le_128_of_equiv e (hA.to_subgroup _) f hf).trans
      (by decide)

/-- Consume the proved model bounds in the existing full-actor Steinberg
fixation theorem. All coordinates and actions refer to the same original A. -/
theorem steinberg_fixed_of_exceptional_kernel_action
    (m : ℕ) (hm : 1 ≤ m) {F A K M : Type*} [Field F] [Group A] [Group K]
    [AddCommGroup M] [Module F M] [FiniteDimensional F M] [Nontrivial M]
    (hA : IsPGroup 2 A)
    (φ : A →* SuzukiRootSubgroup m) (τ : Representation F A M)
    (σ : Representation F A (SuzukiRootSubgroup m → M))
    (hσ : ∀ a v x, σ a v x = τ a (v ((φ a)⁻¹ * x)))
    (hinvol : ∀ a : A, a * a = 1)
    (hquad : ∀ a b v, σ a (σ b v - v) = σ b v - v)
    (f : φ.ker →* MulAut K) (hf : Function.Injective f)
    (hK : Nonempty (K ≃* Matrix.PSL3Four.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M23))
    (hsmall : ∀ a, operatorFixedCodim (σ a) ≤ 2 * Nat.log 2 (Nat.card A)) :
    ∀ a, σ a = 1 :=
  SuzukiSmallDegree.twisted_root_action_trivial_of_small_ratio m hm φ τ σ hσ
    hinvol hquad (root_kernel_card_le_256_of_exceptional_action hA φ f hf hK) hsmall

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
