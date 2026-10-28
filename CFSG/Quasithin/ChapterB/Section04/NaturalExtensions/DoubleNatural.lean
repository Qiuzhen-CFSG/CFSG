module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.BinaryOffender.SectionLinear
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The two natural factors in B.4.9

The shared input keeps the faithful original action, its actual natural
subrepresentation, and an equivariant quotient isomorphism to that same
representation or its contragredient. Splitting means an invariant complement
to that original submodule. No splitting, quadraticity, offender or ratio
conclusion is included in the input.

The basic dimension identity and the two-factor offender budget hold before
splitting. They are the linear-algebra inputs to the independent splitting
and offender arguments for Aschbacher–Smith B.4.9, printed pp.92–95,
combined manuscript of 1 March 2004. The source family restriction is n = 3,
or degree one with n ≥ 4; it belongs in the theorems using this input.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The original faithful action, a marked natural submodule, and an actual
binary equivariant identification of its quotient with that module or its dual. -/
structure DoubleNatural (F : BinaryField) (n : ℕ) (ρ : Representation (ZMod 2) G V) where
  faithful : Function.Injective ρ
  space : Subrepresentation ρ
  natural : ActionEquiv space.toRepresentation (linearNatural F n)
  quotient : Nonempty (Representation.Equiv space.quotientRepresentation space.toRepresentation) ∨
    Nonempty (Representation.Equiv space.quotientRepresentation space.toRepresentation.dual)

namespace DoubleNatural
variable {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F n ρ)

/-- The desired splitting is an invariant direct complement to the original submodule. -/
@[expose] def Splits : Prop := ∃ C : Subrepresentation ρ, IsCompl d.space.toSubmodule C.toSubmodule

variable [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
/-- The two literal factors have the same binary dimension, also in the dual case. -/
theorem quotient_finrank : Module.finrank (ZMod 2) (V ⧸ d.space.toSubmodule) =
    Module.finrank (ZMod 2) d.space.toSubmodule := by
  rcases d.quotient with h | h
  · obtain ⟨e⟩ := h
    exact e.toLinearEquiv.finrank_eq
  · obtain ⟨e⟩ := h
    exact e.toLinearEquiv.finrank_eq.trans Subspace.dual_finrank_eq

include d in
/-- The extension has exactly twice the binary dimension of its natural submodule. -/
theorem finrank : Module.finrank (ZMod 2) V = 2 * n * F.degree := by
  have hF : Module.finrank (ZMod 2) F.Carrier = F.degree := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    rw [Nat.card_zmod, F.card_eq] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
  have hn : Module.finrank (ZMod 2) d.space.toSubmodule = n * F.degree := by
    rw [d.natural.linearEquiv.finrank_eq]
    simp [Module.finrank_pi_fintype, hF]
  have hd := d.space.toSubmodule.finrank_quotient_add_finrank
  rw [d.quotient_finrank, hn] at hd
  simp only [mul_assoc]
  omega

/-- The source inequality (!) uses both actual factors, without assuming splitting. -/
theorem offender_budget {A : Subgroup G} (hA : IsOffender ρ A) :
    fixedCodim d.space.toRepresentation A + fixedCodim d.space.quotientRepresentation A ≤ rank A := by
  have h := fixedCodim_quotient_add_subrepresentation_le ρ d.space A
  have h' : fixedCodim d.space.toRepresentation A +
      fixedCodim d.space.quotientRepresentation A ≤ fixedCodim ρ A := by
    simpa only [add_comm] using h
  exact h'.trans hA.2
end DoubleNatural
end CFSG.Quasithin.ChapterB.NaturalExtensions
