module

public import Theory.Representation.BinaryPermutation
public import Theory.Mathieu.M12.Basic
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Concrete targets for the small binary Mathieu modules

The M₁₂ target is the augmentation subspace modulo constants, realized as
the image in the deleted permutation module. The M₂₂ targets are the
ten-dimensional code hyperplane and cocode quotient at the native fixed
pair. The M₂₄ targets are the eleven-dimensional Golay code modulo
constants and the even permutation space modulo Golay.

Each recognition predicate requires both a group isomorphism and an
intertwining linear equivalence. The M₁₂ predicate concerns only M₁₂'s
action; it does not posit an action of Aut(M₁₂) on twelve letters.
These definitions do not assert completeness of the candidate list.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.3(2),
printed p.348, and H.11--H.13, printed pp.392--395; the completeness input
cited there is G. D. James, J. Algebra 27 (1973), 57--111.
-/

@[expose] public section
namespace Representation.MathieuSmall
open Sporadic.Mathieu

/-- The permutation heart, of dimension ten, rather than the even core of dimension eleven. -/
abbrev M12Heart := BinaryPermutation.natural (Fin 12)

/-- The action of the actual twelve-point Mathieu group on its heart. -/
noncomputable def m12HeartRepresentation : Representation (ZMod 2) M12 M12Heart :=
  (BinaryPermutation.naturalRepresentation (Fin 12)).comp M12.subtype

theorem finrank_m12Heart : Module.finrank (ZMod 2) M12Heart = 10 := by
  simpa using BinaryPermutation.finrank_natural_even (Fin 12) (by decide)

variable {L V : Type*} [Group L] [AddCommGroup V] [Module (ZMod 2) V]

/-- Recognition of the M₁₂ action, allowing a change of group marking. -/
def IsM12Heart (ρ : Representation (ZMod 2) L V) : Prop :=
  ∃ e : L ≃* M12, Nonempty (ρ.Equiv (m12HeartRepresentation.comp e.toMonoidHom))

/-- The actual M₂₂ Todd module or its code dual, with the same group marking. -/
def IsM22ToddOrDual (ρ : Representation (ZMod 2) L V) : Prop :=
  ∃ e : L ≃* M22,
    Nonempty (ρ.Equiv (MathieuCode.m22CocodeRepresentation.comp e.toMonoidHom)) ∨
    Nonempty (ρ.Equiv (MathieuCode.m22CodeRepresentation.comp e.toMonoidHom))

/-- The actual M₂₄ Todd module or its code dual, with the same group marking. -/
def IsM24ToddOrDual (ρ : Representation (ZMod 2) L V) : Prop :=
  ∃ e : L ≃* M24,
    Nonempty (ρ.Equiv (MathieuCode.cocodeRepresentation.comp e.toMonoidHom)) ∨
    Nonempty (ρ.Equiv (MathieuCode.codeRepresentation.comp e.toMonoidHom))

theorem IsM12Heart.finrank {ρ : Representation (ZMod 2) L V} (h : IsM12Heart ρ) :
    Module.finrank (ZMod 2) V = 10 := by
  obtain ⟨_, ⟨E⟩⟩ := h
  exact E.toLinearEquiv.finrank_eq.trans finrank_m12Heart

theorem IsM22ToddOrDual.finrank {ρ : Representation (ZMod 2) L V}
    (h : IsM22ToddOrDual ρ) : Module.finrank (ZMod 2) V = 10 := by
  rcases h with ⟨_, hE | hE⟩ <;> obtain ⟨E⟩ := hE
  · exact E.toLinearEquiv.finrank_eq.trans MathieuCode.finrank_m22Cocode
  · exact E.toLinearEquiv.finrank_eq.trans MathieuCode.finrank_m22Code

theorem IsM24ToddOrDual.finrank {ρ : Representation (ZMod 2) L V}
    (h : IsM24ToddOrDual ρ) : Module.finrank (ZMod 2) V = 11 := by
  rcases h with ⟨_, hE | hE⟩ <;> obtain ⟨E⟩ := hE
  · exact E.toLinearEquiv.finrank_eq.trans MathieuCode.finrank_cocode
  · exact E.toLinearEquiv.finrank_eq.trans MathieuCode.finrank_code

end Representation.MathieuSmall
