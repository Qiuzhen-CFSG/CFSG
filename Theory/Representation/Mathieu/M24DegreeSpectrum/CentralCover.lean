module

public import Theory.Mathieu.M24.ValueBoundParabolics.CentralCover
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient

/-!
# Faithful binary irreducible representations of M₂₄ central covers

A normal two-subgroup acts trivially in a binary irreducible module, so
faithfulness makes the two-core trivial. The existing M₂₄ central-cover
calculation then makes the center trivial. The supplied central-quotient
marking consequently determines a genuine group equivalence with M₂₄.

Transport along its inverse preserves the original vector space,
faithfulness and irreducibility. Pullback along the literal marked quotient
map recovers the original representation exactly.

Source: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408; the application is
the degree sieve in Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, manuscript p.17.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace Representation.Mathieu.M24DegreeSpectrum

namespace CentralCover
variable {L V : Type*} [Group L] [Finite L] [IsQuasisimple L]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) L V)

/-- Faithful irreducible binary M₂₄ covers have trivial center. -/
theorem center_eq_bot (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : L ⧸ center L ≃* M24) : center L = ⊥ := by
  let := hi
  have hcore : pCore 2 L = ⊥ :=
    le_bot_iff.mp ((normal_p_subgroup_le_ker σ (pCore 2 L)
      (pCore_isPGroup (p := 2))).trans ((MonoidHom.ker_eq_bot_iff σ).mpr hf).le)
  exact M24ValueBoundParabolics.center_eq_bot_of_twoCore_eq_bot hcore e

/-- The group isomorphism induced by the original central-quotient marking. -/
noncomputable def groupEquiv (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : L ⧸ center L ≃* M24) : L ≃* M24 :=
  ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot σ hf hi e)).trans
    QuotientGroup.quotientBot).symm.trans e

/-- The group isomorphism uses exactly the supplied quotient marking. -/
theorem groupEquiv_apply (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : L ⧸ center L ≃* M24) (l : L) :
    groupEquiv σ hf hi e l = e (QuotientGroup.mk' (center L) l) := by
  apply congrArg e
  rfl

/-- Transport the original action to native M₂₄ on the same vector space. -/
noncomputable def nativeRepresentation (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : L ⧸ center L ≃* M24) : Representation (ZMod 2) M24 V :=
  σ.comp (groupEquiv σ hf hi e).symm.toMonoidHom

/-- Transport preserves faithfulness. -/
theorem nativeRepresentation_faithful (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : L ⧸ center L ≃* M24) : Function.Injective (nativeRepresentation σ hf hi e) :=
  hf.comp (groupEquiv σ hf hi e).symm.injective

/-- Transport preserves irreducibility. -/
theorem nativeRepresentation_irreducible (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : L ⧸ center L ≃* M24) : (nativeRepresentation σ hf hi e).IsIrreducible :=
  (irreducible_comp_surjective_iff (groupEquiv σ hf hi e).symm.toMonoidHom
    (groupEquiv σ hf hi e).symm.surjective σ).mpr hi

/-- Pullback along the literal marked quotient recovers the original action. -/
theorem nativeRepresentation_comp_quotient (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (e : L ⧸ center L ≃* M24) :
    (nativeRepresentation σ hf hi e).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) = σ := by
  ext l v
  change σ ((groupEquiv σ hf hi e).symm (e (QuotientGroup.mk' (center L) l))) v = σ l v
  rw [← groupEquiv_apply σ hf hi e l, MulEquiv.symm_apply_apply]
end CentralCover
end Representation.Mathieu.M24DegreeSpectrum

