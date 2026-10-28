module

public import Theory.Representation.BinaryPermutation
public import Theory.Mathieu.M12.Basic
public import Theory.Mathieu.M22.Basic
public import Theory.GroupTheory.Covering
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.RepresentationTheory.Intertwining

/-!
# The source inputs for the small Mathieu modules

The M₁₂ module is the image of the even-weight subspace in the permutation
module modulo constants. Thus its dimension is ten, not eleven. The
ambient group need not act on the twelve letters: its solvable residual
acts by this module through an actual group and representation equivalence.

The triple-M₂₂ condition specifies a quasisimple group with center of order
three and actual central quotient M₂₂. In particular the split carrier
`M22CoverModel 3` is not a substitute for this condition. Existence and
uniqueness of the twelve-dimensional module are theorem obligations.

Source: Aschbacher–Smith, Chapter H introduction and H.11–H.12,
printed pp.377 and 392–394, combined manuscript of 1 March 2004.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterH.Section10To12

/-- The ten-dimensional permutation heart. -/
abbrev M12Heart := BinaryPermutation.natural (Fin 12)

/-- The native M₁₂ action on its permutation heart. -/
noncomputable def m12HeartRepresentation : Representation (ZMod 2) Sporadic.Mathieu.M12 M12Heart :=
  (BinaryPermutation.naturalRepresentation (Fin 12)).comp Sporadic.Mathieu.M12.subtype

theorem finrank_m12Heart : Module.finrank (ZMod 2) M12Heart = 10 := by
  simpa using BinaryPermutation.finrank_natural_even (Fin 12) (by decide)

/-- The source H.11 setup, retaining the actual action of the solvable residual. -/
structure M12ModuleInput {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) where
  faithful : Function.Injective ρ
  residualEquiv : Subgroup.solvableResidual G ≃* Sporadic.Mathieu.M12
  moduleEquiv : Representation.Equiv (ρ.comp (Subgroup.solvableResidual G).subtype)
    (m12HeartRepresentation.comp residualEquiv.toMonoidHom)

theorem M12ModuleInput.finrank_eq_ten {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (h : M12ModuleInput ρ) : Module.finrank (ZMod 2) V = 10 :=
  h.moduleEquiv.toLinearEquiv.finrank_eq.trans finrank_m12Heart

/-- A genuine triple central cover of the native M₂₂. -/
structure IsTripleM22 (L : Type*) [Group L] : Prop where
  quasisimple : Theory.GroupTheory.IsQuasisimple L
  center_card : Nat.card (Subgroup.center L) = 3
  centralQuotient : Nonempty ((L ⧸ Subgroup.center L) ≃* Sporadic.Mathieu.M22)

end CFSG.Quasithin.ChapterH.Section10To12
