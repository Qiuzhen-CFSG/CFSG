module

public import Theory.Representation.BinaryNaturalDual.RadicalCore
public import CFSG.Quasithin.ChapterE.Section03.Offenders.CoreDefs

/-!
# The representation interpretation of E.3.30

The binary subspace/subgroup order isomorphism takes each fixed space to
the action centralizer and preserves arbitrary suprema. Thus the linear
generated core is precisely the E.3.30 core, including its corank convention.

This is the bridge used for the generated-core conclusions of H.9.2–3,
Aschbacher–Smith, combined manuscript (1 March 2004), printed pp.390–392.
-/

public section

namespace CFSG.Quasithin.ChapterH.NaturalDual
open BinaryNaturalDual Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem fixedSpace_subgroup (ρ : Representation (ZMod 2) G V) (X : Subgroup G) :
    subgroupOrderIso (fixedSpace ρ X) =
      ChapterE.actionCentralizer (multiplicativeAction ρ) X := by
  ext v
  change (∀ x : X, ρ x v.toAdd = v.toAdd) ↔
    ∀ x ∈ X, Multiplicative.ofAdd (ρ x v.toAdd) = v
  constructor
  · intro h x hx
    exact congrArg Multiplicative.ofAdd (h ⟨x, hx⟩)
  · intro h x
    exact congrArg Multiplicative.toAdd (h x x.property)

/-- Equality of the actual generated objects, not just of their dimensions. -/
theorem generatedCore_subgroup (ρ : Representation (ZMod 2) G V) (k : ℕ) :
    subgroupOrderIso (generatedCore ρ k) =
      ChapterE.dualGeneratedCore (multiplicativeAction ρ) k := by
  simp only [generatedCore, OrderIso.map_iSup, fixedSpace_subgroup,
    ChapterE.dualGeneratedCore]

/-- Taking the faithful action image preserves the source's group-valued core. -/
theorem dualGeneratedCore_actionImage [Finite G]
    (ρ : Representation (ZMod 2) G V) (k : ℕ) :
    ChapterE.dualGeneratedCore (multiplicativeAction ρ) k =
      ChapterE.dualGeneratedCore (multiplicativeAction (imageRepresentation ρ)) k := by
  rw [← generatedCore_subgroup, ← generatedCore_subgroup, generatedCore_actionImage]

/-- The radical calculation yields the actual E.3.30 core. The degree-five
three-space and degree-four two-space cases take `k = 3` and `k = 2`. -/
theorem dualGeneratedCore_eq_top_of_le_radical [FiniteDimensional (ZMod 2) V]
    (U : Submodule (ZMod 2) V) (A : Subgroup (BinaryLinear.GL V))
    (hA : A ≤ BinaryLinear.radical U) {k : ℕ}
    (hU : Module.finrank (ZMod 2) U ≤ k)
    (hUd : Module.finrank (ZMod 2) U.dualAnnihilator ≤ k) :
    ChapterE.dualGeneratedCore
      (multiplicativeAction (naturalDualRepresentation.comp A.subtype)) k = ⊤ := by
  rw [← generatedCore_subgroup, generatedCore_eq_top_of_le_radical U A hA hU hUd,
    OrderIso.map_top]

end CFSG.Quasithin.ChapterH.NaturalDual
