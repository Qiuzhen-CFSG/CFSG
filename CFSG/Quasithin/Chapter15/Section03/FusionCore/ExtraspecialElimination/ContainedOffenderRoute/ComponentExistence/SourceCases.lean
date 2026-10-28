module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.Basic
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.MixedSource

/-!
# Eliminate the solvable and mixed source alternatives

The source's moved-space convention is identified with the coinvariant
kernel used by the S₃ factor construction. Thus its rank-two clause feeds
that construction directly. Together with the complete mixed-case
exclusion, this leaves only the direct-product and hyperplane records
among the literal B.5.6(2)–(5) alternatives. Those remaining records retain
all their original compatible factor and module data.

This is a reduction of supplied classification outputs. It neither assumes
nor asserts the universal classification implication or component existence.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(2)–(5),
printed p.105, and proof of 15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
open ComponentReduction
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

private theorem moved_top_eq_coinvariants {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V) :
    moved ρ ⊤ = Representation.Coinvariants.ker ρ := by
  unfold moved subspaceCommutator Representation.Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨g, _, w, _, rfl⟩
    exact ⟨(g, w), rfl⟩
  · rintro ⟨⟨g, w⟩, rfl⟩
    exact ⟨g, mem_top g, w, Submodule.mem_top, rfl⟩

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)

/-- The full source S₃ record supplies precisely the moved-plane dimension. -/
theorem not_symmetricThreeCase (c : SymmetricThreeCase (starAction d)) : False := by
  apply not_symmetricThree d c.equiv
  rw [← moved_top_eq_coinvariants]
  exact c.dimension

/-- Only the two direct-product alternatives remain among B.5.6(2)–(5). -/
theorem remaining_nonQuasisimple_cases
    (h : NonQuasisimpleAlternative (starAction d)) :
    Nonempty (TwoFactorCase (starAction d)) ∨ Nonempty (HyperplaneCase (starAction d)) := by
  cases h with
  | symmetricThree c => exact (not_symmetricThreeCase d c).elim
  | twoFactors c => exact Or.inl ⟨c⟩
  | outerSixThree c => exact (not_outerSixThreeCase d c).elim
  | hyperplane c => exact Or.inr ⟨c⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
