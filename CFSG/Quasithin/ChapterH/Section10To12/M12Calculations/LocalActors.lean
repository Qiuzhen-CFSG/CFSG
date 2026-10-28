module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Embedding
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Outer
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Reductions
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.FixedPairs
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers

/-!
# Ambient and outer actors in H.11.1

The ambient identification and elementary two-rank bound use the two authorized
model rank premises. The outer involution displacement calculation uses only
the explicit outer-fusion premise, with a proved order-eleven commutator in the
actual degree-24 automorphism model.

For an elementary sixteen, the actual A₅ in an outer involution centralizer
supplies an inner/outer fixed pair. Its common fixed space has dimension at
most three, while its two fixed spaces span at least eight dimensions. This
proves both dimension clauses of H.11.1(4), together with an actual ambient
isomorphism to Aut(M₁₂) preserving the given embedding.

For a non-two-central involution, the normalized residual A₅ acts faithfully
on its displacement space. The intrinsic A₅ centralizer bounds then give
orders at most four and two for the displacement fixer and its residual
intersection. The quadratic reduction proves H.11.1(5), using two-centrality
in an actual Sylow subgroup of the ambient group.

Only the authorized model rank bounds, outer involution fusion, and genuine
inner C₂ × S₅ and outer C₂ × A₅ table rows remain explicit premises. The
parent H.11 source assembly owns their discharge and the construction of
`AmbientExtension`. No subgroup-placement or module-action premise remains.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.11.1, printed pp.392–393.
-/

public section

open Subgroup Representation.BinaryOffender Sporadic.Mathieu
open Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ) (d : AmbientExtension ρ h)

include d in
/-- Both dimension bounds of H.11.1(4), with the fixed pair constructed from
the genuine outer fixed-subgroup row. -/
theorem dimensions_of_elementary_sixteen (hinner : primeRank 2 M12 ≤ 3)
    (hfusion : OuterInvolutionFusion) (hout : DisplacementFixers.OuterFixedSubgroupRows)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 3 ∧
      8 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan ρ A) := by
  obtain ⟨t, z, htA, htL, ht, hzA, hzL, hz, hpair⟩ :=
    exists_inner_outer_fixed_pair ρ h d hinner hfusion (fun a ha ht => hout a ht ha)
      A hA hcard
  exact dimensions_of_inner_outer_fixed_pair ρ h d hfusion htA htL ht hzA hzL hz hpair

include d in
/-- H.11.1(4): an elementary sixteen gives the actual ambient automorphism
identification and both fixed-space bounds. The identification preserves the
original ambient embedding, hence also its residual marking. -/
theorem elementary_sixteen (hinner : primeRank 2 M12 ≤ 3)
    (hfusion : OuterInvolutionFusion) (hout : DisplacementFixers.OuterFixedSubgroupRows)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    ∃ e : G ≃* MulAut M12, (∀ g : G, e g = d.embedding g) ∧
      Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 3 ∧
      8 ≤ Module.finrank (ZMod 2) (fixedSpaceSpan ρ A) := by
  exact ⟨d.automorphismEquivOfElementarySixteen hinner A hA hcard,
    fun g => d.automorphismEquivOfElementarySixteen_apply hinner A hA hcard g,
    dimensions_of_elementary_sixteen ρ h d hinner hfusion hout A hA hcard⟩

include d in
/-- H.11.1(5): a noncyclic quadratic subgroup either has every nonidentity
element two-central in G, or has rank two and fixed codimension greater than
four. All displacement-fixer and residual-placement bounds are proved. -/
theorem quadratic_alternative (hfusion : OuterInvolutionFusion)
    (hin : DisplacementFixers.InnerCentralizerRow)
    (hout : DisplacementFixers.OuterFixedSubgroupRows)
    (A : Subgroup G) (hA : IsQuadratic ρ A) (hn : ¬ IsCyclic A) :
    (∀ a ∈ A, a ≠ 1 → TwoCentral a) ∨ (rank A = 2 ∧ 4 < fixedCodim ρ A) := by
  exact quadratic_alternative_of_fixer_bounds ρ h d hfusion
    (DisplacementFixers.bounds_of_not_twoCentral ρ h d hfusion hin hout) A hA hn

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors
