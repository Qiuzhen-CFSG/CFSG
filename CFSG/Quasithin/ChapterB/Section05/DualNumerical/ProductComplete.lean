module

public import CFSG.Quasithin.ChapterB.Section05.DualNumerical.NonperfectProducts

/-!
# The complete two-factor branch of the B.5.13 dual numerical bound

Both perfect factors act trivially on the opposite prescribed source spaces,
so B.5.3 descends to a proper factor on the full original module. If a factor
is not perfect, the source models reduce to the symmetric-three and
symmetric-five arguments. This assembles every literal B.5.6(3) alternative.

The only recursive premise is the same numerical theorem for nontrivial
subgroups of strictly smaller order. No splitting of the original module or
additional model hypothesis is required.

Source: Aschbacher–Smith B.5.13, printed pp.110–111.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterB.SourceB513
open SourceInduction QuasisimpleSource

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- All source two-factor cases, with induction needed only on nontrivial actors. -/
theorem quadraticRatio_le_two_of_twoFactors_source_nontrivial
    (ρ : Representation (ZMod 2) D V) {K : GroupClass}
    (h : FFHypothesis K ρ.dual) (c : SourceTwoFactorCase ρ.dual)
    (ih : ∀ (A : Subgroup D) [Nontrivial A], Nat.card A < Nat.card D →
      FFHypothesis K (Representation.dual (ρ.comp A.subtype)) →
      quadraticRatio (ρ.comp A.subtype) ≤ 2) :
    quadraticRatio ρ ≤ 2 := by
  by_cases hf : Group.IsPerfect c.first
  · by_cases hs : Group.IsPerfect c.second
    · let _ := hf
      let _ := hs
      let : Nontrivial c.second := c.secondCase.nontrivial
      exact perfect_product_bound ρ h c (ih c.second)
    · exact quadraticRatio_le_two_of_nonperfect_twoFactors_source ρ h c ih (Or.inr hs)
  · exact quadraticRatio_le_two_of_nonperfect_twoFactors_source ρ h c ih (Or.inl hf)

/-- All source two-factor cases under the usual unrestricted subgroup induction. -/
theorem quadraticRatio_le_two_of_twoFactors_source
    (ρ : Representation (ZMod 2) D V) {K : GroupClass}
    (h : FFHypothesis K ρ.dual) (c : SourceTwoFactorCase ρ.dual)
    (ih : ∀ (A : Subgroup D), Nat.card A < Nat.card D →
      FFHypothesis K (Representation.dual (ρ.comp A.subtype)) →
      quadraticRatio (ρ.comp A.subtype) ≤ 2) :
    quadraticRatio ρ ≤ 2 :=
  quadraticRatio_le_two_of_twoFactors_source_nontrivial ρ h c (fun A _ => ih A)

end CFSG.Quasithin.ChapterB.SourceB513
