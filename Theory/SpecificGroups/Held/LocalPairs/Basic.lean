module

public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.GroupAction.ExtendingSubgroupAutomorphisms
public import Theory.GroupTheory.PResidual.Defs
public import Theory.PGroupCore

/-!
# Maps and residuals for actual Held subgroup pairs

The ambient permutation group is the fixed ATLAS degree-2058 carrier. We
use its full permutation normalizer, and retain every element preserving
the two embedded subgroups. The action on the odd subgroup is restriction
of conjugation, with an explicit equality on the original permutations.

For a permuting pair R,S, their join is RS. The definitions below distinguish
the embedded residual O²(RS) from its embedded two-core O₂(O²(RS)). They
impose neither a local subgroup catalogue nor an automorphism classification.

Sources: GLS3, Table 5.3p; Aschbacher–Smith, printed pp.511, 725, 748 and
1164. These maps support the retained Held case, rather than its exclusion.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace Held.LocalPairs

/-- The full permutation normalizer of the actual Held carrier. -/
abbrev PermutationNormalizer :=
  ↥(normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))))

/-- The full automorphism stabilizer of a subgroup of Held. This is the
meaning of normalization by an abstract automorphism. -/
def automorphismNormalizer (U : Subgroup He) : Subgroup (MulAut He) :=
  MulAction.stabilizer (MulAut He) U

/-- All full-normalizer actors preserving the given pair, including outer actors. -/
def permutationPairStabilizer (S R : Subgroup He) : Subgroup PermutationNormalizer :=
  actingPairStabilizer permutationGroup.normalizerMonoidHom S R

/-- The actual conjugation action of the preserving actors on R. -/
def permutationPairAction (S R : Subgroup He) : permutationPairStabilizer S R →* MulAut R :=
  actingPairRestriction permutationGroup.normalizerMonoidHom S R

/-- Membership is simultaneous normalization of the two literal permutation subgroups. -/
theorem mem_permutationPairStabilizer_iff (S R : Subgroup He) (a : PermutationNormalizer) :
    a ∈ permutationPairStabilizer S R ↔
      a.val ∈ normalizer (S.map representation : Set (Equiv.Perm (Fin 2058))) ∧
      a.val ∈ normalizer (R.map representation : Set (Equiv.Perm (Fin 2058))) :=
  mem_normalizer_actingPairStabilizer_iff permutationGroup S R a

/-- Compatibility with the faithful defining permutation representation. -/
theorem permutationPairAction_apply (S R : Subgroup He)
    (a : permutationPairStabilizer S R) (x : R) :
    representation (permutationPairAction S R a x : He) =
      a.val.val * representation (x : He) * a.val.val⁻¹ := rfl

/-- The two-residual in the actual pair overgroup, embedded back in Held. -/
def residual (S R : Subgroup He) : Subgroup He :=
  (pResidual 2 (R ⊔ S : Subgroup He)).map (R ⊔ S).subtype

/-- The two-core of that residual, with its own embedding back in Held. -/
def twoCore (S R : Subgroup He) : Subgroup He :=
  (pCore 2 (residual S R)).map (residual S R).subtype

theorem residual_le (S R : Subgroup He) : residual S R ≤ R ⊔ S := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem twoCore_le_residual (S R : Subgroup He) : twoCore S R ≤ residual S R := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

end Held.LocalPairs
