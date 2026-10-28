module

public import Theory.Representation.BinaryOffender.ElementaryConjugateBudget
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# The two A₆ actor generation calculations

The natural case concerns elementary subgroups of the literal permutation
image S₆ inside Aut(A₆). The exceptional case asks for three inner conjugates
of one involution outside that image. Every elementary subgroup outside S₆
has rank at most two, so the second calculation suffices for all such actors.
These are explicit outstanding finite-group inputs, not classification results.

Conjugators belong to A₆ itself in both contracts. Thus they lift through an
actual component isomorphism in an arbitrary ambient group.

Source: the group generation route to Aschbacher–Smith K.1.1, printed p.452
(PDF p.463), citing GM02 Theorem 6.2 and Table 6.3.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender AlternatingSix.ShadowLocal

namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof

/-- The remaining calculation for actors in the natural permutation subgroup. -/
def NaturalGeneration : Prop :=
  ∀ A : Subgroup AutA6, IsElementaryTwo A → A ≤ natural →
    ∃ (n : ℕ) (c : Fin n → A6), n * rank A ≤ 6 ∧
      AlternatingSix.ShadowLocal.inner ≤ ⨆ i, A.map (MulAut.conj (MulAut.conj (c i))).toMonoidHom

/-- Three component conjugates of every exceptional involution suffice. -/
def ExceptionalInvolutionGeneration : Prop :=
  ∀ t : AutA6, t ^ 2 = 1 → t ∉ natural →
    ∃ c : Fin 3 → A6,
      AlternatingSix.ShadowLocal.inner ≤ ⨆ i, zpowers (MulAut.conj (c i) * t * (MulAut.conj (c i))⁻¹)

end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof
