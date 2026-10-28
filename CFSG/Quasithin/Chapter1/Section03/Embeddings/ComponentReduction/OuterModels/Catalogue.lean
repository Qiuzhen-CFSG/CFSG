module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.LinearTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.LinearUnitary
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.ExceptionalRankTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Mathieu
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoFour
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.HigmanSims
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Held
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits

/-!
# The complete outer-group inspection for intrinsic embeddings

Every actual Theorem C model has a cyclic normal subgroup in its outer
quotient whose odd prime subgroups in the remaining quotient are cyclic.
The concrete automorphism calculations supply all branches, including Held.
Faithful passage from a perfect central cover transfers the result, and the
literal Frattini conjugation module of an odd Xi subgroup is consequently
reducible. The separate four-model inspection supplies abelian outer groups
for the possible nonnormal components.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.510;
Theorem C, printed p.33; Proposition 1.2.1(3), printed p.504.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Subgroup Theory.GroupTheory Section02.LocalModels

theorem held_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (e : S ≃* Held.He) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  held_model_outer_cyclicNormalOddQuotient_of_permutation_normalizer e
    Held.Realization.normalizer_surjective Held.isPGroup_permutationNormalizerQuotient

theorem theoremCModel_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (hmodel : TheoremCModel S) : HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  cases hmodel with
  | alternating n hn he => exact alternating_model_outer_cyclicNormalOddQuotient n hn he
  | linear_odd p r hp ho hr hs he =>
    exact psl2_odd_model_outer_cyclicNormalOddQuotient p r hp ho hr hs he
  | three_odd p hp ho unitary he => exact three_odd_outer_cyclicNormalOddQuotient p hp ho unitary he
  | rank_one he =>
    cases he with
    | linear n hn he => exact psl2_binary_model_outer_cyclicNormalOddQuotient n hn he
    | unitary n hn he => exact unitary_three_even_outer_cyclicNormalOddQuotient n hn he
    | suzuki m hm he =>
      exact (suzuki_outer_cyclicNormalOddQuotient m hm).of_injective
        (MulAut.outerCongr he.some).toMonoidHom (MulAut.outerCongr he.some).injective
  | rank_two he =>
    cases he with
    | linear n hn he => exact linear_three_even_outer_cyclicNormalOddQuotient n hn he
    | symplectic n hn he => exact symplectic_model_outer_cyclicNormalOddQuotient n hn he
    | g2 n hn he => exact g2_model_outer_cyclicNormalOddQuotient n hn he
    | triality n hn he => exact triality_model_outer_cyclicNormalOddQuotient n hn he
    | ree m hm he => exact ree_model_outer_cyclicNormalOddQuotient m hm he
    | symplectic_derived he => exact symplectic_derived_model_outer_cyclicNormalOddQuotient he
    | g2_derived he => exact g2_derived_model_outer_cyclicNormalOddQuotient he
    | tits he => exact tits_model_outer_cyclicNormalOddQuotient he
  | binary_linear n hn he => exact binary_linear_outer_cyclicNormalOddQuotient n hn he
  | sporadic name hne he =>
    cases name with
    | m11 => exact m11_model_outer_cyclicNormalOddQuotient he.some
    | m12 => exact m12_model_outer_cyclicNormalOddQuotient he.some
    | m22 => exact m22_model_outer_cyclicNormalOddQuotient he.some
    | m23 => exact m23_model_outer_cyclicNormalOddQuotient he.some
    | m24 => exact m24_model_outer_cyclicNormalOddQuotient he.some
    | j2 => exact JankoTwo.outer_cyclicNormalOddQuotient he.some
    | hs => exact higmanSims_outer_cyclicNormalOddQuotient he.some
    | ru => exact rudvalis_model_outer_cyclicNormalOddQuotient he.some
    | j3 => exact (hne rfl).elim
    | he => exact held_model_outer_cyclicNormalOddQuotient he.some
    | j4 => exact jankoFour_outer_cyclicNormalOddQuotient he.some
  | janko_one he => exact janko_one_outer_cyclicNormalOddQuotient he.some

theorem quasisimple_outer_cyclicNormalOddQuotient
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hmodel : TheoremCModel (Q ⧸ center Q)) :
    HasCyclicNormalOddQuotient (MulAut.Outer Q) := by
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  exact cyclicNormalOddQuotient_outer_of_centralQuotient (MulEquiv.refl _)
    (theoremCModel_outer_cyclicNormalOddQuotient hmodel)

/-- The actual Frattini module in the intrinsic embedding argument is reducible. -/
theorem quasisimple_outer_exists_invariant
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hmodel : TheoremCModel (Q ⧸ center Q))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (U : Subgroup (MulAut.Outer Q)) (hU : XiOddQuotient p U) :
    ∃ A : Subgroup (U ⧸ frattini U), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ s : normalizer (U : Set (MulAut.Outer Q)), ∀ a ∈ A,
        frattiniConjugationAction (normalizer (U : Set (MulAut.Outer Q))) U le_rfl s a ∈ A :=
  exists_invariant_of_cyclicNormalOddQuotient
    (quasisimple_outer_cyclicNormalOddQuotient hmodel) hp ho U hU

/-- The full second model inspection, on the actual quasisimple component. -/
theorem nonnormalCComponentModel_outer_isMulCommutative
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hmodel : Section02.NonnormalCComponentModel Q) :
    IsMulCommutative (MulAut.Outer Q) := by
  cases hmodel with
  | linear_even n hn he => exact psl2_binary_model_outer_isMulCommutative n hn he
  | suzuki m hm he => exact suzuki_model_outer_isMulCommutative m hm he.some
  | linear_prime p hp ho he => exact psl2_prime_model_outer_isMulCommutative p hp ho he
  | janko he => exact janko_one_outer_isMulCommutative he.some

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
