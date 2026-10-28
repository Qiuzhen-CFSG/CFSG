module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Mathieu.TwelveReduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Mathieu.TwentyTwoReduction
public import Theory.Mathieu.M11.Properties.OuterRestriction
public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.Mathieu.M23.Properties.OuterRestriction
public import Theory.Mathieu.M24.Properties.OuterRestriction

/-!
# The five Mathieu outer-group restrictions

Each concrete Mathieu group has a two-group outer automorphism quotient.
For M₁₂ the marked Sylow subgroup has a two-group automorphism group, and
every automorphism fixing it pointwise is inner. For M₂₂ every abstract
automorphism comes from the full hexad-design group, whose quotient by M₂₂
has order two. These facts discharge the two conditional reductions re-exported
here. The separate M₁₁, M₂₃ and M₂₄ calculations supply the other cases.

Transport along an actual multiplicative equivalence gives the structural
restriction for every group isomorphic to one of these five carriers. No
automorphism or reconstruction premise remains. This is the Mathieu part of
the outer-group inspection on printed p.510 of Aschbacher–Smith, combined
1 March 2004 manuscript, for the groups in Theorem C on printed p.33.
The model automorphism calculations are recorded in GLS3, Tables 5.3a–e.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Theory.GroupTheory Sporadic.Mathieu

/-- The M₁₁ case, transported through its actual Witt-design model equivalence. -/
theorem m11_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (e : S ≃* M11) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  m11_outer_hasCyclicNormalOddQuotient.of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- The M₁₂ case with the marked Sylow automorphism calculation discharged. -/
theorem m12_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (e : S ≃* M12) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  m12_model_outer_cyclicNormalOddQuotient_of_sylow_aut e
    M12SmallPair.SylowAutomorphismGroup.isPGroup_two

/-- The M₂₂ case with full abstract automorphism coverage discharged. -/
theorem m22_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (e : S ≃* M22) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  m22_model_outer_cyclicNormalOddQuotient_of_coverage e m22DesignAutToAut_surjective

/-- The M₂₃ case, using the intrinsic heptad-stabilizer calculation. -/
theorem m23_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (e : S ≃* M23) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  m23_outer_hasCyclicNormalOddQuotient.of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- The M₂₄ case, using reconstruction from the natural point stabilizers. -/
theorem m24_model_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] (e : S ≃* M24) :
    HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  M24OuterRestriction.cyclicNormalOddQuotient.of_injective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
