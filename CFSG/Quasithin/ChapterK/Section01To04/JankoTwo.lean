module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.MarkedApplications
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.ActorReduction

/-!
# K.4.5: the J₂ cubic boundary qhat = 2 < q

For the genuine marked restriction of the natural G₂(4) module to J₂, including
its compatible outer field action, every elementary actor of ratio at most
two is inner, has rank four and fixed codimension eight, and is nonquadratic.
The actual E₄ × A₅ centralizer supplies a rank-four cubic actor attaining two.
These facts prove the cubic equality, the strict quadratic inequality, and
absence of FF and FF-star offenders.

The marking is an actual equivariant identification, not a family tag. Its
recognition and the universal B.4.6 root and long-root module facts remain
explicit earlier-source inputs for the Chapter K assembly. All particular J₂
embedding comparisons, involution geometry, local-module calculations and
ratio deductions are proved here or in the public descendants.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.4.5,
printed p.460 / PDF p.471.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
open NaturalLocalAction
open scoped ENNReal
variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)
include D

omit [FiniteDimensional (ZMod 2) V] in
/-- The actual rank-four cubic actor gives the upper bound in K.4.5. -/
theorem cubicRatio_le_two (h : InvolutionImages.B46RootFacts K) : cubicRatio ρ ≤ 2 := by
  obtain ⟨hA,hr,hc,hd,-⟩ := D.sourceActor_calculation h
  apply (cubicRatio_le_nat_iff ρ 2).mpr
  exact ⟨D.sourceActor,hA,hc,by rw [hd,hr]⟩

/-- K.4.5's cubic boundary, under the genuine marking and the named universal
B.4.6 root facts. The upper bound is attained by the literal centralizer actor. -/
theorem cubicRatio_eq_two
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K) :
    cubicRatio ρ = 2 := by
  let : Module.Finite (ZMod 2) K := Module.finite_of_finrank_eq_succ D.fieldDegree
  apply le_antisymm (D.cubicRatio_le_two h)
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  by_cases hs : actionRatio ρ A ≤ 2
  · have hn := (actionRatio_le_nat_iff ρ hA.1 2).mp hs
    obtain ⟨-,hr,hd,-⟩ := D.small_actor_calculation h hV A hA.1 hn
    rw [actionRatio,hr,hd]
    rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
    norm_num
  · exact le_of_lt (lt_of_not_ge hs)

/-- Every possible actor at ratio at most two is nonquadratic, giving the
strict quadratic inequality, including the case of an empty quadratic family. -/
theorem two_lt_quadraticRatio
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K) :
    2 < quadraticRatio ρ := by
  let : Module.Finite (ZMod 2) K := Module.finite_of_finrank_eq_succ D.fieldDegree
  by_contra! hq
  obtain ⟨A,hA,hquad,hs⟩ := (quadraticRatio_le_two_iff ρ).mp hq
  exact (D.small_actor_calculation h hV A hA hs).2.2.2 hquad

/-- The complete conditional J₂ ratio calculation of K.4.5. Recognition of
the marking and production of the universal B.4.6 inputs remain with Chapter K. -/
theorem ratios
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K) :
    cubicRatio ρ = 2 ∧ 2 < quadraticRatio ρ :=
  ⟨D.cubicRatio_eq_two h hV,D.two_lt_quadraticRatio h hV⟩

/-- There are no FF offenders on the marked twelve-dimensional J₂ module. -/
theorem not_isFFModule
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K) :
    ¬ IsFFModule ρ := by
  let : Module.Finite (ZMod 2) K := Module.finite_of_finrank_eq_succ D.fieldDegree
  rintro ⟨A,hA,hs⟩
  obtain ⟨-,hr,hd,-⟩ := D.small_actor_calculation h hV A hA (by omega)
  omega

/-- In particular, the source's FF-star family is empty. -/
theorem no_bestOffender
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K)
    (A : Subgroup G) : ¬ IsBestOffender ρ A := by
  intro hA
  exact D.not_isFFModule h hV ⟨A,hA.isOffender ρ⟩
end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
