module

public import CFSG.Quasithin.Chapter6.SourceDefs
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.AlternatingFive

/-!
# Excluding the degree-one Hermitian layer in the original source setup

The five singular points identify the Hermitian model at half-degree one
with the deleted A₅ module. Composing the actual quotient actor and module
coordinates gives that same model on the original subgroup. Hypothesis
6.1.1 excludes it on the literal moved layer, so any full Hermitian layer
model has half-degree greater than one.

Source: Aschbacher--Smith, Remark 5.1.4 and Hypothesis 6.1.1,
printed pp.630 and 663, using I.1.6(3), printed p.408; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter6.Source
open Representation.OrthogonalFourMinus
variable {G : Type*} [Group G]

attribute [local instance] SL2.BinarySmall.spaceBinaryModule

/-- The original quotient actor and coordinates identify the half-degree-one
Hermitian model with the actual deleted A₅ module. -/
theorem IsConjugationModel.a5_of_hermitian_one {L W : Subgroup G}
    (hm : IsConjugationModel L W (SL2.BinarySmall.hermitian 1)) :
    IsConjugationModel L W a5Module := by
  obtain ⟨e,f,hf⟩ := hm
  let c : Multiplicative (FiniteModel.Space 1) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 5)) := {
    toFun v := Multiplicative.ofAdd (AlternatingFive.moduleEquiv v.toAdd)
    invFun v := Multiplicative.ofAdd (AlternatingFive.moduleEquiv.symm v.toAdd)
    left_inv v := congrArg Multiplicative.ofAdd
      (AlternatingFive.moduleEquiv.symm_apply_apply v.toAdd)
    right_inv v := congrArg Multiplicative.ofAdd
      (AlternatingFive.moduleEquiv.apply_symm_apply v.toAdd)
    map_mul' v w := congrArg Multiplicative.ofAdd
      (map_add AlternatingFive.moduleEquiv v.toAdd w.toAdd) }
  refine ⟨e.trans AlternatingFive.groupEquiv,
    f.trans c,?_⟩
  intro l w
  have hi := AlternatingFive.intertwines
    (e (QuotientGroup.mk' (pCore 2 L) l)) (f w).toAdd
  change AlternatingFive.moduleEquiv
      (SL2.BinarySmall.hermitian 1 (e (QuotientGroup.mk' (pCore 2 L) l)) (f w).toAdd) =
    a5Module (AlternatingFive.groupEquiv (e (QuotientGroup.mk' (pCore 2 L) l)))
      (AlternatingFive.moduleEquiv (f w).toAdd) at hi
  change (f.symm (Multiplicative.ofAdd (AlternatingFive.moduleEquiv.symm
    (a5Module (AlternatingFive.groupEquiv (e (QuotientGroup.mk' (pCore 2 L) l)))
      (AlternatingFive.moduleEquiv (f w).toAdd)))) : G) = _
  rw [←hi,LinearEquiv.symm_apply_apply]
  exact hf l w

namespace Hypothesis611
variable [Finite G] {κ : GroupClass} {T : Sylow 2 G}
  {L M V : Subgroup G} {n : ℕ}

/-- The literal A₅ exclusion in Hypothesis 6.1.1 rules out a full
half-degree-one Hermitian model on its original moved layer. -/
theorem not_hermitian_layer_one (h : Hypothesis611 κ T L M V n) :
    ¬ IsConjugationModel L (layer L V) (SL2.BinarySmall.hermitian 1) := by
  intro hm
  exact h.not_a5 (Or.inl hm.a5_of_hermitian_one)

/-- Every full Hermitian model of the actual source layer has half-degree
greater than one; no recognition or exclusion callback is required. -/
theorem one_lt_hermitian_layer_half_degree (h : Hypothesis611 κ T L M V n)
    {s : ℕ} [NeZero s]
    (hm : IsConjugationModel L (layer L V) (SL2.BinarySmall.hermitian s)) : 1 < s := by
  have hs : s ≠ 0 := NeZero.ne s
  have hs1 : s ≠ 1 := by
    intro he
    subst s
    exact h.not_hermitian_layer_one hm
  omega

end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
