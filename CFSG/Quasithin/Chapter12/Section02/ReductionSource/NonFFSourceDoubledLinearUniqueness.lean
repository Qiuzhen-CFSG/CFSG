module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearConstrainedExcluded
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearReciprocal

/-!
# Original residual uniqueness for the nonbinary doubled linear row

Failure of uniqueness produces the literal reciprocal witness, its two
radical containments and Fitting escape. Every ordinary and constrained
component of that witness is now excluded on the unchanged whole orbit.
Thus the original odd actor's residual has the required unique maximal
two-local overgroup. The independent outside-component Hall exclusion
is not inferred from reciprocal uniqueness.
Source: Aschbacher--Smith 4.4.6(2) and 7.3.4, printed pp.620,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual odd actor's residual has the original component normalizer
as its unique maximal two-local overgroup, for every nonbinary field. -/
theorem sourceOrbit_linear_residual_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (A : Subgroup G)
    (hA : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) := by
  by_contra hnot
  obtain ⟨J,H,U,hw,hWJ,hJC,hc,hescape⟩ :=
    D.sourceOrbit_linear_reciprocal_hypothesisC28 h hd F hF hmodel A hA ho hnot
  have he : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H :=
    fun hf => hescape (hf.trans (subgroupOf_mono H inf_le_right))
  obtain ⟨K,hK,hq,hout,_,hcases⟩ := hc.ordinary_or_constrained_escape he
  rcases hcases with hordinary | hconstrained
  · exact D.sourceOrbit_linear_witness_not_ordinary h hd F hF hmodel hw hWJ hJC K hordinary
  · exact D.sourceOrbit_linear_witness_not_constrained h hd F hF hmodel hw hWJ hJC
      K hK hq hout hconstrained

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
