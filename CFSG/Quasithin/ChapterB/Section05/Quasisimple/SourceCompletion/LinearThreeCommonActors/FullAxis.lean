module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeWhole
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.AxisFourGeometry.Conjugacy
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank.Intrinsic
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Best offenders on the doubled natural SL3 module

The actual SL3 group has two-rank twice the binary field degree, retaining
its scalar center. A nontrivial actor costs at least that field degree on
each natural copy. The offender inequality therefore forces equality in
both bounds. The existing displacement equality theorem identifies the
actor with the entire pointwise hyperplane stabilizer.

Conversely, full axis groups are conjugate in SL3 to a coordinate hyperplane
centralizer. Its exact rank and fixed codimension give the offender equality,
and the proved doubled-natural ratio bound gives bestness. This is the
intrinsic iff used with the original group marking in B.5.1(1)(ii).

Source: Aschbacher--Smith, B.5.1, printed pp.99–101, and B.4.9(2), p.94.
-/

public section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open scoped MatrixGroups ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
open CFSG.Quasithin.ChapterK.Linear.Natural
open NaturalExtensions.LargerFieldThree
variable (F : BinaryField)

private theorem elementary_rank_le {A : Subgroup SL(3,F.Carrier)}
    (hA : IsElementaryTwo A) : rank A ≤ 2 * F.degree := by
  let : IsElementaryAbelian 2 A := hA.2
  have h := IsElementaryAbelian.primeRank_ge_of_card A hA.card_eq_two_pow_rank
  rwa [Representation.HermitianTensorThree.ImageOuter.OuterRank.specialLinearThree_twoRank
    F.Carrier F.degree_pos F.card_eq] at h

private theorem natural_cost_ge {A : Subgroup SL(3,F.Carrier)} (hA : A ≠ ⊥) :
    F.degree ≤ fixedCodim (linearNatural F 3) A := by
  rw [fixedCodim_eq_field_codim]
  exact Nat.le_mul_of_pos_right _ (field_dimensions_pos F 3 hA).1

private theorem fullAxis_rank_cost {A : Subgroup SL(3,F.Carrier)}
    (hA : IsFullAxisGroup F 3 A) :
    IsElementaryTwo A ∧ rank A = 2 * F.degree ∧
      fixedCodim (linearNatural F 3) A = F.degree := by
  obtain ⟨s, hs⟩ := AxisFourGeometry.full_axis_conjugate_standard F hA
  let Q := hyperplaneCentralizer F 3 0
  have hQ : IsElementaryTwo Q := hyperplaneCentralizer_elementary F 3 0 (by decide)
  have hr : rank A = 2 * F.degree := by
    rw [← rank_map_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective A,
      hs, hyperplaneCentralizer_rank]
    omega
  have hc : fixedCodim (linearNatural F 3) A = F.degree := by
    rw [← fixedCodim_map_conj (linearNatural F 3) A s, hs]
    exact subgroup_fixedCodim F 3 0 le_rfl hQ.1
  have hn : A ≠ ⊥ := by
    intro he
    rw [he, BinaryOffender.rank_bot] at hr
    have := F.degree_pos
    omega
  let e : A ≃* Q := (A.equivMapOfInjective (MulAut.conj s).toMonoidHom
    (MulAut.conj s).injective).trans (MulEquiv.subgroupCongr hs)
  let : IsElementaryAbelian 2 Q := hQ.2
  exact ⟨⟨hn,IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective⟩,hr,hc⟩

/-- Exactly the full common-axis subgroups are best offenders on two copies
of the natural SL3 module, for every binary defining field. -/
theorem doubledThree_bestOffender_iff_fullAxis (A : Subgroup SL(3,F.Carrier)) :
    IsBestOffender (repeated (linearNatural F 3) 2) A ↔ IsFullAxisGroup F 3 A := by
  constructor
  · intro hA
    have ho := (hA.isOffender (repeated (linearNatural F 3) 2)).2
    have hr := elementary_rank_le F hA.1
    have hc := natural_cost_ge F hA.1.1
    rw [repeated_two_fixedCodim] at ho
    exact full_axis_of_rank_cost F hA.1 (by omega) (by omega)
  · intro hA
    obtain ⟨he,hr,hc⟩ := fullAxis_rank_cost F hA
    have hn : ¬ IsStrongFFModule (repeated (linearNatural F 3) 2) := by
      intro h
      exact (not_lt_of_ge (one_le_doubledThree_ratio F))
        ((isStrongFFModule_iff_quadraticRatio_lt_one _).mp h)
    apply (isBestOffender_iff_of_not_strong _ hn A).mpr
    exact ⟨he,by rw [repeated_two_fixedCodim,hc,hr]⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
