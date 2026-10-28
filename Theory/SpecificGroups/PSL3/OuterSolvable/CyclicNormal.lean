module

public import Theory.SpecificGroups.PSL3.OuterSolvable.CyclicDiagonal
public import Theory.GroupTheory.CyclicNormalOddQuotient.CyclicByTwo
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Field

/-!
# Cyclic odd subgroups in the field–graph quotient of Out(PSL₃)

Assume standard automorphisms cover the full automorphism group, the actual
diagonal image in Out is normal, and its quotient is abelian. Mapping the
standard generators into this quotient kills the linear conjugations and
leaves a cyclic field image and the graph involution. Every odd-prime subgroup
of the quotient is therefore cyclic. The diagonal image itself is cyclic
by the determinant calculation.

Coverage and the normality/commutativity calculations remain explicit inputs;
this module does not assert the full automorphism theorem. The matrix
compatibilities giving the latter inputs belong to `StandardQuotient`.
Source: GLS3, Theorem 2.5.12(b–e,i) and §2.7; Aschbacher–Smith, combined
1 March 2004 manuscript, printed p.510.
-/

public section
open scoped MatrixGroups
open Theory.GroupTheory
namespace Matrix.PSL3.OuterSolvable

/-- The actual diagonal image witnesses the required condition, once full
standard coverage and the diagonal-quotient structure have been proved. -/
theorem outer_cyclicNormalOddQuotient_of_standard_inputs
    (F : Type*) [Field F] [Finite F] (hcover : standard F = ⊤)
    [(innerDiagonalOuter F).Normal]
    [IsMulCommutative (MulAut.Outer PSL(3,F) ⧸ innerDiagonalOuter F)] :
    HasCyclicNormalOddQuotient (MulAut.Outer PSL(3,F)) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  let r := QuotientGroup.mk' (innerDiagonalOuter F)
  let f := (r.comp q).comp (fieldAction F)
  have hd : (innerDiagonal F).map (r.comp q) = ⊥ := by
    rw [← Subgroup.map_map]
    change ((linearConj F).range.map q).map r = ⊥
    rw [← MonoidHom.range_comp]
    change (innerDiagonalOuter F).map r = ⊥
    exact QuotientGroup.map_mk'_self _
  have hgen : f.range ⊔ Subgroup.zpowers (r (q (graph F))) = ⊤ := by
    have h := congrArg (Subgroup.map (r.comp q)) hcover
    rw [standard, Subgroup.map_sup, Subgroup.map_sup, hd, bot_sup_eq,
      MonoidHom.map_zpowers, ← MonoidHom.range_comp] at h
    exact h.trans (Subgroup.map_top_of_surjective _
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)))
  have ht : r (q (graph F)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, graph_sq, map_one, map_one]
  let := BenderSuzuki.MatrixGroups.HermitianForm.finiteFieldAut_isCyclic (E := F)
  let : IsCyclic f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact ⟨innerDiagonalOuter F, inferInstance, innerDiagonalOuter_isCyclic F,
    fun p _ ho U hU =>
      isCyclic_pSubgroup_of_cyclic_sup_involution f.range _ ht hgen p ho U hU⟩

end Matrix.PSL3.OuterSolvable
