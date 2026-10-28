module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Action
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.SourceComparison
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCover

/-!
# The component image is the layer of the doubled action quotient

The exact component kernel identifies its image with GL_n(2). Comparing
cardinalities through the abstract full-group equivalence gives index two.
Quasisimplicity then makes this image the whole component layer. The resulting
layer marking retains the original projection from L/O₂(L); no compatibility
of the supplied full-group equivalence is assumed.

Source: Aschbacher--Smith, H.9 setup and the setup of 12.1, printed pp.389,787--788.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open BinaryNaturalDual.ModelOrbits.AutomorphismModel BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)

/-- The range marking for the projection from L. This is distinct from
`componentRangeEquiv` for the embedding of L/O2(L) used by odd actors. -/
noncomputable def componentProjectionRangeEquiv : B.componentToActionQuotient.range ≃* LinearGroup n :=
  (QuotientGroup.quotientKerEquivRange B.componentToActionQuotient).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq B.componentToActionQuotient_ker).trans B.component)

omit [Finite G] in
theorem componentRangeEquiv_apply (l : L) :
    B.componentProjectionRangeEquiv ⟨B.componentToActionQuotient l, ⟨l, rfl⟩⟩ =
      B.componentProjection l := by
  change B.component ((QuotientGroup.quotientMulEquivOfEq B.componentToActionQuotient_ker)
    ((QuotientGroup.quotientKerEquivRange B.componentToActionQuotient).symm
      ((QuotientGroup.quotientKerEquivRange B.componentToActionQuotient)
        (QuotientGroup.mk' B.componentToActionQuotient.ker l)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem component_range_index : B.componentToActionQuotient.range.index = 2 := by
  let : Finite (LinearGroup n) := Finite.of_equiv B.componentToActionQuotient.range
    B.componentProjectionRangeEquiv.toEquiv
  have hc := B.componentToActionQuotient.range.card_mul_index
  have hi := (MulAut.innerSubgroup (LinearGroup n)).card_mul_index
  rw [inner_index B.degree,
    Nat.card_congr (innerEquiv (by have := B.degree; omega : 0 < n)).toEquiv.symm] at hi
  rw [Nat.card_congr B.componentProjectionRangeEquiv.toEquiv, Nat.card_congr B.full.toEquiv, ← hi] at hc
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc

theorem component_range_eq_layer : B.componentToActionQuotient.range =
    componentLayer B.ActionQuotient := by
  have hn : 3 ≤ n := by have := B.degree; omega
  let : IsQuasisimple (LinearGroup n) := IsQuasisimple.of_mulEquiv
    (innerEquiv (by omega : 0 < n)).symm (hG := (inner_isComponent hn).2)
  let : IsQuasisimple B.componentToActionQuotient.range :=
    IsQuasisimple.of_mulEquiv B.componentProjectionRangeEquiv.symm
  let : B.componentToActionQuotient.range.Normal := normal_of_index_eq_two B.component_range_index
  apply le_antisymm
  · exact le_sSup ⟨(inferInstance : B.componentToActionQuotient.range.Normal).isSubnormal,
      inferInstance⟩
  · apply sSup_le
    intro K hK
    exact (hK.eq_of_index_two_quasisimple B.component_range_index).le

noncomputable def sourceLayer : componentLayer B.ActionQuotient ≃* LinearGroup n :=
  (MulEquiv.subgroupCongr B.component_range_eq_layer.symm).trans B.componentProjectionRangeEquiv

theorem sourceLayer_apply (l : L) :
    B.sourceLayer ⟨B.componentToActionQuotient l,
      B.component_range_eq_layer ▸ ⟨l, rfl⟩⟩ = B.componentProjection l :=
  B.componentRangeEquiv_apply l

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
