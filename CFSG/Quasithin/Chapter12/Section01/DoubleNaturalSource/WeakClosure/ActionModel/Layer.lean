module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.ModelAction
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCover

/-!
# The component layer of the literal doubled action quotient

The image of L/O₂(L) is a quasisimple subgroup of index two. The index-two
cover theorem identifies every component with this subgroup, so its range
is the full layer. The resulting layer marking preserves the supplied
component quotient exactly.

Source: Aschbacher--Smith, H.9 and 12.1, printed pp.389,788.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryNaturalDual BinaryLinear.OuterCyclic
open BinaryNaturalDual.ModelOrbits
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)

theorem componentEmbedding_range_eq_layer :
    B.componentEmbedding.range = componentLayer B.ActionQuotient := by
  have hn : 3 ≤ n := by have := B.degree; omega
  let : IsSimpleGroup (LinearGroup n) := AutomorphismModel.linear_simple hn
  let : Group.IsPerfect (LinearGroup n) := AutomorphismModel.linear_perfect hn
  let : IsQuasisimple (LinearGroup n) := ⟨
    ((QuotientGroup.quotientMulEquivOfEq
      (AutomorphismModel.linear_center_eq_bot (by omega : 0 < n))).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple B.componentEmbedding.range :=
    IsQuasisimple.of_mulEquiv B.componentRangeEquiv
  let : B.componentEmbedding.range.Normal := normal_of_index_eq_two B.componentRange_index
  apply le_antisymm
  · exact le_sSup ⟨(inferInstance : B.componentEmbedding.range.Normal).isSubnormal,
      inferInstance⟩
  · apply sSup_le
    intro K hK
    exact (hK.eq_of_index_two_quasisimple B.componentRange_index).le

def quotientLayerEquiv : componentLayer B.ActionQuotient ≃* LinearGroup n :=
  (MulEquiv.subgroupCongr B.componentEmbedding_range_eq_layer.symm).trans
    B.componentRangeEquiv.symm

theorem quotientLayerEquiv_embedding (q : L ⧸ pCore 2 L) :
    B.quotientLayerEquiv ⟨B.componentEmbedding q,
      B.componentEmbedding_range_eq_layer ▸ ⟨q, rfl⟩⟩ = B.component q := by
  change B.component ((MonoidHom.ofInjective B.componentEmbedding_injective).symm
    ((MonoidHom.ofInjective B.componentEmbedding_injective) q)) = _
  rw [MulEquiv.symm_apply_apply]

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
