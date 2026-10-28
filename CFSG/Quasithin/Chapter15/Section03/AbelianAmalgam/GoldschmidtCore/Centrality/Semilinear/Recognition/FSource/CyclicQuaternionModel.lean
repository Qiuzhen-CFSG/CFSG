module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import Theory.GroupTheory.SpecificGroups.QuaternionCyclicModel

/-!
# The literal cyclic-quaternion kernel in row ten

Transport the actual C₄ and Q₈ factors of the concrete central product through
the selected local-core isomorphism. Their commutation, intersection of order
two and generation are preserved, supplying the intrinsic row-ten record.

Source: Aschbacher–Smith F.1.12(I)(8) and F.6.18(10), pp.263 and 310.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open QuaternionCyclic

/-- The original kernel gets actual cyclic and quaternion subgroups. -/
def cyclicQuaternionProductOfModel {D : Type*} [Group D]
    (e : D ≃* QuaternionCyclic.Model) : CyclicQuaternionProduct D where
  cyclic := cyclicEmbedding.range.map e.symm.toMonoidHom
  quaternion := quaternionEmbedding.range.map e.symm.toMonoidHom
  cyclicEquiv := (e.symm.subgroupMap _).symm.trans
    (MonoidHom.ofInjective cyclicEmbedding_injective).symm
  quaternionEquiv := (e.symm.subgroupMap _).symm.trans
    (MonoidHom.ofInjective quaternionEmbedding_injective).symm
  commute := by
    rintro x ⟨a,⟨c,rfl⟩,rfl⟩ y ⟨b,⟨q,rfl⟩,rfl⟩
    exact (e.symm.map_mul _ _).symm.trans
      ((congrArg e.symm (factors_commute q c).symm).trans (e.symm.map_mul _ _))
  intersection := by
    rw [← map_inf _ _ e.symm.toMonoidHom e.symm.injective,
      card_map_of_injective e.symm.injective, inf_comm]
    exact card_factor_intersection
  generates := by
    rw [← Subgroup.map_sup, sup_comm, factors_generate,
      map_top_of_surjective e.symm.toMonoidHom e.symm.surjective]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
