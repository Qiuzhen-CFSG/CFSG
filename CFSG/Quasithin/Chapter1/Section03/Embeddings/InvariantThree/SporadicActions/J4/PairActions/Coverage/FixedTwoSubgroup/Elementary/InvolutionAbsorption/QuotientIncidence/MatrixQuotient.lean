module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientBridge
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization.ActionCore
public import Theory.ElementaryAbelian.ExtraspecialSuitableLift

/-!
# The actual max2 two-core quotient in twelve binary coordinates

Let H be the closure of the original ATLAS max2 outputs and let N be the
certified seed normal closure in its conjugate `localSubgroup`. The irreducible
action on N/Z(N) kills O₂(localSubgroup). Conversely, extraspecial inner twists
and the proved relative-centralizer bound put the action kernel in N. Thus
N = O₂(localSubgroup), without identifying localSubgroup with the full
involution centralizer.

Comparing the two generator images identifies the kernel of the published
row-subquotient homomorphism H → GL₁₂(2) with O₂(H). Its range is exactly the
closure of the two published quotient matrices. The first isomorphism theorem
therefore supplies an actual equivalence H/O₂(H) with that matrix subgroup,
including its compatibility with the canonical quotient map.

Source: the unchanged ATLAS `TwoCoreCentralizer/source/J4G1-max2W1` and the
coordinate certificates imported below. GLS3 Table 5.3i, printed p.270,
motivates this local structure; the application is Aschbacher–Smith,
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`). The inner
twist argument also appears in `Realization.CoreIdentification`; here the
proved relative-centralizer bound avoids its full-generation hypotheses.
-/

@[expose] public section
open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators.Realization

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

set_option maxRecDepth 4000
attribute [local irreducible] Janko4.modelGroup

private theorem quotientAction_ker_le_normalClosure :
    OuterImageComparison.quotientAction.ker ≤ localNormalClosure := by
  intro g hg
  let : IsExtraspecial 2 localNormalClosure := normalClosure_extraspecial
  have hfix (z : localNormalClosure) (hz : z ∈ center localNormalClosure) :
      localNormalClosureAction g z = z := by
    rw [normalClosure_center] at hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    rw [map_zpow, OuterImageComparison.action_centralWord]
  have hmod (n : localNormalClosure) (_hn : n ∈ (⊤ : Subgroup localNormalClosure)) :
      localNormalClosureAction g n * n⁻¹ ∈ center localNormalClosure := by
    rw [normalClosure_center]
    apply (QuotientGroup.eq_one_iff _).mp
    change OuterImageComparison.projection (localNormalClosureAction g n * n⁻¹) = 1
    rw [map_mul, map_inv, ← OuterImageComparison.quotientAction_projection]
    rw [show OuterImageComparison.quotientAction g = 1 from hg]
    exact mul_inv_cancel _
  obtain ⟨r, hr⟩ := extraspecial_two_exists_inner_twist_fixing_subgroup
    (⊤ : Subgroup localNormalClosure) le_top (localNormalClosureAction g) hfix hmod
  have hker : g * (r : localSubgroup) ∈ localNormalClosureAction.ker := by
    apply MulEquiv.ext
    intro n
    have h := congrArg (fun v : localNormalClosure => (v : localSubgroup))
      (hr n (mem_top n))
    apply Subtype.ext
    change (g * (r : localSubgroup)) * (n : localSubgroup) *
      (g * (r : localSubgroup))⁻¹ = n
    change g * ((r : localSubgroup) * (n : localSubgroup) * (r : localSubgroup)⁻¹) * g⁻¹ = n at h
    simpa only [mul_inv_rev, mul_assoc] using h
  have hn := localNormalClosureAction_ker_le hker
  simpa only [mul_inv_cancel_right] using
    localNormalClosure.mul_mem hn (localNormalClosure.inv_mem r.property)

/-- The seed normal closure is the two-core of the generated local subgroup. -/
theorem involutionLocal_normalClosure_eq_twoCore :
    localNormalClosure = pCore 2 localSubgroup := by
  apply le_antisymm
  · exact le_sSup ⟨localNormalClosure_normal, localNormalClosure_isPGroup⟩
  · exact localTwoCore_le_quotientAction_ker.trans quotientAction_ker_le_normalClosure

/-- The actual action on the central quotient has exactly the local two-core as kernel. -/
theorem involutionLocal_quotientAction_ker :
    OuterImageComparison.quotientAction.ker = pCore 2 localSubgroup :=
  le_antisymm (quotientAction_ker_le_normalClosure.trans
    involutionLocal_normalClosure_eq_twoCore.le) localTwoCore_le_quotientAction_ker

private theorem source_generators_generate :
    Subgroup.closure {LowerBound.sourceX, LowerBound.sourceY} = ⊤ := by
  have hset : sourceSubgroup.subtype ⁻¹' ({w10, w14} : Set Janko4.Model) =
      {LowerBound.sourceX, LowerBound.sourceY} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    change (g.val = LowerBound.sourceX.val ∨ g.val = LowerBound.sourceY.val) ↔ _
    simp only [Subtype.val_inj]
  rw [← hset]
  exact Subgroup.closure_preimage_eq_top {w10, w14}

private theorem sourceEquiv_x : sourceSubgroupEquivLocal LowerBound.sourceX = subgroupX := by
  apply Subtype.ext
  apply centralizerToModel_injective
  rw [sourceSubgroupEquivLocal_apply]
  rfl

private theorem sourceEquiv_y : sourceSubgroupEquivLocal LowerBound.sourceY = subgroupY := by
  apply Subtype.ext
  apply centralizerToModel_injective
  rw [sourceSubgroupEquivLocal_apply]
  rfl

private theorem source_quotient_intertwines :
    OuterImageComparison.canonicalRowAction.comp LowerBound.quotientMap =
      (OuterImageComparison.coordinateAction OuterImageComparison.coordinates).comp
        sourceSubgroupEquivLocal.toMonoidHom := by
  apply MonoidHom.eq_of_eqOn_dense source_generators_generate
  intro g hg
  rcases hg with rfl | rfl
  · simp only [MonoidHom.comp_apply, LowerBound.quotientMap_sourceX,
      MulEquiv.coe_toMonoidHom, sourceEquiv_x,
      OuterImageComparison.canonicalRowAction_x,
      OuterImageComparison.coordinateAction_x _ OuterImageComparison.coordinates_respectsBasis]
  · simp only [MonoidHom.comp_apply, LowerBound.quotientMap_sourceY,
      MulEquiv.coe_toMonoidHom, sourceEquiv_y,
      OuterImageComparison.canonicalRowAction_y,
      OuterImageComparison.coordinateAction_y _ OuterImageComparison.coordinates_respectsBasis]

/-- The matrix homomorphism has exactly the specified generated range. -/
theorem involutionSource_matrixQuotient_range :
    LowerBound.quotientMap.range = LowerBound.quotientSubgroup := by
  rw [MonoidHom.range_eq_map, ← source_generators_generate, MonoidHom.map_closure,
    Set.image_pair, LowerBound.quotientMap_sourceX, LowerBound.quotientMap_sourceY]
  rfl

private theorem twoCore_comap_equiv {G A : Type*} [Group G] [Group A] (e : G ≃* A) :
    (pCore 2 A).comap e.toMonoidHom = pCore 2 G := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_comap_eq_self_of_surjective e.surjective, pCore_map_iso]

/-- The kernel is the source subgroup’s actual two-core. -/
theorem involutionSource_matrixQuotient_ker :
    LowerBound.quotientMap.ker = pCore 2 sourceSubgroup := by
  have h := congrArg MonoidHom.ker source_quotient_intertwines
  have hleft : (OuterImageComparison.canonicalRowAction.comp LowerBound.quotientMap).ker =
      LowerBound.quotientMap.ker :=
    MonoidHom.ker_comp_of_injective _ _ OuterImageComparison.canonicalRowAction_injective
  have hcoord : (OuterImageComparison.coordinateAction OuterImageComparison.coordinates).ker =
      OuterImageComparison.quotientAction.ker :=
    MonoidHom.ker_comp_of_injective _ _ (MulAut.congr OuterImageComparison.coordinates).injective
  rw [hleft, ← MonoidHom.comap_ker, hcoord,
    involutionLocal_quotientAction_ker, twoCore_comap_equiv] at h
  exact h

/-- The literal two-core quotient is the certified twelve-dimensional matrix group. -/
noncomputable def involutionSourceMatrixQuotientEquiv :
    InvolutionSourceQuotient ≃* LowerBound.quotientSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq involutionSource_matrixQuotient_ker.symm).trans
    ((QuotientGroup.quotientKerEquivRange LowerBound.quotientMap).trans
      (MulEquiv.subgroupCongr involutionSource_matrixQuotient_range))

/-- The equivalence agrees with the published matrix action on every source element. -/
@[simp] theorem involutionSourceMatrixQuotientEquiv_mk (x : sourceSubgroup) :
    (involutionSourceMatrixQuotientEquiv (involutionSourceQuotientMap x) :
      LowerBound.QuotientMatrixˣ) = LowerBound.quotientMap x := rfl

/-- The exact order follows by matching the presentation upper bound with
its independently checked orbit lower bound. -/
theorem involutionMatrixQuotient_card : Nat.card LowerBound.quotientSubgroup = 2661120 := by
  apply le_antisymm _ LowerBound.quotientSubgroup_card_ge
  calc
    Nat.card LowerBound.quotientSubgroup ≤ Nat.card localNormalClosureOuterAction.range :=
      quotientSubgroup_card_le_localNormalClosureOuterAction_range
    _ ≤ Nat.card LocalNormalClosureQuotient :=
      Nat.card_le_card_of_surjective _ localNormalClosureOuterAction.rangeRestrict_surjective
    _ ≤ 2661120 :=
      NormalClosureControl.ActionKernel.Presentation.quotient_card_le_of_presentation_bound
        NormalClosureControl.ActionKernel.Presentation.presentation_finite_card_le

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
