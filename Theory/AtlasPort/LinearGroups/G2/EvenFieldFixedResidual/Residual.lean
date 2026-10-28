module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.AtlasPort.LinearGroups.G2.BinaryException
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# The two-residual of the actual finite G₂ model

Above field order two, perfectness identifies both the residual and the
derived subgroup with the whole group. Over the binary field, the cubic
acting on the right quaternion factor lies in every normal subgroup with
two-group quotient. The square of its commutator with a quaternion generator
is the long-root involution. Normal closure and the known index two therefore
identify the two-residual with the actual derived subgroup, also at G₂(2).

This preserves the derived endpoint in Aschbacher–Smith, Lemma 16.1.4(4),
printed p.1171, and the full-fixed-group distinction on printed p.1191.
The root and quaternion formulas are from the imported licensed ATLAS port.
-/

public section

namespace Atlas.G2.EvenFieldFixedResidual
open Subgroup
open scoped commutatorElement

/-- The binary two-residual is the proper derived subgroup, not full G₂(2). -/
theorem binary_twoResidual_eq_commutator :
    pResidual 2 (Model (ZMod 2)) = commutator (Model (ZMod 2)) := by
  rw [BinaryParabolicPair.commutator_eq_longRootClosure]
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, ?_⟩
    apply IsPGroup.of_card
    change BinaryException.H.index = 2 ^ 1
    simpa using BinaryException.index_H
  · have ha : BinaryParabolicPair.cubicActor ∈ pResidual 2 (Model (ZMod 2)) :=
      mem_pResidual_of_orderOf_coprime (by rw [BinaryParabolicPair.cubicActor_order]; decide)
    have hcomm : ⁅BinaryParabolicPair.cubicActor, BinaryCore.embedding BinaryCore.rightJ⁆ ∈
        pResidual 2 (Model (ZMod 2)) := by
      exact Subgroup.commutator_le_left _ _
        (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top _))
    have hsq : ⁅BinaryParabolicPair.cubicActor, BinaryCore.embedding BinaryCore.rightJ⁆ ^ 2 =
        rootA (1 : ZMod 2) := by
      rw [commutatorElement_def, BinaryParabolicPair.cubic_rightJ, ← map_inv, ← map_mul,
        ← map_pow, ← BinaryCore.embedding_involution]
      congr 1
    have hA (t : ZMod 2) : rootA t ∈ pResidual 2 (Model (ZMod 2)) := by
      have ht : t = 0 ∨ t = 1 := by revert t; decide +kernel
      rcases ht with rfl | rfl
      · rw [rootA_zero]; exact one_mem _
      · rw [← hsq]; exact pow_mem hcomm _
    apply normalClosure_le_normal
    rintro _ ⟨⟨t,u⟩,rfl⟩
    change rootA t * rootB u ∈ pResidual 2 (Model (ZMod 2))
    apply mul_mem (hA t)
    rw [← weylR_rootA]
    exact (inferInstance : (pResidual 2 (Model (ZMod 2))).Normal).conj_mem _ (hA u) _

variable {F : Type*} [Field F] [Finite F]

/-- Uniform residual equality for every finite field, including order two. -/
theorem twoResidual_eq_commutator : pResidual 2 (Model F) = commutator (Model F) := by
  by_cases hq : 2 < Nat.card F
  · let := isPerfect hq
    rw [Group.IsPerfect.commutator_eq_top]
    apply (pResidual_eq_top_iff 2 _).mpr
    intro N hN hP
    let := hN
    have : Subsingleton (Model F ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ hP.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  · have hcard : Nat.card F = 2 := by
      have := Finite.one_lt_card (α := F)
      omega
    let e := fieldEquiv (binaryFieldEquiv hcard)
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_pResidual, binary_twoResidual_eq_commutator]
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl

/-- An actual G₂ identification transports the residual to the actual
commutator subgroup, retaining the binary endpoint. -/
noncomputable def residualEquivCommutator {G : Type*} [Group G] (e : G ≃* Model F) :
    pResidual 2 G ≃* commutator (Model F) :=
  ((pResidual 2 G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr ((map_pResidual 2 e).trans twoResidual_eq_commutator))

end Atlas.G2.EvenFieldFixedResidual
