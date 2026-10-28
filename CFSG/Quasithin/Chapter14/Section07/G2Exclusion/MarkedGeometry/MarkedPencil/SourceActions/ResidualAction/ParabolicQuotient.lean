module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction.ModelActions
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The full and derived binary point-parabolic quotients

The actual SL₂ block section lies in the derived group. Thus the long-local
quotient map remains surjective on every actor containing that group. Its
kernel is a two-group and SL₂(2) has trivial two-core, so the relative
parabolic quotient is S₃. The full and derived kernels have orders 32 and 16,
respectively; all core and normality statements are intrinsic to the relevant
parabolic. Explicit equivalences retain the literal stabilizer inside J.

Source: Aschbacher–Smith, 14.7.55(6), printed p.1066, and B.4.6. The block
generation argument adapts Atlas/LinearGroups/G2/Parabolic.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, from the existing CFSG port.
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. Covered by the
ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt); see also
LICENSES/ATLAS-CITATION.cff. All other ingredients are imported proved APIs.
-/

open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural Atlas.G2.Explicit
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction
@[expose] public noncomputable section

open Atlas.G2.LieParabolicSetup Atlas.G2.PairStabilizer
open scoped MatrixGroups

private theorem block_mem_derived (M : SL(2,ZMod 2)) :
    blockHom M ∈ commutator (Model (ZMod 2)) := by
  rw [BinaryParabolicPair.commutator_eq_longRootClosure]
  have hJ : blockHom (rankOneJ (F := ZMod 2)) ∈ BinaryException.H := by
    rw [block_rankOneJ, BinaryException.binary_torus, one_mul]
    exact BinaryException.weylR_in_H
  apply Matrix.SL2.transvection_induction (fun M => blockHom M ∈ BinaryException.H) ?_ ?_ M
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change blockHom (upperSL a) ∈ BinaryException.H
      rw [block_upper]
      exact BinaryException.rootE_in_H a
    · change blockHom (lowerSL a) ∈ BinaryException.H
      rw [lowerSL_conjugate,map_mul,map_mul,map_inv,block_upper]
      exact BinaryException.H.mul_mem
        (BinaryException.H.mul_mem hJ (BinaryException.rootE_in_H _))
        (BinaryException.H.inv_mem hJ)
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul]
    exact BinaryException.H.mul_mem hA hB

private theorem baseParabolic_le_local (J : Subgroup (Model (ZMod 2))) :
    pointParabolic J firstPoint ≤ local₂ := by
  rw [local₂_binary]
  change pointParabolic J firstPoint ≤ parabolic
  rw [parabolic_eq_pointStabilizer]
  exact inf_le_left

/-- The actual rank-one quotient map of the relative binary point stabilizer. -/
def pointSLHom (J : Subgroup (Model (ZMod 2))) :
    pointParabolic J firstPoint →* SL(2,ZMod 2) :=
  longSLHom.comp (Subgroup.inclusion (by exact baseParabolic_le_local J))

theorem pointSLHom_surjective (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) : Function.Surjective (pointSLHom J) := by
  intro M
  have hM : blockHom M ∈ pointParabolic J firstPoint :=
    ⟨parabolic_le_pointStabilizer (block_mem_parabolic M), hJ (block_mem_derived M)⟩
  refine ⟨⟨blockHom M,hM⟩, ?_⟩
  exact longSLHom_section M

theorem pointSLHom_kernel_isTwoGroup (J : Subgroup (Model (ZMod 2))) :
    IsPGroup 2 (pointSLHom J).ker := by
  unfold pointSLHom
  rw [← MonoidHom.comap_ker, longSLHom_ker, ← local₂_pCore]
  exact pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective (baseParabolic_le_local J))

/-- The relative two-core is the intersection with the five-root radical.
This retains the different cores in the full and derived actors. -/
theorem pointParabolic_firstPoint_pCore (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) :
    pCore 2 (pointParabolic J firstPoint) = radical₂.subgroupOf (pointParabolic J firstPoint) := by
  have he := (pointSLHom J).comap_pCore_of_ker_isPGroup
    (pointSLHom_surjective J hJ) (pointSLHom_kernel_isTwoGroup J)
  rw [Matrix.SL2.twoCore_eq_bot, MonoidHom.comap_bot] at he
  rw [← he]
  unfold pointSLHom
  rw [← MonoidHom.comap_ker, longSLHom_ker]
  rfl

/-- The relative point stabilizer has quotient S₃, even when the actor is only
the actual derived subgroup. Its kernel is its own intrinsic two-core. -/
def pointParabolicCoreEquiv_firstPoint (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) :
    (pointParabolic J firstPoint) ⧸ pCore 2 (pointParabolic J firstPoint) ≃*
      Equiv.Perm (Fin 3) :=
  ((pointSLHom J).pCoreQuotientEquiv (pointSLHom_surjective J hJ)
    (pointSLHom_kernel_isTwoGroup J)).trans
      (((QuotientGroup.quotientMulEquivOfEq (Matrix.SL2.twoCore_eq_bot (ZMod 2))).trans
        QuotientGroup.quotientBot).trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))

/-- The actual point-parabolic quotient at an arbitrary marked singular point. -/
def pointParabolicCoreEquiv (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) (p : SingularPoints (ZMod 2)) :
    (pointParabolic J p) ⧸ pCore 2 (pointParabolic J p) ≃* Equiv.Perm (Fin 3) := by
  let g := Classical.choose (exists_smul_firstPoint p)
  have hg := Classical.choose_spec (exists_smul_firstPoint p)
  have hp : (pointParabolic J p).map (MulAut.conj g).toMonoidHom = pointParabolic J firstPoint := by
    rw [pointParabolic_conj J hJ, hg]
  let eP := ((pointParabolic J p).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hp)
  have hk : IsPGroup 2 eP.toMonoidHom.ker := by
    rw [eP.toMonoidHom.ker_eq_bot_iff.mpr eP.injective]
    exact IsPGroup.of_subsingleton 2 _
  exact (eP.toMonoidHom.pCoreQuotientEquiv eP.surjective hk).trans
    (pointParabolicCoreEquiv_firstPoint J hJ)


private theorem core_card_of_parabolic_card (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) (n : ℕ)
    (hn : Nat.card (pointParabolic J firstPoint) = 6*n) :
    Nat.card (pCore 2 (pointParabolic J firstPoint)) = n := by
  have hi : (pCore 2 (pointParabolic J firstPoint)).index = 6 := by
    change Nat.card ((pointParabolic J firstPoint) ⧸ pCore 2 (pointParabolic J firstPoint)) = 6
    rw [Nat.card_congr (pointParabolicCoreEquiv_firstPoint J hJ).toEquiv]
    rw [Nat.card_perm, Nat.card_fin]
    rfl
  have h := (pCore 2 (pointParabolic J firstPoint)).card_mul_index
  rw [hi,hn] at h
  omega

/-- The full actor's point-parabolic core has order 32. -/
theorem full_pointCore_card : Nat.card (pCore 2 (pointParabolic ⊤ firstPoint)) = 32 := by
  apply core_card_of_parabolic_card ⊤ le_top 32
  have he : pointParabolic ⊤ firstPoint = parabolic (F := ZMod 2) := by
    rw [pointParabolic, inf_top_eq, parabolic_eq_pointStabilizer]
  rw [he, card_parabolic]
  norm_num

/-- Restricting to the actual derived actor halves the point-parabolic core. -/
theorem derived_pointCore_card :
    Nat.card (pCore 2 (pointParabolic (commutator (Model (ZMod 2))) firstPoint)) = 16 := by
  apply core_card_of_parabolic_card _ le_rfl 16
  let eP : pointParabolic (commutator (Model (ZMod 2))) firstPoint ≃*
      MulAction.stabilizer (commutator (Model (ZMod 2))) (firstPoint (K := ZMod 2)) :=
    { toFun := fun x => ⟨⟨x.val,x.property.2⟩,x.property.1⟩
      invFun := fun x => ⟨x.val.val,x.property,x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  rw [Nat.card_congr eP.toEquiv, BinaryParabolicPair.commutator_eq_longRootClosure]
  exact BinaryException.card_H_pointStabilizer


/-- The ambient intersection is genuinely the stabilizer inside J. -/
def relativePointEquiv (J : Subgroup (Model (ZMod 2))) (p : SingularPoints (ZMod 2)) :
    MulAction.stabilizer J p ≃* pointParabolic J p where
  toFun x := ⟨x.val.val,x.property,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The embedded residual uses the literal stabilizer and its two subtype maps. -/
theorem relativePointResidual_image (J : Subgroup (Model (ZMod 2)))
    (p : SingularPoints (ZMod 2)) :
    ((pResidual 2 (MulAction.stabilizer J p)).map (MulAction.stabilizer J p).subtype).map
      J.subtype = pointResidual J p := by
  have he : (MulAction.stabilizer J p).map J.subtype = pointParabolic J p := by
    ext x
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨hj,j.property⟩
    · rintro ⟨hp,hj⟩
      exact ⟨⟨x,hj⟩,hp,rfl⟩
  rw [map_embedded_pResidual, he]
  rfl

/-- The quotient of the literal relative stabilizer by its intrinsic core. -/
def relativePointCoreEquiv (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) (p : SingularPoints (ZMod 2)) :
    (MulAction.stabilizer J p) ⧸ pCore 2 (MulAction.stabilizer J p) ≃* Equiv.Perm (Fin 3) := by
  let eP := relativePointEquiv J p
  have hk : IsPGroup 2 eP.toMonoidHom.ker := by
    rw [eP.toMonoidHom.ker_eq_bot_iff.mpr eP.injective]
    exact IsPGroup.of_subsingleton 2 _
  exact (eP.toMonoidHom.pCoreQuotientEquiv eP.surjective hk).trans (pointParabolicCoreEquiv J hJ p)

/-- The actual six-dimensional natural action satisfies the commutator clause. -/
theorem natural_pointResidual_commutator (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) (p : SingularPoints (ZMod 2)) :
    subspaceCommutator (action (ZMod 2)) (pencilSpan naturalMap p) (pointResidual J p) =
      pencilSpan naturalMap p :=
  pencilSpan_commutator naturalMap (action (ZMod 2)) naturalMap_equivariant J hJ p

/-- The actual seven-dimensional Weyl action satisfies the same clause. -/
theorem weyl_pointResidual_commutator (J : Subgroup (Model (ZMod 2)))
    (hJ : commutator (Model (ZMod 2)) ≤ J) (p : SingularPoints (ZMod 2)) :
    subspaceCommutator (traceZeroAction (ZMod 2)) (pencilSpan weylMap p) (pointResidual J p) =
      pencilSpan weylMap p :=
  pencilSpan_commutator weylMap (traceZeroAction (ZMod 2)) weylMap_equivariant J hJ p

end
end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.ResidualAction
