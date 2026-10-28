module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Sylow

/-!
# Marked adjacent-node parabolics in binary four-space

A node deletes its cut, using the zero-based convention of `FiveFlags`.
Adding an adjacent node strictly enlarges the stabilizer and leaves a
single cut of dimension one or three. Restriction and quotient actions
therefore identify the enlarged parabolic modulo its intrinsic two-core
with PSL₃(2). The two orientations retain their actual subquotient maps.
Conjugating the standard basis also constructs the full-flag Sylow
subgroup for every marking.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed p.959 (PDF p.976), in the degree-four minimal-parabolic branch.
The local component itself is constructed in the parent module.
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics
/-- Nodes delete cuts: node `i` omits the marked space of dimension `i+1`. -/
noncomputable def fourParabolic (b : Basis 3) (nodes : Set (Fin 3)) :
    Subgroup (LinearGroup 4) := cutStabilizer b nodesᶜ

/-- Containment of the actual parabolics detects containment of node sets. -/
theorem fourParabolic_le_iff (b : Basis 3) (s t : Set (Fin 3)) :
    fourParabolic b s ≤ fourParabolic b t ↔ s ⊆ t := by
  rw [fourParabolic, fourParabolic, cutStabilizer_le_iff, Set.compl_subset_compl]

/-- A proper addition of nodes strictly enlarges the actual stabilizer. -/
theorem fourParabolic_lt_iff (b : Basis 3) (s t : Set (Fin 3)) :
    fourParabolic b s < fourParabolic b t ↔ s ⊂ t := by
  rw [lt_iff_le_not_ge, fourParabolic_le_iff, fourParabolic_le_iff]
  rfl

/-- Choose an adjacent node, retaining both end-cut orientations. -/
def fourAdjacentNode (i : Fin 3) : Fin 3 := if i = 1 then 0 else 1

/-- The chosen node is adjacent in the three-node diagram. -/
theorem fourAdjacentNode_adjacent (i : Fin 3) :
    i.val + 1 = (fourAdjacentNode i).val ∨ (fourAdjacentNode i).val + 1 = i.val := by
  fin_cases i <;> simp [fourAdjacentNode]

/-- Adding the chosen adjacent node gives a strict geometric enlargement. -/
theorem four_single_node_lt (b : Basis 3) (i : Fin 3) :
    fourParabolic b {i} < fourParabolic b {i, fourAdjacentNode i} := by
  apply (fourParabolic_lt_iff b _ _).mpr
  have hne : fourAdjacentNode i ≠ i := by
    have := fourAdjacentNode_adjacent i
    intro h
    rw [h] at this
    omega
  simpa only [Set.pair_comm] using
    (Set.ssubset_insert (s := {i}) (a := fourAdjacentNode i) (by simpa using hne))

/-- Every node parabolic contains the actual complete-flag stabilizer. -/
theorem fullFlag_le_fourParabolic (b : Basis 3) (nodes : Set (Fin 3)) :
    cutStabilizer b Set.univ ≤ fourParabolic b nodes :=
  (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)

/-- The Sylow two-subgroup attached to the supplied full-flag marking. -/
noncomputable def fourFlagSylow (b : Basis 3) : Sylow 2 (LinearGroup 4) :=
  (standardBasis.equiv b (Equiv.refl _)) • standardSylow

/-- The constructed Sylow subgroup is literally the full-flag stabilizer. -/
theorem fourFlagSylow_coe (b : Basis 3) :
    (fourFlagSylow b : Subgroup (LinearGroup 4)) = cutStabilizer b Set.univ := by
  change (cutStabilizer standardBasis Set.univ).map
    (MulAut.conj (standardBasis.equiv b (Equiv.refl _))).toMonoidHom = _
  rw [cutStabilizer_map_conj]
  congr 1
  ext i
  simp

/-- A singleton-cut stabilizer is the same embedded subspace stabilizer. -/
noncomputable def fourCutStabilizerEquiv (b : Basis 3) (i : Fin 3) :
    cutStabilizer b {i} ≃* parabolic (cutSpace b i) :=
  MulEquiv.subgroupCongr (by simp [cutStabilizer])

/-- The two actions induced by the same ambient automorphism. -/
noncomputable def fourCutBlockAction (b : Basis 3) (i : Fin 3) :
    cutStabilizer b {i} →* BinaryLinear.GL (cutSpace b i) × BinaryLinear.GL (Space 4 ⧸ cutSpace b i) :=
  (blockAction (cutSpace b i)).comp (fourCutStabilizerEquiv b i).toMonoidHom

/-- Both subquotient automorphisms lift simultaneously. -/
theorem fourCutBlockAction_surjective (b : Basis 3) (i : Fin 3) :
    Function.Surjective (fourCutBlockAction b i) :=
  (blockAction_surjective _).comp (fourCutStabilizerEquiv b i).surjective

/-- The common action kernel is exactly the intrinsic two-core. -/
theorem ker_fourCutBlockAction (b : Basis 3) (i : Fin 3) :
    (fourCutBlockAction b i).ker = pCore 2 (cutStabilizer b {i}) := by
  have hc := pCore_map_iso 2 (fourCutStabilizerEquiv b i)
  ext g
  change blockAction (cutSpace b i) (fourCutStabilizerEquiv b i g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, ker_blockAction_eq_twoCore, ← hc]
  simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

/-- The actual two-core quotient retains both geometric diagonal blocks. -/
noncomputable def fourCutQuotientEquiv (b : Basis 3) (i : Fin 3) :
    (cutStabilizer b {i} ⧸ pCore 2 (cutStabilizer b {i})) ≃*
      BinaryLinear.GL (cutSpace b i) × BinaryLinear.GL (Space 4 ⧸ cutSpace b i) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_fourCutBlockAction b i).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (fourCutBlockAction_surjective b i))

/-- Coordinates on the marked cut space. -/
noncomputable def fourCutCoordinates (b : Basis 3) (i : Fin 3) :
    cutSpace b i ≃ₗ[ZMod 2] Space (i.val + 1) :=
  LinearEquiv.ofFinrankEq _ _ (by rw [cutSpace_finrank, Module.finrank_fin_fun])

/-- Coordinates on the quotient by the marked cut space. -/
noncomputable def fourQuotientCoordinates (b : Basis 3) (i : Fin 3) :
    (Space 4 ⧸ cutSpace b i) ≃ₗ[ZMod 2] Space (3 - i.val) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_fin_fun]
    have hd := (cutSpace b i).finrank_quotient_add_finrank
    change Module.finrank (ZMod 2) (Space 4 ⧸ cutSpace b i) +
      Module.finrank (ZMod 2) (cutSpace b i) = Module.finrank (ZMod 2) (Space 4) at hd
    rw [cutSpace_finrank, Module.finrank_fin_fun] at hd
    omega)

local instance : Unique (LinearGroup 1) :=
  { default := 1
    uniq := fun _g => (slEquivLinear 1).symm.injective (Subsingleton.elim _ _) }

/-- The line stabilizer has intrinsic two-core quotient PSL₃(2). -/
noncomputable def fourLineQuotientEquiv (b : Basis 3) :
    (cutStabilizer b {0} ⧸ pCore 2 (cutStabilizer b {0})) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (fourCutQuotientEquiv b 0).trans
    (((linearGroupCongr (fourCutCoordinates b 0)).prodCongr
      (linearGroupCongr (fourQuotientCoordinates b 0))).trans
        ((MulEquiv.uniqueProd (N := LinearGroup 1) (M := LinearGroup 3)).trans linearThreeEquivProjective))

/-- The hyperplane stabilizer has intrinsic two-core quotient PSL₃(2). -/
noncomputable def fourHyperplaneQuotientEquiv (b : Basis 3) :
    (cutStabilizer b {2} ⧸ pCore 2 (cutStabilizer b {2})) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  (fourCutQuotientEquiv b 2).trans
    (((linearGroupCongr (fourCutCoordinates b 2)).prodCongr
      (linearGroupCongr (fourQuotientCoordinates b 2))).trans
        ((MulEquiv.prodUnique (N := LinearGroup 1) (M := LinearGroup 3)).trans linearThreeEquivProjective))

/-- The adjacent-node quotient, transported through literal stabilizer equalities. -/
noncomputable def fourEnlargedQuotientEquiv (b : Basis 3) (i : Fin 3) :
    (fourParabolic b {i, fourAdjacentNode i} ⧸
      pCore 2 (fourParabolic b {i, fourAdjacentNode i})) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) := by
  classical
  by_cases h : i = 2
  · have he : ({i, fourAdjacentNode i} : Set (Fin 3))ᶜ = {0} := by
      subst i
      ext j; fin_cases j <;> simp [fourAdjacentNode]
    let a : fourParabolic b {i, fourAdjacentNode i} ≃* cutStabilizer b {0} :=
      MulEquiv.subgroupCongr (congrArg (cutStabilizer b) he)
    exact (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans (fourLineQuotientEquiv b)
  · have he : ({i, fourAdjacentNode i} : Set (Fin 3))ᶜ = {2} := by
      fin_cases i <;> (ext j; fin_cases j <;> simp_all [fourAdjacentNode])
    let a : fourParabolic b {i, fourAdjacentNode i} ≃* cutStabilizer b {2} :=
      MulEquiv.subgroupCongr (congrArg (cutStabilizer b) he)
    exact (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans (fourHyperplaneQuotientEquiv b)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

/-- For the line orientation, PSL₃(2) acts on the actual quotient three-space. -/
theorem fourLineQuotientEquiv_mk (b : Basis 3) (g : cutStabilizer b {0}) :
    fourLineQuotientEquiv b (QuotientGroup.mk' _ g) =
      linearThreeEquivProjective (linearGroupCongr (fourQuotientCoordinates b 0)
        (quotientAction (cutSpace b 0) (fourCutStabilizerEquiv b 0 g))) := rfl

/-- For the hyperplane orientation, PSL₃(2) acts on the actual marked three-space. -/
theorem fourHyperplaneQuotientEquiv_mk (b : Basis 3) (g : cutStabilizer b {2}) :
    fourHyperplaneQuotientEquiv b (QuotientGroup.mk' _ g) =
      linearThreeEquivProjective (linearGroupCongr (fourCutCoordinates b 2)
        (subspaceAction (cutSpace b 2) (fourCutStabilizerEquiv b 2 g))) := rfl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
