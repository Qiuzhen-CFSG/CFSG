module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Model
public import Theory.GroupTheory.RegularWreathSubgroup
public import Theory.SpecificGroups.PSL3Two.Parabolics.PointNormalizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# The paired nonzero-point stabilizer

Move each nonzero binary column independently to the standard first basis
vector. The stabilizer of the constant pair consists exactly of wreath
elements whose two base coordinates belong to the standard point parabolic.
The coordinate-subgroup equivalence and the checked point-parabolic S₄ model
identify the whole stabilizer with S₄ wr C₂, before any two-core quotient.

The point parabolic is maximal and self-normalizing, so its coordinate
subgroup is maximal by the structural regular-wreath theorem. Conjugation
then proves maximality for every pair with both coordinates nonzero. All
transport uses the literal action of Natural.Model and its inverse shift.

Source: Aschbacher--Smith 10.2.4 and 10.2.11, pp.747,753--754.
-/

public noncomputable section
open scoped Matrix
open Subgroup Matrix.PSL3Two
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.PointModel

private def standardPair : Space := fun _ => Multiplicative.ofAdd flagPoint.val

private theorem standardPair_stabilizer :
    pointStabilizer standardPair =
      RegularWreathProduct.coordinateSubgroup (Q := Bit) pointParabolicSL := by
  ext g
  rw [mem_pointStabilizer, RegularWreathProduct.mem_coordinateSubgroup]
  constructor
  · intro h i
    have he := congrArg (fun f : Space => (f i).toAdd) h
    change (g.left i).val *ᵥ flagPoint.val = flagPoint.val at he
    rw [← Fano.stabilizer_flagPoint_SL]
    exact Subtype.ext he
  · intro h
    funext i
    have hi : g.left i ∈ MulAction.stabilizer SL flagPoint := by
      rw [Fano.stabilizer_flagPoint_SL]
      exact h i
    exact congrArg Multiplicative.ofAdd (congrArg Subtype.val hi)

private theorem exists_standardPair_action (v : Space) (hv : ∀ i, v i ≠ 1) :
    ∃ g : Actor, action g standardPair = v := by
  have hnonzero (i : Bit) : (v i).toAdd ≠ 0 := by
    intro h
    exact hv i (congrArg Multiplicative.ofAdd h)
  have hex (i : Bit) : ∃ g : SL, g.val *ᵥ flagPoint.val = (v i).toAdd :=
    Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ flagPoint.property (hnonzero i)
  choose f hf using hex
  refine ⟨⟨f,1⟩, ?_⟩
  funext i
  exact congrArg Multiplicative.ofAdd (hf i)

private theorem pointStabilizer_action (g : Actor) (v : Space) :
    pointStabilizer (action g v) =
      (pointStabilizer v).map (MulAut.conj g).toMonoidHom := by
  let _ : MulAction Actor Space := MulAction.compHom Space action
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g v

/-- Every nonzero pair has a maximal stabilizer in the full paired actor. -/
theorem pointStabilizer_isCoatom (v : Space) (hv : ∀ i, v i ≠ 1) :
    IsCoatom (pointStabilizer v) := by
  obtain ⟨g, hg⟩ := exists_standardPair_action v hv
  rw [← hg, pointStabilizer_action]
  apply (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup _).mpr
  rw [standardPair_stabilizer]
  exact RegularWreathProduct.coordinateSubgroup_isCoatom pointParabolicSL
    isCoatom_pointParabolicSL pointParabolicSL_normalizer

/-- The whole stabilizer, with no quotient, is the actual S₄ wreath product. -/
def pointStabilizerEquivSymmetricWreath (v : Space) (hv : ∀ i, v i ≠ 1) :
    pointStabilizer v ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) Bit := by
  let g := Classical.choose (exists_standardPair_action v hv)
  have hg := Classical.choose_spec (exists_standardPair_action v hv)
  have he : pointStabilizer v =
      (pointStabilizer standardPair).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, pointStabilizer_action]
  exact (MulEquiv.subgroupCongr he).trans
    (((MulAut.conj g).subgroupMap (pointStabilizer standardPair)).symm.trans
      ((MulEquiv.subgroupCongr standardPair_stabilizer).trans
        ((RegularWreathProduct.coordinateSubgroupEquiv pointParabolicSL).trans
          (RegularWreathProduct.congr MarkedAutomorphisms.pointEquivSymmetric
            (MulEquiv.refl Bit)))))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.PointModel
