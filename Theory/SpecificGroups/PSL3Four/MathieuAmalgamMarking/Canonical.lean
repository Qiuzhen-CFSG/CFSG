module

public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Generation
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.DerivedModel
public import Theory.SpecificGroups.PSL3.CartanActions.FullTorusFixer

/-!
# The literal canonical point-parabolic marking

The checked two-generator matrix subgroup maps onto the whole original
point parabolic. The coordinate three-cycle lies outside it, so maximality
proves full PSL3(4) generation. The shared torus/reflection words and exact
thirteen relations are those already retained in Matrices.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3Four.MathieuAmalgamMarking
open Matrix.PSL3.LinearThree

private def fieldIso : NativeSL ≃* SL :=
  { fieldMap with
    invFun := SpecialLinearGroup.map Representation.SL2FourNatural.fieldEquiv.symm.toRingHom
    left_inv := fun g => by
      apply Subtype.ext
      funext i j
      exact Representation.SL2FourNatural.fieldEquiv.symm_apply_apply (g.val i j)
    right_inv := fun g => by
      apply Subtype.ext
      funext i j
      exact Representation.SL2FourNatural.fieldEquiv.apply_symm_apply (g.val i j) }

private theorem point_local_comap : (pointLocalSL F).comap fieldMap = pointLocalSL NativeF := by
  ext g
  change fieldMap g ∈ pointLocalSL F ↔ g ∈ pointLocalSL NativeF
  rw [mem_pointLocalSL_iff,mem_pointLocalSL_iff]
  change Representation.SL2FourNatural.fieldEquiv (g.val 0 0) = 1 ∧
    Representation.SL2FourNatural.fieldEquiv (g.val 1 0) = 0 ∧
    Representation.SL2FourNatural.fieldEquiv (g.val 2 0) = 0 ↔ _
  simp only [←map_one Representation.SL2FourNatural.fieldEquiv,
    ←map_zero Representation.SL2FourNatural.fieldEquiv,
    Representation.SL2FourNatural.fieldEquiv.injective.eq_iff]

/-- The same explicit pair generates the entire literal canonical point parabolic. -/
theorem pair_generates_point : closure (Set.range pair) = pointParabolic F := by
  have hmap : (pointLocalSL NativeF).map fieldMap = pointLocalSL F := by
    rw [←point_local_comap]
    exact map_comap_eq_self_of_surjective fieldIso.surjective _
  have hp : (pointLocalSL NativeF).map project = pointLocal F := by
    rw [project,←Subgroup.map_map,hmap]
    rfl
  have he := congrArg (Subgroup.map project) native_pair_generates
  rw [MonoidHom.map_closure,←Set.range_comp,hp] at he
  change closure (Set.range pair) = pointLocal F at he
  rw [pointParabolic_eq_sup,sup_eq_left.mpr
    (Matrix.PSL3.CartanActions.FullTorusFixer.borel_le_pointLocal_of_card_four card_F)]
  exact he

/-- The exterior cubic is outside the marked point parabolic. -/
theorem cycle_not_mem_point : cycle ∉ pointParabolic F := by
  intro hh
  have hm : fieldMap nativeCycle ∈ pointParabolicSL F :=
    (show (pointParabolic F).comap (Matrix.PSL3.projection F) = pointParabolicSL F from
      pointParabolic_comap F) ▸ hh
  have hz := ((mem_pointParabolicSL_iff F _).mp hm).2
  change Representation.SL2FourNatural.fieldEquiv (1:NativeF) = 0 at hz
  exact one_ne_zero (by simpa only [map_one] using hz)

/-- These literal three generators generate the whole canonical linear group. -/
theorem pair_cycle_generates : closure (Set.range pair) ⊔ zpowers cycle = ⊤ := by
  rw [pair_generates_point]
  rcases (pointParabolic_isCoatom F).le_iff.mp
      (show pointParabolic F ≤ pointParabolic F ⊔ zpowers cycle from le_sup_left) with ht | he
  · exact ht
  · exact (cycle_not_mem_point (he ▸ mem_sup_right (mem_zpowers cycle))).elim

end Matrix.PSL3Four.MathieuAmalgamMarking
