module


public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.Reduction

/-!
# Faithfulness of binary octad reduction modulo the scalar sign

A norm-32 vector is determined up to sign by its class modulo twice Leech.
The all-positive octad root has nonzero pairing with every positive
two-coordinate root. Hence an isometry trivial modulo two uses one common
sign on all these roots. Their sums and differences recover every coordinate
axis, so the isometry is scalar on the entire octad lattice.

This proves equality of the actual projective lattice kernel with the
binary reduction kernel, independently of extraspeciality.

Source: Aschbacher, *Sporadic Groups* (1994), 25.2 and 25.5, pp.133–134.
-/

@[expose] public noncomputable section
open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped BigOperators

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage.LatticeModel

def axis (i : Coordinate) : lattice := ⟨coordinateEight i.val, by
  rw [mem_lattice_iff_support]
  intro j hj
  have hji : j ≠ i.val := fun he => i.prop (he ▸ hj)
  simp [coordinateEight, coordinateVector, hji]⟩

def pairRoot (i j : Coordinate) : lattice := ⟨minimumPairPlus i.val j.val, by
  rw [mem_lattice_iff_support]
  intro k hk
  have hki : k ≠ i.val := fun he => i.prop (he ▸ hk)
  have hkj : k ≠ j.val := fun he => j.prop (he ▸ hk)
  simp [minimumPairPlus, coordinateVector, hki, hkj]⟩

/-- The stabilizer of the coordinate-axis class is exactly the actual
monomial part of the Leech centralizer. -/
theorem fixes_axis_class_iff_monomial (g : centralizer) (i : Coordinate) :
    linearAction g (reduction (axis i)) = reduction (axis i) ↔
      g.val ∈ monomialSubgroup := by
  rw [← standardCrossStabilizer_eq_monomial, standardCrossStabilizer_mem]
  have he : standardCross = standardCrossAt i.val := standardCross_independent _ _
  rw [he]
  constructor
  · intro h
    apply Subtype.ext
    exact congrArg leechInclusion h
  · intro h
    apply leechInclusion_injective
    exact congrArg Subtype.val h

def positiveRoot : lattice := coordinateEquiv.symm
  ⟨fun _ => 2, (mem_coordinateModel _).mpr ⟨Or.inr (fun _ => by norm_num), by
    rw [Finset.sum_const, Finset.card_univ, coordinate_card]
    norm_num⟩⟩

theorem positiveRoot_coordinate (i : Coordinate) : positiveRoot.val.val i.val = 2 := by
  change extendCoordinates (fun _ => 2) i.val = 2
  simp [extendCoordinates, i.prop]

theorem dot_coordinates (x y : lattice) :
    integerDot x.val.val y.val.val =
      ∑ i : Coordinate, x.val.val i.val * y.val.val i.val := by
  symm
  apply Fintype.sum_of_injective (fun i : Coordinate => i.val) Subtype.val_injective
  · intro i hi
    have hz : (golayBasis 0).val i = 0 := by
      by_contra hn
      exact hi ⟨⟨i, hn⟩, rfl⟩
    rw [(mem_lattice_iff_support x.val).mp x.prop i hz, zero_mul]
  · intro i
    rfl

theorem positiveRoot_norm : integerDot positiveRoot.val.val positiveRoot.val.val = 32 := by
  rw [dot_coordinates]
  simp only [positiveRoot_coordinate, Finset.sum_const, Finset.card_univ, coordinate_card]
  norm_num

theorem pairRoot_norm (i j : Coordinate) (hij : i ≠ j) :
    integerDot (pairRoot i j).val.val (pairRoot i j).val.val = 32 :=
  minimumPairPlus_norm _ _ (fun h => hij (Subtype.ext h))

theorem dot_pairRoot (x : lattice) (i j : Coordinate) :
    integerDot x.val.val (pairRoot i j).val.val =
      4 * x.val.val i.val + 4 * x.val.val j.val := by
  simp [integerDot, pairRoot, minimumPairPlus, coordinateVector, add_mul,
    Finset.sum_add_distrib, Pi.single_apply, mul_comm]

theorem positiveRoot_dot_pairRoot (i j : Coordinate) :
    integerDot positiveRoot.val.val (pairRoot i j).val.val = 16 := by
  rw [dot_pairRoot, positiveRoot_coordinate, positiveRoot_coordinate]
  norm_num

theorem dot_axis (x : lattice) (i : Coordinate) :
    integerDot x.val.val (axis i).val.val = 8 * x.val.val i.val := by
  simp [integerDot, axis, coordinateEight, coordinateVector, Pi.single_apply, mul_comm]

theorem axis_norm (i : Coordinate) :
    integerDot (axis i).val.val (axis i).val.val = 64 := by
  rw [dot_axis]
  norm_num [axis, coordinateEight, coordinateVector]

theorem axis_class_ne_zero (i : Coordinate) : reduction (axis i) ≠ 0 := by
  intro h
  have hn : (axis i).val ≠ 0 := by
    intro hz
    have hh := congrArg (fun x : leech => x.val i.val) hz
    norm_num [axis, coordinateEight, coordinateVector] at hh
  have hz : leechReduction (axis i).val = 0 := by
    have hh := congrArg leechInclusion h
    simpa only [leechInclusion_reduction, map_zero] using hh
  have hm := leech_zero_class_min (axis i).val hn hz
  dsimp [leechHalfNorm] at hm
  rw [axis_norm] at hm
  norm_num at hm

theorem Coordinates.axis_ne_zero (C : Coordinates) (i : Coordinate) :
    C.coordinates (reduction (axis i)) ≠ 0 := by
  intro h
  exact axis_class_ne_zero i (C.coordinates.injective (h.trans (map_zero _).symm))

theorem Coordinates.axis_singular (C : Coordinates) (i : Coordinate) :
    SelectedGeometry.form (C.coordinates (reduction (axis i))) = 0 := by
  rw [C.norm, axis_norm]
  decide

theorem pairRoot_axis (i j k : Coordinate) :
    pairRoot i j + pairRoot i k - pairRoot j k = axis i := by
  apply Subtype.ext
  apply Subtype.ext
  funext a
  simp only [pairRoot, axis, minimumPairPlus, coordinateEight, coordinateVector,
    Submodule.coe_add, Submodule.coe_sub, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> ring

/-- Kernel elements fix each short root up to sign, in the actual lattice. -/
theorem kernel_short_root (g : centralizer) (hg : g ∈ linearAction.ker)
    (x : lattice) (hx : integerDot x.val.val x.val.val = 32) :
    action g x = x ∨ action g x = -x := by
  have hred : leechReduction (action g x).val = leechReduction x.val := by
    have hh := congrArg (fun f : ModTwo ≃ₗ[ZMod 2] ModTwo =>
      leechInclusion (f (reduction x))) (MonoidHom.mem_ker.mp hg)
    exact hh
  have hnorm := action_preserves_form g x x
  have hh := leech_congruent_short_unique (action g x).val x.val hred (by
    dsimp [leechHalfNorm]
    rw [hnorm, hx]
    norm_num)
  exact hh.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)

theorem fixes_pairRoots_of_fixes_positiveRoot (g : centralizer)
    (hg : g ∈ linearAction.ker) (hr : action g positiveRoot = positiveRoot)
    (i j : Coordinate) (hij : i ≠ j) : action g (pairRoot i j) = pairRoot i j := by
  rcases kernel_short_root g hg (pairRoot i j) (pairRoot_norm i j hij) with h | h
  · exact h
  · have hp := action_preserves_form g positiveRoot (pairRoot i j)
    rw [hr, h] at hp
    have hn : integerDot positiveRoot.val.val (-pairRoot i j).val.val =
        -integerDot positiveRoot.val.val (pairRoot i j).val.val := by
      simp [integerDot]
    rw [hn, positiveRoot_dot_pairRoot] at hp
    omega

private theorem two_other_coordinates (i : Coordinate) :
    ∃ j k : Coordinate, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  classical
  have hi : 1 < Fintype.card Coordinate := by rw [coordinate_card]; decide
  let : Nontrivial Coordinate := Fintype.one_lt_card_iff_nontrivial.mp hi
  obtain ⟨j, hji⟩ := exists_ne i
  have hc : ({i, j} : Finset Coordinate).card < (Finset.univ : Finset Coordinate).card := by
    have := Finset.card_le_two (a := i) (b := j)
    rw [Finset.card_univ, coordinate_card]
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨j, k, hji.symm, (fun h => hk.1 h.symm), (fun h => hk.2 h.symm)⟩

theorem fixes_axes_of_fixes_positiveRoot (g : centralizer)
    (hg : g ∈ linearAction.ker) (hr : action g positiveRoot = positiveRoot)
    (i : Coordinate) : action g (axis i) = axis i := by
  obtain ⟨j, k, hij, hik, hjk⟩ := two_other_coordinates i
  rw [← pairRoot_axis i j k, map_sub, map_add,
    fixes_pairRoots_of_fixes_positiveRoot g hg hr i j hij,
    fixes_pairRoots_of_fixes_positiveRoot g hg hr i k hik,
    fixes_pairRoots_of_fixes_positiveRoot g hg hr j k hjk]

theorem mem_action_ker_of_fixes_axes (g : centralizer)
    (hg : ∀ i : Coordinate, action g (axis i) = axis i) : g ∈ action.ker := by
  rw [MonoidHom.mem_ker]
  apply LinearEquiv.ext
  intro x
  apply coordinates_injective
  funext i
  have h := action_preserves_form g x (axis i)
  rw [hg i, dot_axis, dot_axis] at h
  change (action g x).val.val i.val = x.val.val i.val
  omega

/-- Reduction has no further kernel beyond the literal pointwise kernel and
the scalar sign. This uses the short roots, not an order comparison. -/
theorem linearAction_ker_eq_projectiveLatticeKernel :
    linearAction.ker = projectiveLatticeKernel := by
  apply le_antisymm ?_ projectiveLatticeKernel_le_linearAction_ker
  intro g hg
  rcases kernel_short_root g hg positiveRoot positiveRoot_norm with hp | hp
  · exact (show action.ker ≤ projectiveLatticeKernel from le_sup_left) (mem_action_ker_of_fixes_axes g
      (fixes_axes_of_fixes_positiveRoot g hg hp))
  · have hs : octadSign ∈ linearAction.ker :=
      projectiveLatticeKernel_le_linearAction_ker
        ((show Subgroup.zpowers octadSign ≤ projectiveLatticeKernel from le_sup_right)
          (Subgroup.mem_zpowers _))
    have hgs : g * octadSign ∈ action.ker := by
      apply mem_action_ker_of_fixes_axes
      apply fixes_axes_of_fixes_positiveRoot (g * octadSign) (linearAction.ker.mul_mem hg hs)
      rw [map_mul]
      change action g (action octadSign positiveRoot) = positiveRoot
      rw [action_octadSign, map_neg, hp, neg_neg]
    have hm : g * octadSign ∈ projectiveLatticeKernel :=
      (show action.ker ≤ projectiveLatticeKernel from le_sup_left) hgs
    have hs' : octadSign ∈ projectiveLatticeKernel :=
      (show Subgroup.zpowers octadSign ≤ projectiveLatticeKernel from le_sup_right)
        (Subgroup.mem_zpowers _)
    simpa only [mul_inv_cancel_right] using projectiveLatticeKernel.mul_mem hm
      (projectiveLatticeKernel.inv_mem hs')

/-- A genuine embedding of the published projective lattice image. -/
theorem Coordinates.projectiveAction_injective (C : Coordinates) :
    Function.Injective C.projectiveAction := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  exact (C.orthogonalAction_ker.trans linearAction_ker_eq_projectiveLatticeKernel).symm

end Realization.OmegaImage.LatticeModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
