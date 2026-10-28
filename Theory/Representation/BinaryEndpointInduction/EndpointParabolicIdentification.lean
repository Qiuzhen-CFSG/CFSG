module

public import Theory.Representation.BinaryEndpointInduction.ParabolicSeedMarking
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.InvariantSubspaces
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.GraphDuality

/-!
# Exact marking of the two endpoint parabolics

The supplied basis is first sent to the standard coordinates. Inverse transpose
sends the first-coordinate line stabilizer to the row-e0 parabolic; the literal
four-cycle sends the last endpoint hyperplane to the same hyperplane x0 = 0.
Thus either actual endpoint admits a marking by the parabolic used in the
45-dimensional induction. No classification of arbitrary automorphisms is used.
-/

public noncomputable section
open Matrix Subgroup BinaryLinear BinaryLinear.OuterCyclic
  BinaryLinear.InvariantNodeActions
open scoped MatrixGroups
namespace BinaryEndpointInduction

private def coordinateBasis : InvariantNodeActions.Basis 3 :=
  Pi.basisFun (ZMod 2) (Fin 4)

private def firstHyperplane : Submodule (ZMod 2) (Space 4) :=
  (LinearMap.proj (0 : Fin 4)).ker

private theorem mem_coordinate_cut (i : Fin 3) (x : Space 4) :
    x ∈ cutSpace coordinateBasis i ↔ ∀ j : Fin 4, i.val < j.val → x j = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin 4, x j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hx
    exact Nat.not_le_of_gt hj (h j hx)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

private theorem coordinate_cut_two (x : Space 4) :
    x ∈ cutSpace coordinateBasis 2 ↔ x 3 = 0 := by
  rw [mem_coordinate_cut]
  constructor
  · intro h
    exact h 3 (by decide)
  · intro h j hj
    have he : j = 3 := by omega
    simpa only [he] using h

private theorem first_orthogonal :
    flagOrthogonal (cutSpace coordinateBasis 0) = firstHyperplane := by
  ext x
  rw [mem_flagOrthogonal]
  change (∀ w ∈ cutSpace coordinateBasis 0, dotProduct w x = 0) ↔ x 0 = 0
  constructor
  · intro h
    have hw : Pi.single (0 : Fin 4) (1 : ZMod 2) ∈ cutSpace coordinateBasis 0 := by
      rw [mem_coordinate_cut]
      intro j hj
      simp [show j ≠ 0 by omega]
    simpa only [single_dotProduct, one_mul] using h _ hw
  · intro hx w hw
    have h1 := (mem_coordinate_cut 0 w).mp hw 1 (by decide)
    have h2 := (mem_coordinate_cut 0 w).mp hw 2 (by decide)
    have h3 := (mem_coordinate_cut 0 w).mp hw 3 (by decide)
    simp [dotProduct, Fin.sum_univ_succ, hx, h1, h2, h3]

private theorem cycle_cut_two :
    (cutSpace coordinateBasis 2).map (slEquivLinear 4 cycleGenerator).toLinearMap =
      firstHyperplane := by
  ext x
  rw [Submodule.mem_map_equiv, coordinate_cut_two]
  change ((cycleGenerator⁻¹).val.mulVec x) 3 = 0 ↔ x 0 = 0
  have hc : ∀ y : Space 4, ((cycleGenerator⁻¹).val.mulVec y) 3 = y 0 := by
    decide +kernel
  rw [hc]

private theorem hyperplane_marking :
    (parabolic firstHyperplane).map (slEquivLinear 4).symm.toMonoidHom =
      endpointParabolic := by
  ext g
  rw [Subgroup.mem_map_equiv]
  change (∀ x : Space 4, (g.val.mulVec x) 0 = 0 ↔ x 0 = 0) ↔
    ∀ k : Fin 4, g.val 0 k = if k = 0 then 1 else 0
  constructor
  · intro hg k
    by_cases hk : k = 0
    · subst k
      have hn : g.val 0 0 ≠ 0 := by
        intro hzero
        have h := (hg (Pi.single 0 1)).mp (by simpa using hzero)
        simp at h
      have h1 : g.val 0 0 = 1 :=
        (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn
      simpa using h1
    · have h := (hg (Pi.single k 1)).mpr (by simp [hk])
      simpa [hk] using h
  · intro hg x
    have he : (g.val.mulVec x) 0 = x 0 := by
      simp [Matrix.mulVec, dotProduct, hg]
    rw [he]

private theorem basis_coordinates (v : InvariantNodeActions.Basis 3)
    (cuts : Set (Fin 3)) :
    (cutStabilizer v cuts).map (MulAut.conj v.equivFun).toMonoidHom =
      cutStabilizer coordinateBasis cuts := by
  rw [cutStabilizer_map_conj]
  congr 1
  ext i j
  simp [coordinateBasis, Module.Basis.equivFun_self, Pi.basisFun_apply,
    Pi.single_apply, eq_comm]

/-- Either endpoint stabilizer, with its supplied basis and subgroup image,
admits an exact marking by the literal parabolic used in endpoint induction. -/
theorem exists_endpointParabolic_marking {X : Type*} [Group X]
    (D : Subgroup X) (a : X ≃* LinearGroup 4) (v : InvariantNodeActions.Basis 3)
    (hD : D.map a.toMonoidHom = cutStabilizer v {0} ∨
      D.map a.toMonoidHom = cutStabilizer v {2}) :
    ∃ e : X ≃* SL(4, ZMod 2), D.map e.toMonoidHom = endpointParabolic := by
  let b : X ≃* LinearGroup 4 := a.trans (MulAut.conj v.equivFun)
  have hb (cuts : Set (Fin 3)) (h : D.map a.toMonoidHom = cutStabilizer v cuts) :
      D.map b.toMonoidHom = cutStabilizer coordinateBasis cuts := by
    change D.map ((MulAut.conj v.equivFun).toMonoidHom.comp a.toMonoidHom) = _
    rw [← Subgroup.map_map, h, basis_coordinates]
  rcases hD with hD | hD
  · refine ⟨(b.trans (graphLinear 4)).trans (slEquivLinear 4).symm, ?_⟩
    change D.map ((slEquivLinear 4).symm.toMonoidHom.comp
      ((graphLinear 4).toMonoidHom.comp b.toMonoidHom)) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, hb {0} hD]
    simp only [cutStabilizer, Set.mem_singleton_iff, iInf_iInf_eq_left]
    rw [graph_map_parabolic, first_orthogonal, hyperplane_marking]
  · refine ⟨(b.trans (MulAut.conj (slEquivLinear 4 cycleGenerator))).trans
      (slEquivLinear 4).symm, ?_⟩
    change D.map ((slEquivLinear 4).symm.toMonoidHom.comp
      ((MulAut.conj (slEquivLinear 4 cycleGenerator)).toMonoidHom.comp b.toMonoidHom)) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, hb {2} hD]
    simp only [cutStabilizer, Set.mem_singleton_iff, iInf_iInf_eq_left]
    rw [inner_map_parabolic, cycle_cut_two, hyperplane_marking]

end BinaryEndpointInduction
