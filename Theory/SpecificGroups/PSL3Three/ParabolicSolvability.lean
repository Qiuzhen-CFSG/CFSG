module

public import Theory.SpecificGroups.PSL3Three.Subgroups
public import Theory.SpecificGroups.SL2.BinaryTetrahedral
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Tactic

/-!
# Solvability of the two parabolics of PSL₃(3)

The stabilizers of the first coordinate line and the last two coordinate
plane are solvable. For each stabilizer in SL₃(3), taking the lower right
two-by-two block defines a homomorphism to GL₂(3). The determinant condition
makes this block invertible. Its kernel consists of unipotent matrices with
two free entries in the first row or first column, and is abelian.

The determinant homomorphism makes GL₂(3) an extension of a subgroup of the
abelian group of field units by SL₂(3). The binary tetrahedral description
SL₂(3) ≃ Q₈ ⋊ C₃ proves this kernel solvable. Solvability then passes to the
specified images of the parabolics in PSL₃(3).

Source: GLS, volume III, Theorem 6.5.3(a), in
`refs/KGroup/GLS3/chapter6.tex`, for the parabolic subgroup alternative.
Here the relevant parabolics have structure 3²:GL₂(3).
-/

namespace Matrix.PSL3Three

open scoped Pointwise

private abbrev F := ZMod 3
private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) F
private abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) F

private theorem gl2_three_isSolvable : Group.IsSolvable GL2 := by
  let hQ : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by norm_num [QuaternionGroup.card])
  let : Group.IsNilpotent (QuaternionGroup 2) := hQ.isNilpotent
  let : Group.IsSolvable
      (QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
        Multiplicative (ZMod 3)) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl
      SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge
  let : Group.IsSolvable SL2 := by
    apply Group.isSolvable_of_surjective
      (G := (QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
        Multiplicative (ZMod 3))) (G' := SL2)
      (f := GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.toMonoidHom)
    exact GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.surjective
  let det := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)
  apply Group.isSolvable_of_ker_le_range (SpecialLinearGroup.toGL (R := F)) det
  intro g hg
  let y : SL2 := ⟨(g : Matrix (Fin 2) (Fin 2) F), by
    have h := congr_arg Units.val hg
    change Matrix.det (g : Matrix (Fin 2) (Fin 2) F) = 1 at h
    exact h⟩
  refine ⟨y, ?_⟩
  apply Units.ext
  rfl

private theorem line_first_col (g : lineStabilizerSL) :
    g.1 1 0 = 0 ∧ g.1 2 0 = 0 := by
  let v : Fin 3 → F := fun i => if i = 0 then 1 else 0
  have hstab : g.1 • ({v : Fin 3 → F | v 1 = 0 ∧ v 2 = 0} : Set (Fin 3 → F)) =
      ({v : Fin 3 → F | v 1 = 0 ∧ v 2 = 0} : Set (Fin 3 → F)) :=
    MulAction.mem_stabilizer_iff.mp g.property
  have hv : v ∈ ({v : Fin 3 → F | v 1 = 0 ∧ v 2 = 0} : Set (Fin 3 → F)) := by
    simp [v]
  have hm := Set.smul_mem_smul_set hv (a := g.1)
  rw [hstab] at hm
  have hm1 := hm.1
  change ((g.1 : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 1 = 0 at hm1
  have hm2 := hm.2
  change ((g.1 : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 2 = 0 at hm2
  constructor
  · simpa [v, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hm1
  · simpa [v, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hm2

private def lineBlock (g : lineStabilizerSL) : Matrix (Fin 2) (Fin 2) F :=
  !![g.1 1 1, g.1 1 2; g.1 2 1, g.1 2 2]

private theorem lineBlock_det_ne_zero (g : lineStabilizerSL) :
    (lineBlock g).det ≠ 0 := by
  obtain ⟨h10, h20⟩ := line_first_col g
  have hd := g.1.prop
  change Matrix.det (g.1 : Matrix (Fin 3) (Fin 3) F) = 1 at hd
  rw [Matrix.det_fin_three] at hd
  simp only [h10, h20, zero_mul, sub_zero, mul_zero, add_zero] at hd
  have hdet : g.1 0 0 * (lineBlock g).det = 1 := by
    calc
      _ = g.1 0 0 * g.1 1 1 * g.1 2 2 - g.1 0 0 * g.1 1 2 * g.1 2 1 := by
        simp [lineBlock, Matrix.det_fin_two]
        ring
      _ = 1 := hd
  intro h
  rw [h] at hdet
  simp at hdet

private def lineRestriction : lineStabilizerSL →* GL2 where
  toFun g := Matrix.GeneralLinearGroup.mkOfDetNeZero (lineBlock g) (lineBlock_det_ne_zero g)
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    obtain ⟨g10, g20⟩ := line_first_col g
    obtain ⟨h10, h20⟩ := line_first_col h
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lineBlock, Matrix.mul_apply, Fin.sum_univ_succ, g10, g20]

private theorem lineRestriction_kernel_commutative :
    ∀ ⦃g h : lineStabilizerSL⦄,
      g ∈ lineRestriction.ker → h ∈ lineRestriction.ker → g * h = h * g := by
  intro g h hg hh
  obtain ⟨g10, g20⟩ := line_first_col g
  obtain ⟨h10, h20⟩ := line_first_col h
  have hg' : lineRestriction g = 1 := hg
  have hh' : lineRestriction h = 1 := hh
  have gb : lineBlock g = 1 := by
    apply Units.ext_iff.mp at hg'
    exact hg'
  have hb : lineBlock h = 1 := by
    apply Units.ext_iff.mp at hh'
    exact hh'
  have g11 : g.1 1 1 = 1 := by simpa [lineBlock] using congr_fun (congr_fun gb 0) 0
  have g12 : g.1 1 2 = 0 := by simpa [lineBlock] using congr_fun (congr_fun gb 0) 1
  have g21 : g.1 2 1 = 0 := by simpa [lineBlock] using congr_fun (congr_fun gb 1) 0
  have g22 : g.1 2 2 = 1 := by simpa [lineBlock] using congr_fun (congr_fun gb 1) 1
  have h11 : h.1 1 1 = 1 := by simpa [lineBlock] using congr_fun (congr_fun hb 0) 0
  have h12 : h.1 1 2 = 0 := by simpa [lineBlock] using congr_fun (congr_fun hb 0) 1
  have h21 : h.1 2 1 = 0 := by simpa [lineBlock] using congr_fun (congr_fun hb 1) 0
  have h22 : h.1 2 2 = 1 := by simpa [lineBlock] using congr_fun (congr_fun hb 1) 1
  have ga : g.1 0 0 = 1 := by
    have hd := g.1.prop
    change Matrix.det (g.1 : Matrix (Fin 3) (Fin 3) F) = 1 at hd
    rw [Matrix.det_fin_three] at hd
    simp only [g10, g20, g11, g12, g21, g22, sub_zero, mul_one, mul_zero, add_zero] at hd
    exact hd
  have ha : h.1 0 0 = 1 := by
    have hd := h.1.prop
    change Matrix.det (h.1 : Matrix (Fin 3) (Fin 3) F) = 1 at hd
    rw [Matrix.det_fin_three] at hd
    simp only [h10, h20, h11, h12, h21, h22, sub_zero, mul_one, mul_zero, add_zero] at hd
    exact hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, g10, g20, h10, h20, ga, ha,
      g11, g12, g21, g22, h11, h12, h21, h22, add_comm]

private theorem lineStabilizerSL_isSolvable : Group.IsSolvable lineStabilizerSL := by
  let : Group.IsSolvable GL2 := gl2_three_isSolvable
  let : Group.IsSolvable lineRestriction.ker :=
    Group.isSolvable_of_comm (fun g h => by
      apply Subtype.ext
      exact lineRestriction_kernel_commutative (g := g.1) (h := h.1) g.2 h.2)
  apply Group.isSolvable_of_ker_le_range lineRestriction.ker.subtype lineRestriction
  rw [lineRestriction.ker.subtype.range_eq_map]
  intro x hx
  exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

private def lineMap : lineStabilizerSL →* lineStabilizer :=
  (project.comp lineStabilizerSL.subtype).codRestrict lineStabilizer (by
    intro g
    exact ⟨g.1, g.2, rfl⟩)

private theorem lineMap_surjective : Function.Surjective lineMap := by
  intro g
  obtain ⟨x, hx, hxg⟩ := g.2
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxg

/-- The stabilizer of the first coordinate line in PSL₃(3) is solvable. -/
public theorem lineStabilizer_isSolvable : Group.IsSolvable lineStabilizer := by
  let : Group.IsSolvable lineStabilizerSL := lineStabilizerSL_isSolvable
  exact Group.isSolvable_of_surjective lineMap_surjective

private theorem plane_first_row (g : planeStabilizerSL) :
    g.1 0 1 = 0 ∧ g.1 0 2 = 0 := by
  let v1 : Fin 3 → F := fun i => if i = 1 then 1 else 0
  let v2 : Fin 3 → F := fun i => if i = 2 then 1 else 0
  have hstab : g.1 • ({v : Fin 3 → F | v 0 = 0} : Set (Fin 3 → F)) =
      ({v : Fin 3 → F | v 0 = 0} : Set (Fin 3 → F)) :=
    MulAction.mem_stabilizer_iff.mp g.property
  have hv1 : v1 ∈ ({v : Fin 3 → F | v 0 = 0} : Set (Fin 3 → F)) := by simp [v1]
  have hv2 : v2 ∈ ({v : Fin 3 → F | v 0 = 0} : Set (Fin 3 → F)) := by simp [v2]
  have hm1 := Set.smul_mem_smul_set hv1 (a := g.1)
  have hm2 := Set.smul_mem_smul_set hv2 (a := g.1)
  rw [hstab] at hm1 hm2
  have hm1' := hm1
  have hm2' := hm2
  change ((g.1 : Matrix (Fin 3) (Fin 3) F) *ᵥ v1) 0 = 0 at hm1'
  change ((g.1 : Matrix (Fin 3) (Fin 3) F) *ᵥ v2) 0 = 0 at hm2'
  constructor
  · simpa [v1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hm1'
  · simpa [v2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hm2'

private def planeBlock (g : planeStabilizerSL) : Matrix (Fin 2) (Fin 2) F :=
  !![g.1 1 1, g.1 1 2; g.1 2 1, g.1 2 2]

private theorem planeBlock_det_ne_zero (g : planeStabilizerSL) :
    (planeBlock g).det ≠ 0 := by
  obtain ⟨h01, h02⟩ := plane_first_row g
  have hd := g.1.prop
  change Matrix.det (g.1 : Matrix (Fin 3) (Fin 3) F) = 1 at hd
  rw [Matrix.det_fin_three] at hd
  simp only [h01, h02, zero_mul, sub_zero, add_zero] at hd
  ring_nf at hd
  have hdet : g.1 0 0 * (planeBlock g).det = 1 := by
    calc
      _ = g.1 0 0 * g.1 1 1 * g.1 2 2 - g.1 0 0 * g.1 1 2 * g.1 2 1 := by
        simp [planeBlock, Matrix.det_fin_two]
        ring
      _ = 1 := hd
  intro h
  rw [h] at hdet
  simp at hdet

private def planeRestriction : planeStabilizerSL →* GL2 where
  toFun g := Matrix.GeneralLinearGroup.mkOfDetNeZero (planeBlock g) (planeBlock_det_ne_zero g)
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    obtain ⟨g01, g02⟩ := plane_first_row g
    obtain ⟨h01, h02⟩ := plane_first_row h
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeBlock, Matrix.mul_apply, Fin.sum_univ_succ, h01, h02]

private theorem planeRestriction_kernel_commutative :
    ∀ ⦃g h : planeStabilizerSL⦄,
      g ∈ planeRestriction.ker → h ∈ planeRestriction.ker → g * h = h * g := by
  intro g h hg hh
  obtain ⟨g01, g02⟩ := plane_first_row g
  obtain ⟨h01, h02⟩ := plane_first_row h
  have hg' : planeRestriction g = 1 := hg
  have hh' : planeRestriction h = 1 := hh
  have gb : planeBlock g = 1 := by
    apply Units.ext_iff.mp at hg'
    exact hg'
  have hb : planeBlock h = 1 := by
    apply Units.ext_iff.mp at hh'
    exact hh'
  have g11 : g.1 1 1 = 1 := by simpa [planeBlock] using congr_fun (congr_fun gb 0) 0
  have g12 : g.1 1 2 = 0 := by simpa [planeBlock] using congr_fun (congr_fun gb 0) 1
  have g21 : g.1 2 1 = 0 := by simpa [planeBlock] using congr_fun (congr_fun gb 1) 0
  have g22 : g.1 2 2 = 1 := by simpa [planeBlock] using congr_fun (congr_fun gb 1) 1
  have h11 : h.1 1 1 = 1 := by simpa [planeBlock] using congr_fun (congr_fun hb 0) 0
  have h12 : h.1 1 2 = 0 := by simpa [planeBlock] using congr_fun (congr_fun hb 0) 1
  have h21 : h.1 2 1 = 0 := by simpa [planeBlock] using congr_fun (congr_fun hb 1) 0
  have h22 : h.1 2 2 = 1 := by simpa [planeBlock] using congr_fun (congr_fun hb 1) 1
  have ga : g.1 0 0 = 1 := by
    have hd := g.1.prop
    change Matrix.det (g.1 : Matrix (Fin 3) (Fin 3) F) = 1 at hd
    rw [Matrix.det_fin_three] at hd
    simp only [g01, g02, g11, g12, g21, g22, sub_zero, mul_one, mul_zero, add_zero] at hd
    ring_nf at hd
    exact hd
  have ha : h.1 0 0 = 1 := by
    have hd := h.1.prop
    change Matrix.det (h.1 : Matrix (Fin 3) (Fin 3) F) = 1 at hd
    rw [Matrix.det_fin_three] at hd
    simp only [h01, h02, h11, h12, h21, h22, sub_zero, mul_one, mul_zero, add_zero] at hd
    ring_nf at hd
    exact hd
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem planeStabilizerSL_isSolvable : Group.IsSolvable planeStabilizerSL := by
  let : Group.IsSolvable GL2 := gl2_three_isSolvable
  let : Group.IsSolvable planeRestriction.ker :=
    Group.isSolvable_of_comm (fun g h => by
      apply Subtype.ext
      exact planeRestriction_kernel_commutative (g := g.1) (h := h.1) g.2 h.2)
  apply Group.isSolvable_of_ker_le_range planeRestriction.ker.subtype planeRestriction
  rw [planeRestriction.ker.subtype.range_eq_map]
  intro x hx
  exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

private def planeMap : planeStabilizerSL →* planeStabilizer :=
  (project.comp planeStabilizerSL.subtype).codRestrict planeStabilizer (by
    intro g
    exact ⟨g.1, g.2, rfl⟩)

private theorem planeMap_surjective : Function.Surjective planeMap := by
  intro g
  obtain ⟨x, hx, hxg⟩ := g.2
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxg

/-- The stabilizer of the last two coordinate plane in PSL₃(3) is solvable. -/
public theorem planeStabilizer_isSolvable : Group.IsSolvable planeStabilizer := by
  let : Group.IsSolvable planeStabilizerSL := planeStabilizerSL_isSolvable
  exact Group.isSolvable_of_surjective planeMap_surjective

end Matrix.PSL3Three
