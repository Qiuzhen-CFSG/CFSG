module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFamily

/-!
# Long roots and extra natural fixed vectors in the plane radical

An actual conjugate of root 0 contained in the standard Sylow has its center
vector in the natural plane: the lower-left diagonal entries of its parameter-one
matrix are squares of the lower coordinates of that vector. Its elements are
therefore symmetric upper shears of rank at most one, with a common fixed vector
outside the plane.

Conversely, a subgroup of the plane radical fixing an extra vector has a common
nonzero lower-coordinate kernel. Choose an SL₂ matrix with that kernel vector
as its second row. Levi conjugation then sends every shear in the subgroup into
the literal root 0. Conjugating that root back supplies an actual long-root
subgroup contained in the plane radical. This includes the trivial subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389, the natural fixed-space-family argument.
-/

public section
open scoped Matrix
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace SymplecticConjugatePair
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

private lemma conjugate_root_matrix (g : Sp F) (t : F) :
    (g * rootElement 0 t * g⁻¹).val = 1 +
      g.val * Matrix.single (.inl 0) (.inr 0) t * (g⁻¹).val := by
  have h : (rootElement 0 t).val = 1 + Matrix.single (.inl 0) (.inr 0) t := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootElement, rootMatrix, fromBlocks, Matrix.single]
  change g.val * (rootElement 0 t).val * (g⁻¹).val = _
  rw [h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  have hi : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  rw [hi]

private lemma conjugate_root_lower (g : Sp F) (i : Fin 2) :
    (g * rootElement 0 1 * g⁻¹).val (.inr i) (.inl i) =
      g.val (.inr i) (.inl 0)^2 := by
  rw [conjugate_root_matrix, SymplecticGroup.coe_inv]
  fin_cases i <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.J, fromBlocks, Matrix.one_apply, CharTwo.neg_eq, pow_two]

private lemma conjugate_root_shear (g : Sp F) (t : F)
    (hz : ∀ i, g.val (.inr i) (.inl 0) = 0) :
    g * rootElement 0 t * g⁻¹ = Plane.shearSp
      ⟨!![t * g.val (.inl 0) (.inl 0)^2,
          t * g.val (.inl 0) (.inl 0) * g.val (.inl 1) (.inl 0);
          t * g.val (.inl 0) (.inl 0) * g.val (.inl 1) (.inl 0),
          t * g.val (.inl 1) (.inl 0)^2], by
        ext i j; fin_cases i <;> fin_cases j <;> rfl⟩ := by
  apply Subtype.ext
  rw [conjugate_root_matrix, SymplecticGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Plane.shearSp, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.J, fromBlocks, Matrix.one_apply, CharTwo.neg_eq, hz, pow_two] <;> ring_nf
  all_goals simp

private lemma conjugate_root_column (g : Sp F)
    (hU : (RootSubgroup.group 0).map (MulAut.conj g).toMonoidHom ≤ unipotent) :
    (∀ i, g.val (.inr i) (.inl 0) = 0) ∧
      (g.val (.inl 0) (.inl 0) ≠ 0 ∨ g.val (.inl 1) (.inl 0) ≠ 0) := by
  have hm := hU (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom
    ((RootSubgroup.mem_group_iff 0 _).mpr ⟨1, rfl⟩))
  obtain ⟨⟨b,u,w,v⟩,he⟩ := element_surjective ⟨_,hm⟩
  have he' : (element b u w v).val = g * rootElement 0 1 * g⁻¹ := congrArg Subtype.val he
  have hz (i : Fin 2) : g.val (.inr i) (.inl 0) = 0 := by
    apply sq_eq_zero_iff.mp
    rw [← conjugate_root_lower, ← he', element_matrix]
    rfl
  refine ⟨hz, ?_⟩
  by_contra hn
  push Not at hn
  have hi : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  have hi' := congrArg (fun M => M (.inl 0) (.inl 0)) hi
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hn.1, hn.2, hz] at hi'

private lemma shear_natural_fixed_iff (B : Plane.symmetricMatrices F) (v : Vector F) :
    binaryNatural (Plane.shearSp B) v = v ↔
      B.val 0 0 * v (.inr 0) + B.val 1 0 * v (.inr 1) = 0 ∧
      B.val 1 0 * v (.inr 0) + B.val 1 1 * v (.inr 1) = 0 := by
  have hs : B.val 0 1 = B.val 1 0 := B.property.apply 1 0
  change (Plane.shearSp B).val *ᵥ v = v ↔ _
  simp [funext_iff, Sum.forall, Fin.forall_fin_two, Plane.shearSp,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
    fromBlocks, one_apply, hs, add_assoc]

/-- Every actual long-root subgroup in the standard Sylow lies in the plane radical. -/
lemma IsSylowTransvectionRoot.le_planeRadical {R : Subgroup (Sp F)}
    (hR : IsSylowTransvectionRoot R) : R ≤ planeRadical := by
  obtain ⟨hU, g, rfl⟩ := hR
  have hz := (conjugate_root_column g hU).1
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 0 x).mp hx
  change g * rootElement 0 t * g⁻¹ ∈ planeRadical
  rw [conjugate_root_shear g t hz]
  exact (mem_planeRadical_iff _).mpr ⟨_,rfl⟩

/-- A Sylow transvection root fixes a vector outside the natural plane. -/
lemma IsSylowTransvectionRoot.plane_lt_fixedSpace {R : Subgroup (Sp F)}
    (hR : IsSylowTransvectionRoot R) :
    (plane F).restrictScalars (ZMod 2) < fixedSpace binaryNatural R := by
  have hle := (le_planeRadical_iff_plane_fixed hR.1).mp hR.le_planeRadical
  obtain ⟨hU,g,rfl⟩ := hR
  obtain ⟨hz,hn⟩ := conjugate_root_column g hU
  let v : Vector F := Sum.elim 0 ![g.val (.inl 1) (.inl 0), g.val (.inl 0) (.inl 0)]
  have hv : v ∈ fixedSpace binaryNatural ((RootSubgroup.group 0).map
      (MulAut.conj g).toMonoidHom) := by
    intro x
    obtain ⟨z,hz',he⟩ := x.property
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 0 z).mp hz'
    change binaryNatural x.val v = v
    rw [← he]
    change binaryNatural (g * rootElement 0 t * g⁻¹) v = v
    rw [conjugate_root_shear g t hz, shear_natural_fixed_iff]
    dsimp [v]
    constructor <;> ring_nf <;> simp [CharTwo.two_eq_zero]
  have hvn : v ∉ (plane F).restrictScalars (ZMod 2) := by
    intro hp
    have h0 : g.val (.inl 0) (.inl 0) = 0 := hp 1
    have h1 : g.val (.inl 1) (.inl 0) = 0 := hp 0
    exact hn.elim (fun h => h h0) (fun h => h h1)
  exact lt_of_le_not_ge hle (fun h => hvn (h hv))

private lemma levi_conjugates_shear (A : SpecialLinearGroup (Fin 2) F)
    (B : Plane.symmetricMatrices F) :
    (MulAut.conj (Plane.leviSp A)) (Plane.shearSp B) = Plane.shearSp (Plane.congruence A B) := by
  have h := congrArg Subtype.val (Plane.conjugate_shear (Plane.levi A) B)
  rw [Plane.quotientMap_levi] at h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv,
    Plane.levi, Plane.shear, MulAut.conj_apply] using h

private lemma shear_mem_root_zero (C : Plane.symmetricMatrices F)
    (h : ∀ j, C.val 1 j = 0) : Plane.shearSp C ∈ RootSubgroup.group 0 := by
  have h01 : C.val 0 1 = 0 := (C.property.apply 1 0).trans (h 0)
  apply (RootSubgroup.mem_group_iff 0 _).mpr
  refine ⟨C.val 0 0, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootElement, rootMatrix, Plane.shearSp, fromBlocks, Matrix.single, h, h01]

private lemma conjugate_shear_mem_root (M : SpecialLinearGroup (Fin 2) F)
    (B : Plane.symmetricMatrices F)
    (h1 : B.val 0 0 * M.val 1 0 + B.val 1 0 * M.val 1 1 = 0)
    (h2 : B.val 1 0 * M.val 1 0 + B.val 1 1 * M.val 1 1 = 0) :
    (MulAut.conj (Plane.leviSp M)) (Plane.shearSp B) ∈ RootSubgroup.group 0 := by
  rw [levi_conjugates_shear]
  apply shear_mem_root_zero
  have hs : B.val 0 1 = B.val 1 0 := B.property.apply 1 0
  have hz (j : Fin 2) : (M.val * B.val) 1 j = 0 := by
    fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, mul_comm] using h1
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, hs] using h2
  intro j
  change ((M.val * B.val) * M.valᵀ) 1 j = 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, hz]

private lemma exists_levi_row (x y : F) (h : x ≠ 0 ∨ y ≠ 0) :
    ∃ M : SpecialLinearGroup (Fin 2) F, M.val 1 0 = x ∧ M.val 1 1 = y := by
  by_cases hy : y = 0
  · have hx := h.resolve_right (by simpa using hy)
    refine ⟨⟨!![0,-x⁻¹;x,y], ?_⟩,rfl,rfl⟩
    simp [Matrix.det_fin_two, hx]
  · refine ⟨⟨!![y⁻¹,0;x,y], ?_⟩,rfl,rfl⟩
    simp [Matrix.det_fin_two, hy]

private lemma levi_root_le_planeRadical (M : SpecialLinearGroup (Fin 2) F) :
    (RootSubgroup.group 0).map (MulAut.conj (Plane.leviSp M)).toMonoidHom ≤
      planeRadical := by
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 0 x).mp hx
  have he : rootElement 0 t = Plane.shearSp
      ⟨!![t,0;0,0], by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩ := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rootElement,rootMatrix,Plane.shearSp,
      fromBlocks,Matrix.single]
  rw [he]
  change (MulAut.conj (Plane.leviSp M)) _ ∈ planeRadical
  rw [levi_conjugates_shear]
  exact (mem_planeRadical_iff _).mpr ⟨_,rfl⟩

/-- An extra natural fixed vector places any radical subgroup, including the
trivial subgroup, in an actual long-root conjugate inside the standard Sylow. -/
lemma exists_sylowTransvectionRoot_of_fixedSpace_ne {D : Subgroup (Sp F)}
    (hD : D ≤ planeRadical)
    (hne : fixedSpace binaryNatural D ≠ (plane F).restrictScalars (ZMod 2)) :
    ∃ R : Subgroup (Sp F), IsSylowTransvectionRoot R ∧ D ≤ R := by
  classical
  have hle : (plane F).restrictScalars (ZMod 2) ≤ fixedSpace binaryNatural D :=
    (le_planeRadical_iff_plane_fixed (hD.trans planeRadical_le_unipotent)).mp hD
  have hnle : ¬ fixedSpace binaryNatural D ≤ (plane F).restrictScalars (ZMod 2) :=
    fun h => hne (le_antisymm h hle)
  obtain ⟨v,hv,hvp⟩ := SetLike.not_le_iff_exists.mp hnle
  have hxy : v (.inr 0) ≠ 0 ∨ v (.inr 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hvp
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  obtain ⟨M,hx,hy⟩ := exists_levi_row (v (.inr 0)) (v (.inr 1)) hxy
  let g := Plane.leviSp M
  let R := (RootSubgroup.group (F := F) 0).map (MulAut.conj g⁻¹).toMonoidHom
  have hg : g⁻¹ = Plane.leviSp M⁻¹ := by
    apply (mul_left_cancel (a := g))
    rw [mul_inv_cancel]
    apply Subtype.ext
    change 1 = fromBlocks M.val 0 0 (M⁻¹).valᵀ *
      fromBlocks (M⁻¹).val 0 0 (M⁻¹⁻¹).valᵀ
    have hi : M.val * (M⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel M)
    simp only [inv_inv, Matrix.fromBlocks_multiply, mul_zero, zero_mul, add_zero,
      zero_add, hi, ← transpose_mul, transpose_one]
    exact Matrix.fromBlocks_one.symm
  have hRP : R ≤ planeRadical := by
    dsimp [R]
    rw [hg]
    exact levi_root_le_planeRadical _
  refine ⟨R, ⟨hRP.trans planeRadical_le_unipotent, g⁻¹, rfl⟩, ?_⟩
  intro z hz
  obtain ⟨B,rfl⟩ := (mem_planeRadical_iff _).mp (hD hz)
  have hb := (shear_natural_fixed_iff B v).mp (hv ⟨_,hz⟩)
  have hc : (MulAut.conj g) (Plane.shearSp B) ∈ RootSubgroup.group 0 := by
    apply conjugate_shear_mem_root
    · simpa only [hx,hy] using hb.1
    · simpa only [hx,hy] using hb.2
  refine ⟨_,hc,?_⟩
  simp [MulAut.conj_apply, mul_assoc]

/-- The containment and strict fixed-space inclusion needed for the natural
fixed-space-family criterion. Both follow from actual root conjugacy. -/
theorem sylowTransvectionRoot_geometry (R : Subgroup (Sp F))
    (hR : IsSylowTransvectionRoot R) :
    R ≤ planeRadical ∧
      (plane F).restrictScalars (ZMod 2) < fixedSpace binaryNatural R :=
  ⟨hR.le_planeRadical, hR.plane_lt_fixedSpace⟩

end SymplecticConjugatePair
