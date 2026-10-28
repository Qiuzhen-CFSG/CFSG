module

public import Theory.SpecificGroups.PSL3.CartanActions

/-!
# The GL₃ Borel kernel on the split Cartan

A general linear matrix preserving the projective upper unipotent subgroup
is upper triangular. In characteristic two, trace removes the scalar ambiguity
in lifting this preservation to SL₃. The common fixed vector and covector then
recover the upper triangular flag. If such a matrix takes a diagonal projective
element back to the torus, its nonzero diagonal entries force it to fix that
element. No normalization of the whole torus is assumed.

Source: the matrix description in GLS3, §2.7,
`refs/KGroup/GLS3/chapter2.tex`, and the Cartan action step in
Aschbacher–Smith, `refs/quasithin.pdf`, printed p.511, following A.3.15(5),
printed pp.50–51. The trace and flag argument extends the SL₃ proof in
`LinearThreeSylow.Normalizers` to the full general linear group.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.CartanActions.NormalizerForm
variable (F : Type*) [Field F]

private theorem scalar_of_projection_eq (x y : SL(3,F))
    (h : projection F x = projection F y) : ∃ r : F, x.val = r • y.val := by
  have hc := (projection F).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
    _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • y.val := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

private theorem linearConjSL_val (m : GL (Fin 3) F) (x : SL(3,F)) :
    (linearConjSL F m x).val = m.val * x.val * m.inv :=
  congrArg Units.val (linearConjSL_toGL F m x)

private theorem trace_unipotent [CharP F 2] (u : SL(3,F)) (hu : u ∈ unipotentSL F) :
    Matrix.trace u.val = 1 := by
  rw [(mem_unipotentSL_iff F u).mp hu]
  simp [Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

/-- Trace removes the scalar ambiguity when a GL₃ conjugate projects into U. -/
theorem linearConjSL_mem_unipotent [CharP F 2] (m : GL (Fin 3) F)
    (u : SL(3,F)) (hu : u ∈ unipotentSL F)
    (h : linearConj F m (projection F u) ∈ unipotent F) :
    linearConjSL F m u ∈ unipotentSL F := by
  obtain ⟨v,hv,hproj⟩ := h
  obtain ⟨r,hr⟩ := scalar_of_projection_eq F (linearConjSL F m u) v hproj.symm
  have ht : Matrix.trace (linearConjSL F m u).val = 1 := by
    rw [linearConjSL_val, Matrix.trace_mul_cycle, m.inv_val, one_mul]
    exact trace_unipotent F u hu
  rw [hr, Matrix.trace_smul, trace_unipotent F v hv, smul_eq_mul, mul_one] at ht
  have he : linearConjSL F m u = v := Subtype.ext (by simpa [ht] using hr)
  rwa [he]

private theorem map_inv_eq {G : Type*} [Group G] (H : Subgroup G) (a : MulAut G)
    (h : H.map a.toMonoidHom = H) : H.map a⁻¹.toMonoidHom = H := by
  conv_lhs => rw [← h]
  rw [Subgroup.map_map]
  have he : a⁻¹.toMonoidHom.comp a.toMonoidHom = MonoidHom.id G := by
    ext x
    exact a.symm_apply_apply x
  rw [he, Subgroup.map_id]

/-- A GL₃ matrix preserving projective U fixes its vector and covector flags. -/
theorem linearConj_upperTriangular [CharP F 2] (m : GL (Fin 3) F)
    (h : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F) :
    m.val 1 0 = 0 ∧ m.val 2 0 = 0 ∧ m.val 2 1 = 0 := by
  have hf (u : SL(3,F)) (hu : u ∈ unipotentSL F) :
      linearConjSL F m u ∈ unipotentSL F :=
    linearConjSL_mem_unipotent F m u hu
      (h.le (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem (projection F) hu)))
  have hi : (unipotent F).map (linearConj F m⁻¹).toMonoidHom = unipotent F := by
    rw [map_inv]
    exact map_inv_eq _ _ h
  have hb (u : SL(3,F)) (hu : u ∈ unipotentSL F) :
      linearConjSL F m⁻¹ u ∈ unipotentSL F :=
    linearConjSL_mem_unipotent F m⁻¹ u hu
      (hi.le (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem (projection F) hu)))
  have hcol (u : U F) (i : Fin 3) :
      ((specialLinear F u).val * m.val) i 0 = m.val i 0 := by
    let v := linearConjSL F m⁻¹ (specialLinear F u)
    have hv := (mem_pointLocalSL_iff F v).mp
      (hb _ ((specialLinear_range F).le ⟨u,rfl⟩)).1
    have he : (specialLinear F u).val * m.val = m.val * v.val := by
      dsimp only [v]
      rw [linearConjSL_val]
      change _ = m.val * (m.inv * (specialLinear F u).val * m.val)
      simp only [← Matrix.mul_assoc, m.val_inv, one_mul]
    rw [he]
    simp [Matrix.mul_apply, Fin.sum_univ_three, hv.1,hv.2.1,hv.2.2]
  have hrow (u : U F) (j : Fin 3) :
      (m.val * (specialLinear F u).val) 2 j = m.val 2 j := by
    let v := linearConjSL F m (specialLinear F u)
    have hv := (mem_lineLocalSL_iff F v).mp
      (hf _ ((specialLinear_range F).le ⟨u,rfl⟩)).2
    have he : m.val * (specialLinear F u).val = v.val * m.val := by
      dsimp only [v]
      rw [linearConjSL_val, Matrix.mul_assoc, m.inv_val, mul_one]
    rw [he]
    simp [Matrix.mul_apply, Fin.sum_univ_three, hv.1,hv.2.1,hv.2.2]
  have h10 := hcol ⟨1,0,0⟩ 0
  have h20 := hcol ⟨0,1,0⟩ 1
  have h21 := hrow ⟨0,1,0⟩ 2
  change (matrix F ⟨1,0,0⟩ * m.val) 0 0 = m.val 0 0 at h10
  change (matrix F ⟨0,1,0⟩ * m.val) 1 0 = m.val 1 0 at h20
  change (m.val * matrix F ⟨0,1,0⟩) 2 2 = m.val 2 2 at h21
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h10 h20 h21
  exact ⟨h10,h20,h21⟩

/-- Upper triangular GL₃ conjugation cannot move a torus element to another
one: its three nonzero diagonal entries compare the three eigenvalues. -/
theorem upperTriangular_torus_kernel (m : GL (Fin 3) F)
    (hm : m.val 1 0 = 0 ∧ m.val 2 0 = 0 ∧ m.val 2 1 = 0)
    (b : PSL(3,F)) (hb : b ∈ torus F) (hmb : linearConj F m b ∈ torus F) :
    linearConj F m b = b := by
  obtain ⟨d,rfl⟩ := hb
  obtain ⟨e,he⟩ := hmb
  have hp : projection F (linearConjSL F m (torusSL F d)) =
      projection F (torusSL F e) := he.symm
  obtain ⟨r,hr⟩ := scalar_of_projection_eq F _ _ hp
  have hn : Matrix.det m.val ≠ 0 := (GeneralLinearGroup.det m).ne_zero
  rw [Matrix.det_fin_three] at hn
  simp only [hm.1,hm.2.1,hm.2.2,mul_zero,zero_mul,sub_zero,add_zero] at hn
  have hn' : ∀ i : Fin 3, m.val i i ≠ 0 := by
    intro i
    fin_cases i
    · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
    · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
    · exact (mul_ne_zero_iff.mp hn).2
  have heq : m.val * (torusSL F d).val = (r • (torusSL F e).val) * m.val := by
    rw [← hr, linearConjSL_val, Matrix.mul_assoc, m.inv_val, mul_one]
  have hd (i : Fin 3) : (torusSL F d).val i i = r * (torusSL F e).val i i := by
    have hh := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a i i) heq
    simp only [torusSL_val, Matrix.mul_diagonal, Matrix.smul_mul, Matrix.diagonal_mul,
      Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq] at hh ⊢
    apply (mul_left_cancel₀ (hn' i))
    calc
      _ = r * (_ * m.val i i) := hh
      _ = _ := by ring
  have hs : linearConjSL F m (torusSL F d) = torusSL F d := by
    apply Subtype.ext
    rw [hr]
    ext i j
    by_cases hij : i = j
    · subst j
      exact (hd i).symm
    · simp [torusSL_val, hij]
  change projection F (linearConjSL F m (torusSL F d)) = _
  rw [hs]
  rfl

/-- The actual GL₃ Borel kernel, with no additional alignment premise. -/
theorem linearConj_torus_kernel [CharP F 2] (m : GL (Fin 3) F)
    (h : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (b : PSL(3,F)) (hb : b ∈ torus F) (hmb : linearConj F m b ∈ torus F) :
    linearConj F m b = b :=
  upperTriangular_torus_kernel F m (linearConj_upperTriangular F m h) b hb hmb

end Matrix.PSL3.CartanActions.NormalizerForm
