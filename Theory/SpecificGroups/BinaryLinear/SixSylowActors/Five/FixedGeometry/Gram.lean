module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.Contracts
public import Theory.LinearAlgebra.AlternatingFinrank
public import Theory.LinearAlgebra.BinaryAlternatingFour
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Symmetric binary forms in dimension five

A nondegenerate symmetric form represents its diagonal functional by a
canonical vector. That vector has norm one: otherwise subtracting the square
of the diagonal functional would give a nondegenerate alternating form in
odd dimension. Splitting off the canonical line leaves a nondegenerate
alternating four-space. The checked four-dimensional congruence theorem
identifies this complement with the standard symplectic space.

Applying the construction both to the given form and to the identity form
produces an actual linear isometry. Its matrix gives the precise factorization
`g = h.transpose * h`, with determinant one over the binary field.

This is the form normalization needed in the degree-five outer-involution
argument of Aschbacher–Smith, E.6.23, printed p.254 (PDF p.265) of
`refs/quasithin.pdf`. The compatible fixed-group model is a separate result.
-/

noncomputable section
namespace BinaryLinear.SixSylowActors.Five.Gram
private abbrev F := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private lemma binary_add_self (r : F) : r + r = 0 := by revert r; decide
private lemma binary_mul_self (r : F) : r * r = r := by revert r; decide

/-- Over the binary field the diagonal of a symmetric form is linear. -/
private def diagonal (B : LinearMap.BilinForm F V) (hs : B.IsSymm) : V →ₗ[F] F where
  toFun x := B x x
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply]
    rw [hs.eq y x]
    calc
      _ = B x x + B y y + (B x y + B x y) := by ring
      _ = _ := by rw [binary_add_self, add_zero]
  map_smul' r x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, binary_mul_self]
    rfl

/-- The representing vector has norm one by alternating dimension parity. -/
private theorem canonical (B : LinearMap.BilinForm F V) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (hd : Module.finrank F V = 5) :
    ∃ c : V, B c c = 1 ∧ ∀ x, B c x = B x x := by
  let q := diagonal B hs
  let c := (B.toDual hn).symm q
  have hc (x : V) : B c x = q x := LinearMap.BilinForm.apply_toDual_symm_apply q x
  have hqc : q c = 1 := by
    by_contra h
    have hz : q c = 0 := (by decide : ∀ r : F, r ≠ 1 → r = 0) _ h
    let D : LinearMap.BilinForm F V := B - q.smulRight q
    have hDalt : D.IsAlt := by
      intro x
      change B x x - q x * q x = 0
      rw [binary_mul_self]
      exact sub_self _
    have hDsep : D.SeparatingLeft := by
      intro x hx
      have hqx : q x = 0 := by
        have he := hx c
        change B x c - q x * q c = 0 at he
        rwa [hs.eq x c, hc, hz, mul_zero, sub_zero] at he
      apply hn.1 x
      intro y
      have he := hx y
      change B x y - q x * q y = 0 at he
      simpa only [hqx, zero_mul, sub_zero] using he
    have heven := AlternatingForm.even_finrank D hDalt
      (LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hDsep)
    rw [hd] at heven
    norm_num at heven
  exact ⟨c, (hc c).trans hqc, hc⟩

variable (B : LinearMap.BilinForm F V) (hs : B.IsSymm) (c : V) (hc : B c c = 1)

/-- Orthogonal projection gives the line plus its actual perpendicular kernel. -/
private def split : V ≃ₗ[F] F × (B c).ker where
  toFun x := (B c x, ⟨x - (B c x) • c, by simp [map_sub, map_smul, hc]⟩)
  invFun z := z.1 • c + z.2.val
  left_inv x := by dsimp; abel
  right_inv z := by
    rcases z with ⟨r, ⟨w, hw⟩⟩
    have hw' : B c w = 0 := hw
    apply Prod.ext
    · simp [map_add, map_smul, hc, hw']
    · apply Subtype.ext
      simp [map_add, map_smul, hc, hw']
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · apply Subtype.ext
      simp only [map_add, add_smul]
      dsimp
      abel
  map_smul' r x := by
    apply Prod.ext
    · exact map_smul _ _ _
    · apply Subtype.ext
      simp [map_smul, smul_sub, smul_smul]

omit [FiniteDimensional F V] in
include hs in
private theorem split_form (x y : F × (B c).ker) :
    B ((split B c hc).symm x) ((split B c hc).symm y) =
      x.1 * y.1 + B.restrict (B c).ker x.2 y.2 := by
  have hx : B c x.2 = 0 := x.2.prop
  have hy : B c y.2 = 0 := y.2.prop
  have hx' : B x.2 c = 0 := (hs.eq _ _).trans hx
  change B (x.1 • c + x.2.val) (y.1 • c + y.2.val) = _
  simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hc, hx', hy, mul_comm]

include hs hc in
private theorem complement_nondegenerate (hn : B.Nondegenerate) :
    (B.restrict (B c).ker).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  apply Subtype.ext
  apply hn.1 x.val
  intro y
  obtain ⟨z, rfl⟩ := (split B c hc).symm.surjective y
  have hx' : B x.val c = 0 := (hs.eq _ _).trans x.prop
  have hw : B x.val z.2.val = 0 := hx z.2
  change B x.val (z.1 • c + z.2.val) = 0
  simp [map_add, map_smul, hx', hw]

include hc in
private theorem complement_finrank (hd : Module.finrank F V = 5) :
    Module.finrank F (B c).ker = 4 := by
  have he := (split B c hc).finrank_eq
  rw [hd, Module.finrank_prod, Module.finrank_self] at he
  omega
end BinaryLinear.SixSylowActors.Five.Gram

namespace BinaryLinear.SixSylowActors.Five.Gram
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
/-- Lift the checked matrix congruence to an equivalence on the original space. -/
private theorem alternating_normalize (B : LinearMap.BilinForm F V) (ha : B.IsAlt)
    (hn : B.Nondegenerate) (hd : Module.finrank F V = 4) :
    ∃ e : (Fin 4 → F) ≃ₗ[F] V,
      ∀ x y, B (e x) (e y) = BinaryAlternatingFour.J4.toBilin' x y := by
  let b := Module.finBasisOfFinrankEq F V hd
  let E := b.equivFun.symm
  let C := B.comp E.toLinearMap E.toLinearMap
  have hCa : C.toMatrix'.toBilin'.IsAlt := by
    rw [Matrix.toBilin'_toMatrix']
    exact fun x => ha (E x)
  have hCn : C.toMatrix'.toBilin'.Nondegenerate := by
    rw [Matrix.toBilin'_toMatrix']
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    intro x hx
    apply E.injective
    rw [map_zero]
    apply hn.1 (E x)
    intro y
    obtain ⟨z, rfl⟩ := E.surjective y
    exact hx z
  obtain ⟨M, hM, hcongr⟩ := BinaryAlternatingFour.exists_congruence C.toMatrix' hCa hCn
  let e := Matrix.toLinearEquiv (Pi.basisFun F (Fin 4)) M (isUnit_iff_ne_zero.mpr hM)
  have he (x : Fin 4 → F) : e x = M.toLin' x := by
    simp only [e, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin']
  refine ⟨e.trans E, ?_⟩
  intro x y
  change C (e x) (e y) = _
  rw [he, he]
  have hform : C.comp M.toLin' M.toLin' = BinaryAlternatingFour.J4.toBilin' := by
    apply LinearMap.BilinForm.toMatrix'.injective
    simpa only [LinearMap.BilinForm.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.BilinForm.toMatrix'_toBilin'] using hcongr
  exact congrArg (fun D : LinearMap.BilinForm F (Fin 4 → F) => D x y) hform

private theorem alternating_isometry
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (B : LinearMap.BilinForm F V) (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hd : Module.finrank F V = 4)
    (C : LinearMap.BilinForm F W) (hCa : C.IsAlt) (hCn : C.Nondegenerate)
    (hCd : Module.finrank F W = 4) :
    ∃ e : V ≃ₗ[F] W, ∀ x y, C (e x) (e y) = B x y := by
  obtain ⟨i, hi⟩ := alternating_normalize B ha hn hd
  obtain ⟨j, hj⟩ := alternating_normalize C hCa hCn hCd
  refine ⟨i.symm.trans j, ?_⟩
  intro x y
  change C (j (i.symm x)) (j (i.symm y)) = B x y
  rw [hj, ← hi, i.apply_symm_apply, i.apply_symm_apply]
end BinaryLinear.SixSylowActors.Five.Gram

namespace BinaryLinear.SixSylowActors.Five.Gram
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
/-- Compare the canonical decompositions, retaining an actual linear equivalence. -/
private theorem symmetric_isometry
    (B C : LinearMap.BilinForm F V)
    (hsB : B.IsSymm) (hsC : C.IsSymm)
    (hnB : B.Nondegenerate) (hnC : C.Nondegenerate)
    (hd : Module.finrank F V = 5) :
    ∃ e : V ≃ₗ[F] V, ∀ x y, C (e x) (e y) = B x y := by
  obtain ⟨c, hc, hcx⟩ := canonical B hsB hnB hd
  obtain ⟨d, hd', hdx⟩ := canonical C hsC hnC hd
  have hBa : (B.restrict (B c).ker).IsAlt := by
    intro x
    exact (hcx x).symm.trans x.prop
  have hCa : (C.restrict (C d).ker).IsAlt := by
    intro x
    exact (hdx x).symm.trans x.prop
  obtain ⟨i, hi⟩ := alternating_isometry (B.restrict (B c).ker) hBa
    (complement_nondegenerate B hsB c hc hnB) (complement_finrank B c hc hd)
    (C.restrict (C d).ker) hCa
    (complement_nondegenerate C hsC d hd' hnC) (complement_finrank C d hd' hd)
  let L := split B c hc
  let M := split C d hd'
  let E := L.trans (((LinearEquiv.refl F F).prodCongr i).trans M.symm)
  have hE (z : F × (B c).ker) : E (L.symm z) = M.symm (z.1, i z.2) := by
    change M.symm (((LinearEquiv.refl F F).prodCongr i) (L (L.symm z))) = _
    rw [L.apply_symm_apply]
    rfl
  refine ⟨E, ?_⟩
  intro x y
  obtain ⟨x, rfl⟩ := L.symm.surjective x
  obtain ⟨y, rfl⟩ := L.symm.surjective y
  rw [hE, hE]
  rw [split_form C hsC d hd', split_form B hsB c hc]
  exact congrArg (fun t => x.1 * y.1 + t) (hi x.2 y.2)

private theorem matrix_gram {n : ℕ} (hn : n = 5)
    (g : Matrix.SpecialLinearGroup (Fin n) F) (hg : g.transpose = g) :
    ∃ h : Matrix.SpecialLinearGroup (Fin n) F, g = h.transpose * h := by
  let A : Matrix (Fin n) (Fin n) F := g
  have hs : A.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr
    (congrArg (fun k : Matrix.SpecialLinearGroup (Fin n) F => (k : Matrix (Fin n) (Fin n) F)) hg)
  have hnd : A.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (by
      change g.val.det ≠ 0
      rw [g.prop]
      exact one_ne_zero)
  have hI : (1 : Matrix (Fin n) (Fin n) F).toBilin'.IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr Matrix.transpose_one
  have hIn : (1 : Matrix (Fin n) (Fin n) F).toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (by simp)
  obtain ⟨e, he⟩ := symmetric_isometry A.toBilin' (1 : Matrix (Fin n) (Fin n) F).toBilin'
    hs hI hnd hIn (by simp [hn])
  let H := e.toLinearMap.toMatrix'
  have hunit : IsUnit H.det := e.isUnit_det (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n))
  have hdet : H.det = 1 :=
    (by decide : ∀ r : F, r ≠ 0 → r = 1) _ (isUnit_iff_ne_zero.mp hunit)
  have hform : (1 : Matrix (Fin n) (Fin n) F).toBilin'.comp e.toLinearMap e.toLinearMap =
      A.toBilin' := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact he x y
  have hmat : H.transpose * H = A := by
    have hm := congrArg LinearMap.BilinForm.toMatrix' hform
    simpa only [LinearMap.BilinForm.toMatrix'_comp, LinearMap.BilinForm.toMatrix'_toBilin',
      Matrix.mul_one] using hm
  refine ⟨⟨H, hdet⟩, ?_⟩
  apply Subtype.ext
  exact hmat.symm

end BinaryLinear.SixSylowActors.Five.Gram

namespace BinaryLinear.SixSylowActors.Five

/-- Every symmetric invertible binary five-matrix is an actual Gram matrix.
The change of basis has determinant one since the field has only one nonzero element. -/
public theorem symmetric_gram (g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hg : g.transpose = g) :
    ∃ h : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2), g = h.transpose * h :=
  Gram.matrix_gram rfl g hg

end BinaryLinear.SixSylowActors.Five
