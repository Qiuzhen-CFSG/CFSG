module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Theory.LinearAlgebra.AlternatingFinrank
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Symmetric ternary forms in characteristic two

Over a finite field of characteristic two, inverse Frobenius turns the
self-pairing of a symmetric bilinear form into a linear functional. The vector
representing this functional has norm one: otherwise subtracting its square
would give a nondegenerate alternating form in odd dimension. Its orthogonal
complement is a nondegenerate alternating plane. Comparing this decomposition
with that of the identity form constructs an actual Gram factorization.

This generalizes the construction in
`PSL3Four/InvolutionNormalForms/Graph/Gram.lean`, replacing the GF(4)-specific
square-root formula by inverse Frobenius. The alternating parity theorem is
reused from the attributed ATLAS port `Theory.LinearAlgebra.AlternatingFinrank`;
its source notice and license remain in that module. No odd-characteristic
orthogonal classification is used, and the field with two elements is included.

This supplies the form normalization for the graph-involution branch of
Aschbacher–Smith E.1.14(1), printed p.214, and 16.1.4(6), printed p.1171;
the matrix action convention is GLS3 §2.7.
-/

noncomputable section
open Matrix
namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks.GraphConjugacy.Gram
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private def diagonal (B : LinearMap.BilinForm F V) (hs : B.IsSymm) : V →ₗ[F] F where
  toFun x := (frobeniusEquiv F 2).symm (B x x)
  map_add' x y := by
    simp only [LinearMap.map_add, LinearMap.add_apply]
    rw [hs.eq y x]
    have he : B x x + B x y + (B x y + B y y) = B x x + B y y := by
      calc
        _ = B x x + B y y + (B x y + B x y) := by ring
        _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
    rw [he, map_add]
  map_smul' r x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← mul_assoc, ← pow_two, map_mul, frobeniusEquiv_symm_pow]

private theorem canonical (B : LinearMap.BilinForm F V) (hs : B.IsSymm)
    (hn : B.Nondegenerate) (hd : Module.finrank F V = 3) :
    ∃ c : V, B c c = 1 ∧ ∀ x, B c x = (frobeniusEquiv F 2).symm (B x x) := by
  let q := diagonal B hs
  let c := (B.toDual hn).symm q
  have hc (x : V) : B c x = q x := LinearMap.BilinForm.apply_toDual_symm_apply q x
  have hqc : q c = 1 := by
    by_contra h
    have hid : (q c)^2 = q c := by
      calc
        (q c)^2 = B c c := frobeniusEquiv_symm_pow_p F 2 (B c c)
        _ = q c := hc c
    have hz : q c = 0 := by
      have hz : q c * (q c - 1) = 0 := by
        calc
          _ = (q c)^2 - q c := by ring
          _ = 0 := sub_eq_zero.mpr hid
      exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr h)
    let D : LinearMap.BilinForm F V := B - q.smulRight q
    have hDalt : D.IsAlt := by
      intro x
      change B x x - ((frobeniusEquiv F 2).symm (B x x)) *
        ((frobeniusEquiv F 2).symm (B x x)) = 0
      rw [← pow_two, frobeniusEquiv_symm_pow_p]
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
    obtain ⟨k, hk⟩ := heven
    omega
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

omit [FiniteDimensional F V] [Finite F] [CharP F 2] in
include hs in
private theorem split_form (x y : F × (B c).ker) :
    B ((split B c hc).symm x) ((split B c hc).symm y) =
      x.1 * y.1 + B.restrict (B c).ker x.2 y.2 := by
  have hx : B c x.2 = 0 := x.2.prop
  have hy : B c y.2 = 0 := y.2.prop
  have hx' : B x.2 c = 0 := (hs.eq _ _).trans hx
  change B (x.1 • c + x.2.val) (y.1 • c + y.2.val) = _
  simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hc, hx', hy, mul_comm]

omit [Finite F] [CharP F 2] in
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

omit [Finite F] [CharP F 2] in
include hc in
private theorem complement_finrank (hd : Module.finrank F V = 3) :
    Module.finrank F (B c).ker = 2 := by
  have he := (split B c hc).finrank_eq
  rw [hd, Module.finrank_prod, Module.finrank_self] at he
  omega
end Matrix.PSL3Even.OuterElementaryRank.FixedRanks.GraphConjugacy.Gram

namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks.GraphConjugacy.Gram
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
omit [Finite F] in
private theorem alternating_normalize (B : LinearMap.BilinForm F V) (ha : B.IsAlt)
    (hn : B.Nondegenerate) (hd : Module.finrank F V = 2) :
    ∃ e : (Fin 2 → F) ≃ₗ[F] V,
      ∀ x y, B (e x) (e y) = (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) F).toBilin' x y := by
  let b := Module.finBasisOfFinrankEq F V hd
  let E := b.equivFun.symm
  let C := B.comp E.toLinearMap E.toLinearMap
  let A := C.toMatrix'
  have hCa : A.toBilin'.IsAlt := by
    rw [Matrix.toBilin'_toMatrix']
    exact fun x => ha (E x)
  have hCn : A.toBilin'.Nondegenerate := by
    rw [Matrix.toBilin'_toMatrix']
    apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    intro x hx
    apply E.injective
    rw [map_zero]
    apply hn.1 (E x)
    intro y
    obtain ⟨z, rfl⟩ := E.surjective y
    exact hx z
  have hdiag (i : Fin 2) : A i i = 0 := by
    simpa only [Matrix.toBilin'_single] using hCa.self_eq_zero (Pi.single i 1)
  have hswap : A 1 0 = A 0 1 := by
    simpa only [Matrix.toBilin'_single, CharTwo.neg_eq] using
      (hCa.neg_eq (Pi.single 0 1) (Pi.single 1 1)).symm
  have hshape : A = !![0,A 0 1;A 0 1,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hdiag, hswap]
  have ht : A 0 1 ≠ 0 := by
    have hnA := LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp hCn
    intro hz
    rw [hshape] at hnA
    simp [Matrix.det_fin_two, hz] at hnA
  let M : Matrix (Fin 2) (Fin 2) F := !![1,0;0,(A 0 1)⁻¹]
  have hM : IsUnit M.det := by
    simp [M, Matrix.det_fin_two, ht]
  have hcongr : M.transpose * A * M = !![0,1;1,0] := by
    rw [hshape]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two, ht]
  let e := Matrix.toLinearEquiv (Pi.basisFun F (Fin 2)) M hM
  have he (x : Fin 2 → F) : e x = M.toLin' x := by
    simp only [e, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin']
  refine ⟨e.trans E, ?_⟩
  intro x y
  change C (e x) (e y) = _
  rw [he, he]
  have hform : C.comp M.toLin' M.toLin' =
      (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) F).toBilin' := by
    apply LinearMap.BilinForm.toMatrix'.injective
    simpa only [LinearMap.BilinForm.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.BilinForm.toMatrix'_toBilin'] using hcongr
  exact congrArg (fun D : LinearMap.BilinForm F (Fin 2 → F) => D x y) hform

omit [Finite F] in
private theorem alternating_isometry
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (B : LinearMap.BilinForm F V) (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hd : Module.finrank F V = 2)
    (C : LinearMap.BilinForm F W) (hCa : C.IsAlt) (hCn : C.Nondegenerate)
    (hCd : Module.finrank F W = 2) :
    ∃ e : V ≃ₗ[F] W, ∀ x y, C (e x) (e y) = B x y := by
  obtain ⟨i, hi⟩ := alternating_normalize B ha hn hd
  obtain ⟨j, hj⟩ := alternating_normalize C hCa hCn hCd
  refine ⟨i.symm.trans j, ?_⟩
  intro x y
  change C (j (i.symm x)) (j (i.symm y)) = B x y
  rw [hj, ← hi, i.apply_symm_apply, i.apply_symm_apply]

/-- Compare the canonical decompositions, retaining an actual linear equivalence. -/
private theorem symmetric_isometry
    (B C : LinearMap.BilinForm F V)
    (hsB : B.IsSymm) (hsC : C.IsSymm)
    (hnB : B.Nondegenerate) (hnC : C.Nondegenerate)
    (hd : Module.finrank F V = 3) :
    ∃ e : V ≃ₗ[F] V, ∀ x y, C (e x) (e y) = B x y := by
  obtain ⟨c, hc, hcx⟩ := canonical B hsB hnB hd
  obtain ⟨d, hd', hdx⟩ := canonical C hsC hnC hd
  have hBa : (B.restrict (B c).ker).IsAlt := by
    intro x
    have hx : (frobeniusEquiv F 2).symm (B x x) = 0 := (hcx x).symm.trans x.prop
    exact (frobeniusEquiv F 2).symm.injective (hx.trans (map_zero _).symm)
  have hCa : (C.restrict (C d).ker).IsAlt := by
    intro x
    have hx : (frobeniusEquiv F 2).symm (C x x) = 0 := (hdx x).symm.trans x.prop
    exact (frobeniusEquiv F 2).symm.injective (hx.trans (map_zero _).symm)
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

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks.GraphConjugacy.Gram

namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks.GraphConjugacy

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every nonsingular symmetric ternary matrix over a finite field of
characteristic two has an actual invertible Gram factor. -/
public theorem symmetric_gram (g : GL (Fin 3) F) (hg : g.val.transpose = g.val) :
    ∃ h : GL (Fin 3) F, g.val = h.val.transpose * h.val := by
  let A : Matrix (Fin 3) (Fin 3) F := g.val
  have hs : A.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hg
  have hnd : A.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
      (GeneralLinearGroup.det_ne_zero g)
  have hI : (1 : Matrix (Fin 3) (Fin 3) F).toBilin'.IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr Matrix.transpose_one
  have hIn : (1 : Matrix (Fin 3) (Fin 3) F).toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr (by simp)
  obtain ⟨e, he⟩ := Gram.symmetric_isometry A.toBilin'
    (1 : Matrix (Fin 3) (Fin 3) F).toBilin' hs hI hnd hIn (by simp)
  let H := e.toLinearMap.toMatrix'
  have hunit : IsUnit H.det := e.isUnit_det (Pi.basisFun F (Fin 3)) (Pi.basisFun F (Fin 3))
  have hform : (1 : Matrix (Fin 3) (Fin 3) F).toBilin'.comp e.toLinearMap e.toLinearMap =
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
  exact ⟨GeneralLinearGroup.mk'' H hunit, hmat.symm⟩

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks.GraphConjugacy
