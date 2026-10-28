module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.AlphaGroups

/-!
# The full component fixer of a central tensor displacement

For the coefficient-twisted action X ↦ g X σ(g)ᵀ, fixing the displacement
of a nonidentity central shear forces g to be a scalar plus a multiple of
that shear. Two matrix-entry slices prove this without a case split on rank.
The symplectic equation removes the scalar factor in characteristic two;
the remaining equation says that the shear parameter is fixed by σ.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
The α-group convention is AS76a §11, as documented in AlphaGroups.
-/

@[expose] public section
set_option linter.unusedSimpArgs false
open scoped Matrix TensorProduct Classical
open Matrix Representation
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {F : Type*} [Field F]

private lemma slice (σ : F ≃+* F) (g j : Sp F)
    (hf : ∀ X, matrixAction σ g (matrixAction σ j X - X) = matrixAction σ j X - X)
    (i k m l : Fin 2 ⊕ Fin 2) :
    (g*j).val i k * σ (j.val m l) - g.val i k * (1 : Mat (F := F)) m l =
      j.val i k * σ ((g⁻¹*j).val m l) - (1 : Mat (F := F)) i k * σ ((g⁻¹).val m l) := by
  have h (X : Mat (F := F)) := congrArg
    (fun Y : Mat (F := F) => Y * ((g⁻¹).val.map σ).transpose) (hf X)
  have hinv : (g.val.map σ).transpose * ((g⁻¹).val.map σ).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul]
    have hh : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
    rw [hh]
    simp
  have h' (X : Mat (F := F)) :
      (g*j).val * X * (j.val.map σ).transpose - g.val * X =
        j.val * X * ((g⁻¹*j).val.map σ).transpose - X * ((g⁻¹).val.map σ).transpose := by
    have hh := h X
    change (g.val * (j.val * X * (j.val.map σ).transpose - X) *
      (g.val.map σ).transpose) * ((g⁻¹).val.map σ).transpose =
        (j.val * X * (j.val.map σ).transpose - X) * ((g⁻¹).val.map σ).transpose at hh
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hinv, Matrix.mul_one] at hh
    change (g.val*j.val) * X * (j.val.map σ).transpose - g.val * X =
      j.val * X * (((g⁻¹).val*j.val).map σ).transpose - X * ((g⁻¹).val.map σ).transpose
    simpa only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc] using hh
  have hs (A C : Mat (F := F)) : (A * (Matrix.single k l (1 : F) : Mat (F := F)) * C) i m = A i k * C l m := by
    simp only [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero, mul_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul]
  have hh := congrArg (fun X : Mat (F := F) => X i m) (h' ((Matrix.single k l (1 : F) : Mat (F := F))))
  simp only [Matrix.sub_apply] at hh
  rw [hs, hs] at hh
  have hleft : (g.val * (Matrix.single k l (1 : F) : Mat (F := F))) i m = g.val i k * (1 : Mat (F := F)) m l := by
    by_cases hm : m = l
    · subst m; simp
    · simp [Matrix.mul_single_apply_of_ne, hm, Matrix.one_apply]
  have hright : ((Matrix.single k l (1 : F) : Mat (F := F)) * ((g⁻¹).val.map σ).transpose) i m =
      (1 : Mat (F := F)) i k * σ ((g⁻¹).val m l) := by
    by_cases hi : i = k
    · subst i; simp
    · simp [Matrix.single_mul_apply_of_ne, hi, Matrix.one_apply]
  simpa only [hleft, hright, Matrix.transpose_apply, Matrix.map_apply] using hh

private lemma scalar_blocks_of_fixes (σ : F ≃+* F) (g : Sp F) (B : Plane.symmetricMatrices F)
    (q : Fin 2) (hB : B.val 0 q ≠ 0)
    (hf : ∀ X, matrixAction σ g (matrixAction σ (Plane.shearSp B) X - X) =
      matrixAction σ (Plane.shearSp B) X - X) :
    ∃ r t : F, g.val = Matrix.fromBlocks (r • 1) (t • B.val) 0 (r • 1) := by
  let j := Plane.shearSp B
  let z := σ (B.val 0 q)
  have hz : z ≠ 0 := (map_ne_zero σ).mpr hB
  let c := σ ((g⁻¹).val (.inl 0) (.inl 0))
  let d := σ ((g⁻¹*j).val (.inl 0) (.inr q))
  let e := σ ((g⁻¹).val (.inl 0) (.inr q))
  have hd (i k) := slice σ g j hf i k (.inl 0) (.inl 0)
  have ho (i k) := slice σ g j hf i k (.inl 0) (.inr q)
  have hc : (g⁻¹*j).val (.inl 0) (.inl 0) = (g⁻¹).val (.inl 0) (.inl 0) := by
    simp [j, Plane.shearSp, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks, Matrix.one_apply]
  have hd' (i k) : (g*j).val i k - g.val i k = j.val i k*c - (1 : Mat (F := F)) i k*c := by
    have hh := hd i k
    rw [hc] at hh
    simpa [j, Plane.shearSp, Matrix.fromBlocks, Matrix.one_apply, c] using hh
  have ho' (i k) : (g*j).val i k*z = j.val i k*d - (1 : Mat (F := F)) i k*e := by
    simpa [j, Plane.shearSp, Matrix.fromBlocks, Matrix.one_apply, z,d,e] using ho i k
  have hg : g.val = (d/z-c) • j.val + (c-e/z) • (1 : Mat (F := F)) := by
    ext i k
    change g.val i k = (d/z-c)*j.val i k + (c-e/z)*(1 : Mat (F := F)) i k
    apply (mul_left_cancel₀ hz)
    field_simp
    linear_combination ho' i k - z * hd' i k
  refine ⟨(d-e)/z, d/z-c, ?_⟩
  rw [hg]
  ext i k
  rcases i with i | i <;> rcases k with k | k
  all_goals simp [j, Plane.shearSp, Matrix.fromBlocks, Matrix.one_apply]
  all_goals split_ifs <;> ring

variable [CharP F 2]
private lemma shear_of_fixes (σ : F ≃+* F) (g : Sp F) (B : Plane.symmetricMatrices F)
    (q : Fin 2) (hB : B.val 0 q ≠ 0)
    (hf : ∀ X, matrixAction σ g (matrixAction σ (Plane.shearSp B) X - X) =
      matrixAction σ (Plane.shearSp B) X - X) :
    ∃ t : F, g = Plane.shearSp (t • B) := by
  obtain ⟨r,t,he⟩ := scalar_blocks_of_fixes σ g B q hB hf
  have hg := g.property
  rw [he, SymplecticGroup.fromBlocks_mem_iff] at hg
  have hr : r^2 = 1 := by
    have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 0 0) hg.2.2
    simpa [Matrix.mul_apply, Fin.sum_univ_two, pow_two] using hh
  have hr' : r = 1 := by simpa [CharTwo.neg_eq] using sq_eq_one_iff.mp hr
  refine ⟨t, Subtype.ext ?_⟩
  simpa [hr',Plane.shearSp] using he
omit [CharP F 2] in
private lemma shear_displacement_blocks (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    matrixAction σ (Plane.shearSp B) (Matrix.fromBlocks P Q R S) -
        Matrix.fromBlocks P Q R S =
      Matrix.fromBlocks (B.val*R + (Q+B.val*S)*(B.val.map σ).transpose)
        (B.val*S) (S*(B.val.map σ).transpose) 0 := by
  rw [shear_blocks, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  congr 1 <;> abel

omit [CharP F 2] in
private lemma scalar_shear_fixes_iff (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    (t : F) (P Q R S : Matrix (Fin 2) (Fin 2) F) :
    matrixAction σ (Plane.shearSp (t • B))
      (matrixAction σ (Plane.shearSp B) (Matrix.fromBlocks P Q R S) -
        Matrix.fromBlocks P Q R S) =
      matrixAction σ (Plane.shearSp B) (Matrix.fromBlocks P Q R S) -
        Matrix.fromBlocks P Q R S ↔
      (t + σ t) • (B.val*S*(B.val.map σ).transpose) = 0 := by
  have ht : (((t • B).val).map σ).transpose = σ t • (B.val.map σ).transpose := by
    ext i k
    exact map_mul σ t (B.val k i)
  rw [← mem_matrixFixed, shear_displacement_blocks, shear_fixed_iff]
  simp only [Matrix.mul_zero, Matrix.zero_mul, true_and, ht]
  change t • B.val * (S*(B.val.map σ).transpose) + B.val*S*(σ t • (B.val.map σ).transpose) = 0 ↔ _
  rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, ← add_smul]

private lemma scalar_shear_fixes (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    {t : F} (ht : σ t = t) (X : Mat (F := F)) :
    matrixAction σ (Plane.shearSp (t • B)) (matrixAction σ (Plane.shearSp B) X - X) =
      matrixAction σ (Plane.shearSp B) X - X := by
  rw [← Matrix.fromBlocks_toBlocks X, scalar_shear_fixes_iff, ht,
    CharTwo.add_self_eq_zero, zero_smul]

private lemma scalar_fixed_of_shear_fixes (σ : F ≃+* F) (B : Plane.symmetricMatrices F)
    (q : Fin 2) (hB : B.val 0 q ≠ 0) (t : F)
    (hf : ∀ X, matrixAction σ (Plane.shearSp (t • B))
      (matrixAction σ (Plane.shearSp B) X - X) = matrixAction σ (Plane.shearSp B) X - X) :
    σ t = t := by
  have hh := (scalar_shear_fixes_iff σ B t 0 0 0 ((Matrix.single q q (1 : F) : Matrix (Fin 2) (Fin 2) F))).mp
    (hf (Matrix.fromBlocks 0 0 0 ((Matrix.single q q (1 : F) : Matrix (Fin 2) (Fin 2) F))))
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hh
  have hm : (B.val * (Matrix.single q q (1 : F) : Matrix (Fin 2) (Fin 2) F) * (B.val.map σ).transpose) 0 0 =
      B.val 0 q * σ (B.val 0 q) := by
    fin_cases q <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  change (t + σ t) * _ = 0 at he
  rw [hm] at he
  have ht : t + σ t = 0 := (mul_eq_zero.mp he).resolve_right
    (mul_ne_zero hB ((map_ne_zero σ).mpr hB))
  simpa [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right ht

variable [Finite F] [Algebra (ZMod 2) F]
lemma fixes_central_displacement_iff (σ : F ≃+* F) (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) (g : Sp F) :
    (∀ X, matrixAction σ g (matrixAction σ (rootElement 0 a * rootElement 4 b) X - X) =
      matrixAction σ (rootElement 0 a * rootElement 4 b) X - X) ↔
      g ∈ centralSigmaAlpha σ a b := by
  rw [central_eq_shear, mem_centralSigmaAlpha]
  obtain ⟨q,hq⟩ : ∃ q : Fin 2, (centralBlock a b).val 0 q ≠ 0 := by
    rcases hab with ha | hb
    · exact ⟨0,ha⟩
    · exact ⟨1,hb⟩
  constructor
  · intro hf
    obtain ⟨t,rfl⟩ := shear_of_fixes σ g (centralBlock a b) q hq hf
    exact ⟨t,scalar_fixed_of_shear_fixes σ (centralBlock a b) q hq t hf,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact scalar_shear_fixes σ (centralBlock a b) ht

/-- The literal pointwise-fixer calculation on the actual matrix displacement
space. It applies to all three central involution types, including c₂. -/
theorem central_displacement_fixer_iff (σ : F ≃+* F) (a b : F)
    (hab : a ≠ 0 ∨ b ≠ 0) (g : Sp F) :
    (∀ X ∈ LinearMap.range
      (matrixAction σ (rootElement 0 a * rootElement 4 b) - LinearMap.id),
      matrixAction σ g X = X) ↔ g ∈ centralSigmaAlpha σ a b := by
  rw [← fixes_central_displacement_iff σ a b hab g]
  constructor
  · intro hf X
    exact hf _ ⟨X,rfl⟩
  · rintro hf _ ⟨X,rfl⟩
    exact hf X

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
