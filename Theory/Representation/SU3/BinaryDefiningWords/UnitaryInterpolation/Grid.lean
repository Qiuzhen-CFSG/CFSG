module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.FlagInterpolation.FilteredSpace
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Interpolation on the upper unitary group

In characteristic two, the Hermitian coordinates satisfy `xy+z = z^q`.
Consequently `1-z^(q-1)(xy+z)^(q-1)` evaluates to the characteristic function
of the identity. Its translates lie in the flag space of weights `(q-1,q-1)`
and give every delta function on the upper unitary group. The flag-space
cube bound and the order `q^3` then imply injectivity of evaluation.

This is the finite unitary interpolation needed for the concrete binary
words of GLS III, 2.8.6(a) and 2.8.10(c), without a simplicity hypothesis.
The translation calculation follows the SL₃ `FlagInterpolation.GridSurjectivity`
module, replacing its full-grid norm argument by a Hermitian delta function.
-/

@[expose] public section
noncomputable section
open Classical
open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External
open Matrix.PSL3Even.UnipotentGeometry MvPolynomial
open Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
namespace Representation.SU3.BinaryDefiningWords.UnitaryInterpolation
variable {F K : Type*} [Field F] [Field K]

/-- Embed Hermitian root coordinates into the ambient upper-unitriangular grid. -/
def coordinates (J : HermitianForm 3 F) (z : hermitianUnipotentCoord J) : U F :=
  ⟨z.val.1, -J.conj z.val.1, z.val.2⟩

/-- Evaluation on the actual upper-unitary grid. -/
def evaluation (J : HermitianForm 3 F) (ι : F →+* K) (a b : ℕ) :
    flagSpace K a b →ₗ[K] (hermitianUnipotentCoord J → K) where
  toFun p z := MvPolynomial.eval (point ι (coordinates J z)) p.val
  map_add' p r := by ext z; simp
  map_smul' c p := by ext z; simp

/-- A Hermitian root coordinate with zero last entry is the identity. -/
theorem eq_one_of_snd_eq_zero (J : HermitianForm 3 F)
    (z : hermitianUnipotentCoord J) (hz : z.val.2 = 0) : z = 1 := by
  have hp : z.val.1 * J.conj z.val.1 = 0 := by simpa [hz] using z.property
  have hx : z.val.1 = 0 := (mul_eq_zero.mp hp).elim id (fun h => J.conj.injective (by simpa using h))
  exact Subtype.ext (Prod.ext hx hz)

private lemma one_mem (a b : ℕ) : (1 : MvPolynomial (Fin 3) K) ∈ flagSpace K a b :=
  flagSpace_mono (Nat.zero_le _) (Nat.zero_le _) one_mem_flagSpace_zero

private lemma const_mem (a b : ℕ) (c : K) : (C c : MvPolynomial (Fin 3) K) ∈ flagSpace K a b := by
  simpa [MvPolynomial.smul_eq_C_mul] using (flagSpace K a b).smul_mem c (one_mem a b)

private lemma x_mem : (X 0 : MvPolynomial (Fin 3) K) ∈ flagSpace K 1 0 := by
  apply Submodule.subset_span
  exact ⟨1,0,0,0,by omega,by omega,by simp⟩

private lemma z_mem : (X 2 : MvPolynomial (Fin 3) K) ∈ flagSpace K 1 0 := by
  apply Submodule.subset_span
  exact ⟨0,1,0,0,by omega,by omega,by simp⟩

private lemma y_mem : (X 1 : MvPolynomial (Fin 3) K) ∈ flagSpace K 0 1 := by
  apply Submodule.subset_span
  exact ⟨0,0,1,0,by omega,by omega,by simp⟩

private lemma t_mem : (X 0 * X 1 + X 2 : MvPolynomial (Fin 3) K) ∈ flagSpace K 0 1 := by
  apply Submodule.subset_span
  exact ⟨0,0,0,1,by omega,by omega,by simp⟩

/-- A translate of the complement of the Hermitian identity delta polynomial. -/
def translatedWitness (ι : F →+* K) (m : ℕ) (g : U F) : MvPolynomial (Fin 3) K :=
  (X 2 + C (ι g.c) + C (ι g.y) * X 0)^m *
    (X 0 * X 1 + X 2 + C (ι g.x) * X 1 + C (ι (g.x*g.y+g.c)))^m

lemma translatedWitness_mem (ι : F →+* K) (m : ℕ) (g : U F) :
    translatedWitness ι m g ∈ flagSpace K m m := by
  have ha : (X 2 + C (ι g.c) + C (ι g.y) * X 0 : MvPolynomial (Fin 3) K) ∈ flagSpace K 1 0 := by
    apply Submodule.add_mem _ (Submodule.add_mem _ z_mem (const_mem _ _ _))
    simpa [MvPolynomial.smul_eq_C_mul] using (flagSpace K 1 0).smul_mem (ι g.y) x_mem
  have hb : (X 0 * X 1 + X 2 + C (ι g.x) * X 1 +
      C (ι (g.x*g.y+g.c)) : MvPolynomial (Fin 3) K) ∈ flagSpace K 0 1 := by
    apply Submodule.add_mem _ _ (const_mem _ _ _)
    apply Submodule.add_mem _ t_mem
    simpa [MvPolynomial.smul_eq_C_mul] using (flagSpace K 0 1).smul_mem (ι g.x) y_mem
  simpa [translatedWitness] using mul_mem_flagSpace (pow_mem_flagSpace ha m) (pow_mem_flagSpace hb m)

lemma translatedWitness_eval [CharP K 2] (ι : F →+* K) (m : ℕ) (g u : U F) :
    MvPolynomial.eval (point ι u) (translatedWitness ι m g) =
      (ι (u*g).c)^m * (ι (u*g).x * ι (u*g).y + ι (u*g).c)^m := by
  simp only [translatedWitness, map_mul, map_add, map_pow, eval_X, eval_C,
    point, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    mul_x, mul_y, mul_c]
  congr 1
  · congr 1
    ring
  · congr 1
    calc
      _ = (ι u.x + ι g.x) * (ι u.y + ι g.y) +
          (ι u.c + ι g.c + ι u.x * ι g.y) -
          (ι u.x * ι g.y + ι u.x * ι g.y) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, sub_zero]

theorem coordinates_mul (J : HermitianForm 3 F) (u g : hermitianUnipotentCoord J) :
    coordinates J (u*g) = coordinates J u * coordinates J g := by
  apply U.ext
  · rfl
  · change -J.conj (u.val.1 + g.val.1) = -J.conj u.val.1 + -J.conj g.val.1
    rw [map_add, neg_add]
  · change u.val.2 + g.val.2 - u.val.1 * J.conj g.val.1 =
      u.val.2 + g.val.2 + u.val.1 * -J.conj g.val.1
    rw [mul_neg, sub_eq_add_neg]

/-- The maximal-weight witness is one away from the identity and zero there. -/
theorem witness_value [Finite F] [CharP F 2] (J : HermitianForm 3 F)
    (q : ℕ) (hq : 1 < q) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) (ι : F →+* K) (u : hermitianUnipotentCoord J) :
    (ι (coordinates J u).c)^(q-1) *
      (ι (coordinates J u).x * ι (coordinates J u).y + ι (coordinates J u).c)^(q-1) =
      if u = 1 then 0 else 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have ht : u.val.1 * -J.conj u.val.1 + u.val.2 = u.val.2 ^ q := by
    rw [← hconj]
    have h := u.property
    rw [CharTwo.neg_eq]
    apply eq_of_sub_eq_zero
    rw [sub_eq_add_neg, CharTwo.neg_eq]
    linear_combination h
  change (ι u.val.2)^(q-1) * (ι u.val.1 * ι (-J.conj u.val.1) + ι u.val.2)^(q-1) = _
  rw [← map_mul, ← map_add, ht, map_pow, ← pow_mul, ← pow_add]
  have he : q - 1 + q * (q - 1) = Fintype.card F - 1 := by
    have hc : Fintype.card F = q ^ 2 := by simpa [Nat.card_eq_fintype_card] using hcard
    rw [hc]
    have hq' : q - 1 + 1 = q := by omega
    have hq2 : q^2 - 1 + 1 = q^2 := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  rw [he, ← map_pow]
  by_cases hu : u = 1
  · subst u
    simp only [ite_true]
    change ι ((0:F) ^ (Fintype.card F - 1)) = 0
    rw [zero_pow (by have := Fintype.one_lt_card (α := F); omega), map_zero]
  · have hz : u.val.2 ≠ 0 := fun h => hu (eq_one_of_snd_eq_zero J u h)
    rw [if_neg hu, FiniteField.pow_card_sub_one_eq_one _ hz, map_one]

/-- Every function on the Hermitian grid is a maximal restricted flag polynomial. -/
theorem evaluation_surjective [Finite F] [CharP F 2] [CharP K 2]
    (J : HermitianForm 3 F) (q : ℕ) (hq : 1 < q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) (ι : F →+* K) :
    Function.Surjective (evaluation J ι (q-1) (q-1)) := by
  classical
  let : Fintype (hermitianUnipotentCoord J) := Fintype.ofFinite _
  let δ (g : hermitianUnipotentCoord J) : flagSpace K (q-1) (q-1) :=
    ⟨1 - translatedWitness ι (q-1) (coordinates J g⁻¹),
      (flagSpace K _ _).sub_mem (one_mem _ _) (translatedWitness_mem _ _ _)⟩
  have hδ (g u : hermitianUnipotentCoord J) : evaluation J ι _ _ (δ g) u = if u = g then 1 else 0 := by
    change MvPolynomial.eval (point ι (coordinates J u))
      (1 - translatedWitness ι (q-1) (coordinates J g⁻¹)) = _
    rw [map_sub, map_one, translatedWitness_eval, ← coordinates_mul,
      witness_value J q hq hcard hconj]
    by_cases h : u = g
    · subst u
      simp
    · have he : u * g⁻¹ ≠ 1 := by
        intro he
        apply h
        calc
          u = (u * g⁻¹) * g := by simp [mul_assoc]
          _ = g := by rw [he, one_mul]
      simp [he, h]
  intro f
  refine ⟨∑ g, f g • δ g, ?_⟩
  ext u
  simp [map_sum, map_smul, hδ]

/-- Cardinality of the literal Hermitian coordinate group. -/
theorem card_coordinates [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (q : ℕ)
    (hcard : Nat.card F = q ^ 2) (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    Nat.card (hermitianUnipotentCoord J) = q ^ 3 := by
  obtain ⟨_, _, _, _, _, _, hroot, _⟩ := huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R, _, _, _, _, _, _, _, hRcard, _, _, _, _, ⟨e, _⟩, _⟩ := hroot
  exact (Nat.card_congr e).trans hRcard

/-- Restricted flag polynomials are determined by evaluation on the unitary grid. -/
theorem eq_zero_of_eval_eq_zero [Finite F] [CharP F 2] [CharP K 2]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 0 < s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (a b : ℕ) (ha : a < 2^s) (hb : b < 2^s)
    (p : MvPolynomial (Fin 3) K) (hp : p ∈ flagSpace K a b)
    (heval : ∀ u : hermitianUnipotentCoord J,
      MvPolynomial.eval (point ι (coordinates J u)) p = 0) : p = 0 := by
  classical
  let : Fintype (hermitianUnipotentCoord J) := Fintype.ofFinite _
  let m := 2^s-1
  have hm : m + 1 = 2^s := by dsimp [m]; have := Nat.two_pow_pos s; omega
  have hq : 1 < 2^s := Nat.one_lt_pow hs.ne' (by decide)
  have hsurj := evaluation_surjective J (2^s) hq hcard hconj ι
  have hc := card_coordinates J hJ (2^s) hcard
    (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s hs hcard hconj)
  have hdimU : Module.finrank K (hermitianUnipotentCoord J → K) = (2^s)^3 := by
    rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hc]
  have hdim : Module.finrank K (flagSpace K m m) =
      Module.finrank K (hermitianUnipotentCoord J → K) := by
    apply le_antisymm
    · rw [hdimU, ← hm]
      exact finrank_flagSpace_le_cube m
    · exact LinearMap.finrank_le_finrank_of_surjective hsurj
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  have hpm : p ∈ flagSpace K m m := flagSpace_mono (show a ≤ m by omega) (show b ≤ m by omega) hp
  have he : evaluation J ι m m ⟨p,hpm⟩ = evaluation J ι m m 0 := by
    ext u
    simpa [evaluation] using heval u
  exact congrArg Subtype.val (hinj he)

end Representation.SU3.BinaryDefiningWords.UnitaryInterpolation
