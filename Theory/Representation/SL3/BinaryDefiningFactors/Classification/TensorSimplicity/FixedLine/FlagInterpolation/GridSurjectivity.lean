module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.FlagInterpolation.FilteredSpace
public import Theory.Representation.PGroupRegularOrbit
public import Mathlib.FieldTheory.Finite.Basic
/-!
# Surjectivity of evaluation on the unipotent grid

For `q = |F|`, the polynomial `z^(q-1)(xy+z)^(q-1)` has grid sum `-1`.
Its right translates remain in `flagSpace K (q-1) (q-1)`: the first factor
is a linear combination of `1,x,z`, and the second of `1,y,xy+z`.
The finite p-group regular-orbit criterion therefore shows that their
evaluations span all functions on the grid. No irreducibility assertion
about tensor words or algebraic-group modules enters the argument.

Source context: GLS III, 2.8.6(a), 2.8.9 and 2.8.10(c), in
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MvPolynomial Matrix.PSL3Even.UnipotentGeometry
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
variable {F : Type*} [Field F]

private lemma sum_power [Fintype F] : (∑ x : F, x ^ (Fintype.card F - 1)) = -1 := by
  classical
  have hpos : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  calc
    _ = ∑ x : F, (1 - if x = 0 then (1:F) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x = 0
      · simp [h, zero_pow hpos.ne']
      · simp [h, FiniteField.pow_card_sub_one_eq_one x h]
    _ = -1 := by simp [Finset.sum_sub_distrib]

private lemma sum_shift_power [Fintype F] [DecidableEq F] (x z : F) :
    (∑ y : F, (x*y+z) ^ (Fintype.card F - 1)) = if x = 0 then 0 else -1 := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    calc
      _ = ∑ y : F, y ^ (Fintype.card F - 1) :=
        ((Equiv.mulLeft₀ x hx).trans (Equiv.addRight z)).sum_comp _
      _ = -1 := sum_power

private lemma norm_value [Fintype F] :
    (∑ x : F, ∑ y : F, ∑ z : F,
      z ^ (Fintype.card F - 1) * (x*y+z) ^ (Fintype.card F - 1)) = -1 := by
  classical
  calc
    _ = ∑ x : F, ∑ z : F, z ^ (Fintype.card F - 1) *
        (if x = 0 then 0 else -1) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      rw [← Finset.mul_sum, sum_shift_power]
    _ = ∑ x : F, (1 - if x = 0 then (1:F) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_mul, sum_power]
      by_cases h : x = 0 <;> simp [h]
    _ = -1 := by simp [Finset.sum_sub_distrib]

variable {K : Type*} [Field K]
private lemma mapped_norm [Fintype F] (ι : F →+* K) [Fintype (U F)] :
    (∑ u : U F, (ι u.c) ^ (Fintype.card F - 1) *
      (ι u.x * ι u.y + ι u.c) ^ (Fintype.card F - 1)) = -1 := by
  rw [show (fun u : U F => (ι u.c) ^ (Fintype.card F - 1) *
      (ι u.x * ι u.y + ι u.c) ^ (Fintype.card F - 1)) =
      fun u => ι (u.c ^ (Fintype.card F - 1) *
        (u.x * u.y + u.c) ^ (Fintype.card F - 1)) by ext u; simp]
  rw [← map_sum]
  have h : (∑ u : U F, u.c ^ (Fintype.card F - 1) *
      (u.x * u.y + u.c) ^ (Fintype.card F - 1)) = -1 := by
    calc
      _ = ∑ u : F × F × F, u.2.2 ^ (Fintype.card F - 1) *
          (u.1 * u.2.1 + u.2.2) ^ (Fintype.card F - 1) :=
        Fintype.sum_equiv (coordinates F) _ _ (fun u => rfl)
      _ = -1 := by simpa only [Fintype.sum_prod_type] using norm_value (F := F)
  rw [h, map_neg, map_one]

private lemma one_mem (a b : ℕ) : (1 : Polynomial K) ∈ flagSpace K a b :=
  flagSpace_mono (Nat.zero_le _) (Nat.zero_le _) one_mem_flagSpace_zero

private lemma const_mem (a b : ℕ) (c : K) : (C c : Polynomial K) ∈ flagSpace K a b := by
  simpa [MvPolynomial.smul_eq_C_mul] using (flagSpace K a b).smul_mem c (one_mem a b)

private lemma x_mem : (X 0 : Polynomial K) ∈ flagSpace K 1 0 := by
  apply Submodule.subset_span
  exact ⟨1,0,0,0,by omega,by omega,by simp⟩

private lemma z_mem : (X 2 : Polynomial K) ∈ flagSpace K 1 0 := by
  apply Submodule.subset_span
  exact ⟨0,1,0,0,by omega,by omega,by simp⟩

private lemma y_mem : (X 1 : Polynomial K) ∈ flagSpace K 0 1 := by
  apply Submodule.subset_span
  exact ⟨0,0,1,0,by omega,by omega,by simp⟩

private lemma t_mem : (X 0 * X 1 + X 2 : Polynomial K) ∈ flagSpace K 0 1 := by
  apply Submodule.subset_span
  exact ⟨0,0,0,1,by omega,by omega,by simp⟩

private def translatedWitness (ι : F →+* K) (m : ℕ) (g : U F) : Polynomial K :=
  (X 2 + C (ι g.c) + C (ι g.y) * X 0)^m *
    (X 0 * X 1 + X 2 + C (ι g.x) * X 1 + C (ι (g.x*g.y+g.c)))^m

private lemma translatedWitness_mem (ι : F →+* K) (m : ℕ) (g : U F) :
    translatedWitness ι m g ∈ flagSpace K m m := by
  have ha : (X 2 + C (ι g.c) + C (ι g.y) * X 0 : Polynomial K) ∈ flagSpace K 1 0 := by
    apply Submodule.add_mem _ (Submodule.add_mem _ z_mem (const_mem _ _ _))
    simpa [MvPolynomial.smul_eq_C_mul] using (flagSpace K 1 0).smul_mem (ι g.y) x_mem
  have hb : (X 0 * X 1 + X 2 + C (ι g.x) * X 1 +
      C (ι (g.x*g.y+g.c)) : Polynomial K) ∈ flagSpace K 0 1 := by
    apply Submodule.add_mem _ _ (const_mem _ _ _)
    apply Submodule.add_mem _ t_mem
    simpa [MvPolynomial.smul_eq_C_mul] using (flagSpace K 0 1).smul_mem (ι g.x) y_mem
  simpa [translatedWitness] using mul_mem_flagSpace (pow_mem_flagSpace ha m) (pow_mem_flagSpace hb m)

private lemma translatedWitness_eval [CharP K 2] (ι : F →+* K) (m : ℕ) (g u : U F) :
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

private def rightRegular : Representation K (U F) (U F → K) where
  toFun g :=
    { toFun := fun f u => f (u*g)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by ext f u; simp
  map_mul' g h := by ext f u; simp [mul_assoc]

/-- Evaluation on the complete finite-field grid. -/
def gridEvaluation (ι : F →+* K) (a b : ℕ) : flagSpace K a b →ₗ[K] (U F → K) where
  toFun p u := MvPolynomial.eval (point ι u) p.val
  map_add' p q := by ext u; simp
  map_smul' c p := by ext u; simp

/-- At maximal restricted weights, every grid function is a flag polynomial. -/
lemma gridEvaluation_surjective [Fintype F] [CharP K 2] (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2^n) :
    Function.Surjective (gridEvaluation ι (Fintype.card F - 1) (Fintype.card F - 1)) := by
  classical
  let : Fintype (U F) := Fintype.ofFinite (U F)
  let m := Fintype.card F - 1
  let f : U F → K := fun u => (ι u.c)^m * (ι u.x * ι u.y + ι u.c)^m
  have hp : IsPGroup (ringChar K) (U F) := by
    rw [ringChar.eq K 2]
    apply IsPGroup.of_card (n := n*3)
    rw [card_U, hcard, pow_mul]
  have hc : ringChar K ≠ 0 := by rw [ringChar.eq K 2]; decide
  have hn : (∑ g : U F, rightRegular g f) ≠ 0 := by
    intro hz
    have h := congrFun hz 1
    have he : (∑ g : U F, rightRegular g f) 1 = -1 := by
      simpa [rightRegular, f, m] using mapped_norm ι
    rw [he] at h
    exact neg_ne_zero.mpr (one_ne_zero : (1:K) ≠ 0) h
  have hsurj := LinearMap.surjective_of_injective
    (PGroupRegularOrbit.orbitMap_injective hc hp rightRegular f hn)
  intro v
  obtain ⟨c,hc⟩ := hsurj v
  let w : flagSpace K m m := ∑ g : U F, c g • ⟨translatedWitness ι m g, translatedWitness_mem ι m g⟩
  refine ⟨w, ?_⟩
  rw [← hc]
  ext u
  change MvPolynomial.eval (point ι u) (w.val) =
    (PGroupRegularOrbit.orbitMap rightRegular f c) u
  simp [w, PGroupRegularOrbit.orbitMap, rightRegular, translatedWitness_eval, f]
end Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
