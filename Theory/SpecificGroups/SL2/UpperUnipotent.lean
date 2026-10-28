module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The upper unipotent Sylow subgroup of SL2

The upper transvections form the range of an exposed homomorphism from the
additive group of a field. This range has the field's cardinality and, over a
finite field of characteristic p, is the underlying subgroup of the canonical
Sylow p-subgroup constructed here. The exposed definitions retain the exact
matrix convention needed for fixed-vector calculations in ABG Chapter II,
Section 4, Lemma 18(ii).

The additive transvection law constructs the homomorphism, and the upper-right
matrix entry proves injectivity. For Sylow maximality, a p-subgroup containing
the upper transvections has a nonzero fixed vector in the natural module: the
number of fixed vectors is divisible by p and includes zero. That vector lies
on the first coordinate line, so every matrix in the larger subgroup fixes that
line pointwise. The determinant-one condition then places every matrix in the
upper unipotent subgroup. This argument also covers characteristic two and
requires no ambient group-order formula.
-/

namespace Matrix.SpecialLinearGroup

variable (K : Type*) [Field K]

@[expose] public def upperUnipotentHom : Multiplicative K →*
    SpecialLinearGroup (Fin 2) K where
  toFun t := transvection (i := 0) (j := 1) zero_ne_one t.toAdd
  map_one' := transvection_coeff_zero _
  map_mul' a b := transvection_add _ a.toAdd b.toAdd

@[expose] public def upperUnipotent : Subgroup (SpecialLinearGroup (Fin 2) K) :=
  (upperUnipotentHom K).range

public theorem mem_upperUnipotent (g : SpecialLinearGroup (Fin 2) K) :
    g ∈ upperUnipotent K ↔ ∃ t : K, transvection zero_ne_one t = g := by
  rfl

public theorem upperUnipotentHom_injective : Function.Injective (upperUnipotentHom K) := by
  intro a b h
  have he := congrArg (fun g : SpecialLinearGroup (Fin 2) K => g.1 0 1) h
  simpa [upperUnipotentHom, transvection_coe] using he

public theorem card_upperUnipotent : Nat.card (upperUnipotent K) = Nat.card K := by
  exact Nat.card_congr (MonoidHom.ofInjective (upperUnipotentHom_injective K)).toEquiv.symm

private theorem upperUnipotent_isPGroup [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (upperUnipotent K) := by
  let := Fintype.ofFinite K
  obtain ⟨n, _, hn⟩ := FiniteField.card K p
  apply IsPGroup.of_card (n := (n : ℕ))
  simpa [card_upperUnipotent, Nat.card_eq_fintype_card] using hn

private theorem le_upperUnipotent_of_isPGroup [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (P : Subgroup (SpecialLinearGroup (Fin 2) K)) (hP : IsPGroup p P)
    (hUP : upperUnipotent K ≤ P) : P ≤ upperUnipotent K := by
  let := Fintype.ofFinite K
  obtain ⟨n, _, hn⟩ := FiniteField.card K p
  have hpK : p ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self p n.ne_zero
  have hpV : p ∣ Nat.card (Fin 2 → K) := by
    rw [Nat.card_fun]
    exact dvd_trans hpK (dvd_pow_self (Nat.card K) (by simp))
  have hz : (0 : Fin 2 → K) ∈ MulAction.fixedPoints P (Fin 2 → K) := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact smul_zero g
  obtain ⟨v, hv, hnv⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → K) hpV hz
  have hfix := MulAction.mem_fixedPoints.mp hv
  have ht : transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : K) ∈ P :=
    hUP ((mem_upperUnipotent K _).mpr ⟨1, rfl⟩)
  have htfix := congrFun (hfix ⟨_, ht⟩) 0
  have hv1 : v 1 = 0 := by
    simpa [SpecialLinearGroup.smul_def, transvection_coe, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] using htfix
  have hv0 : v 0 ≠ 0 := by
    intro hzero
    apply hnv
    ext i
    fin_cases i <;> simp_all
  intro g hg
  have hgfix := hfix ⟨g, hg⟩
  have h00 : g.1 0 0 = 1 := by
    have he := congrFun hgfix 0
    have he' : g.1 0 0 * v 0 = 1 * v 0 := by
      simpa [SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, hv1] using he
    exact mul_right_cancel₀ hv0 he'
  have h10 : g.1 1 0 = 0 := by
    have he := congrFun hgfix 1
    have he' : g.1 1 0 * v 0 = 0 := by
      simpa [SpecialLinearGroup.smul_def, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, hv1] using he
    exact (mul_eq_zero.mp he').resolve_right hv0
  have h11 : g.1 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] using
      g.property
  apply (mem_upperUnipotent K g).mpr
  refine ⟨g.1 0 1, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvection_coe, h00, h10, h11]

@[expose] public noncomputable def upperUnipotentSylow [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] : Sylow p (SpecialLinearGroup (Fin 2) K) :=
  { upperUnipotent K with
    isPGroup' := by exact upperUnipotent_isPGroup K p
    is_maximal' := by
      intro P hP hUP
      exact le_antisymm (le_upperUnipotent_of_isPGroup K p P hP hUP) hUP }

@[simp] public theorem coe_upperUnipotentSylow [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] :
    (upperUnipotentSylow K p : Subgroup (SpecialLinearGroup (Fin 2) K)) =
      upperUnipotent K := rfl

end Matrix.SpecialLinearGroup
