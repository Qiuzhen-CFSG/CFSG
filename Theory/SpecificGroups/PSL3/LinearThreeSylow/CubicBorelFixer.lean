module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Mathlib.Tactic.LinearCombination

/-!
# Rigidity of cubic Borel elements over square fields of characteristic two

For a nonidentity cube root a, both d = diag(a,a²,1) and du, with u
upper unitriangular, have order three in PSL₃. Thus fixing the Borel's
cubic elements fixes its whole unipotent subgroup. The pointwise fixer
calculation makes such an automorphism a highest-root conjugation.
Commutation with d kills that root parameter. Conjugating the prescribed
Sylow subgroup transports the result without changing the coefficient field.

The triangular calculation extends the checked field-four calculation in
`Candidates.LinearCore.KernelAction.CentralSylow.CubicRoots` to every
finite field containing a nontrivial cube root; that source is preserved.
Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

public section
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3Even.UnipotentGeometry
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree.CubicBorel
variable {F : Type*} [Field F]

private def cubicTriangular (a : F) (ha : a^3 = 1) (u : U F) : SL(3,F) :=
  ⟨!![a, a*u.x, a*u.c; 0,a^2,a^2*u.y; 0,0,1], by
    simp [Matrix.det_fin_three]
    simpa only [← pow_succ', Nat.reduceAdd] using ha⟩
private theorem cubicTriangular_cube (a : F) (ha : a^3 = 1)
    (hsum : a^2+a+1 = 0) (u : U F) : cubicTriangular a ha u ^ 3 = 1 := by
  apply Subtype.ext
  change (cubicTriangular a ha u).val ^ 3 = 1
  rw [pow_succ, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicTriangular, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring_nf
  all_goals simp only [show a^4 = a by rw [show 4 = 3+1 from rfl, pow_add, ha]; simp,
    show a^5 = a^2 by rw [show 5 = 3+2 from rfl, pow_add, ha, one_mul],
    show a^6 = 1 by rw [show 6 = 3*2 from rfl, pow_mul, ha, one_pow], ha, one_mul]
  · linear_combination u.x * hsum
  · linear_combination (u.c + u.x*u.y) * hsum
  · linear_combination u.y * hsum

private theorem cubicTriangular_order (a : F) (ha : a^3 = 1)
    (hsum : a^2+a+1 = 0) (hne : a ≠ 1) (u : U F) :
    orderOf (projection F (cubicTriangular a ha u)) = 3 := by
  apply orderOf_eq_prime
  · rw [← map_pow, cubicTriangular_cube a ha hsum, map_one]
  · intro he
    have hl : cubicTriangular a ha u ∈ lineLocalSL F := by
      rw [mem_lineLocalSL_iff]
      simp [cubicTriangular]
    have he' : (⟨cubicTriangular a ha u, hl⟩ : lineLocalSL F) = 1 :=
      lineLocal_projection_injective F (by simpa using he)
    have he00 := congrArg (fun z : lineLocalSL F => z.val.val 0 0) he'
    exact hne (by simpa [cubicTriangular] using he00)

private theorem cubicTriangular_factor (a : F) (ha : a^3 = 1) (u : U F) :
    cubicTriangular a ha 1 * specialLinear F u = cubicTriangular a ha u := by
  apply Subtype.ext
  change (cubicTriangular a ha 1).val * matrix F u = (cubicTriangular a ha u).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicTriangular, matrix, Matrix.mul_apply, Fin.sum_univ_three]

variable [Finite F]

private theorem exists_cubic_unit {n : ℕ} (heven : Even n) (hF : Nat.card F = 2 ^ n) :
    ∃ a : F, a ^ 3 = 1 ∧ a ^ 2 + a + 1 = 0 ∧ a ≠ 1 := by
  have hc : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    obtain ⟨k, rfl⟩ := heven
    have hm : 2 ^ (k + k) % 3 = 1 := by
      rw [← two_mul k, pow_mul]
      simp [Nat.pow_mod]
    omega
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hc
  have ha3 : (a : F) ^ 3 = 1 := congrArg Units.val (ha ▸ pow_orderOf_eq_one a)
  have hne : (a : F) ≠ 1 := by
    intro hh
    have : a = 1 := Units.ext hh
    simp [this] at ha
  refine ⟨a, ha3, ?_, hne⟩
  apply (mul_eq_zero.mp (show ((a : F)-1)*((a : F)^2+a+1) = 0 from by
    linear_combination ha3)).resolve_left
  exact sub_ne_zero.mpr hne

/-- Cubic elements determine every automorphism on the standard Borel. -/
theorem eq_one_of_fixes_borel_cubics {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hF : Nat.card F = 2 ^ n) (α : MulAut PSL(3,F))
    (hfix : ∀ b ∈ borel F, orderOf b = 3 → α b = b) : α = 1 := by
  obtain ⟨a, ha, hsum, hne⟩ := exists_cubic_unit heven hF
  have hct (u : U F) : α (projection F (cubicTriangular a ha u)) =
      projection F (cubicTriangular a ha u) := by
    apply hfix _ _ (cubicTriangular_order a ha hsum hne u)
    apply mem_map_of_mem (projection F)
    rw [mem_borelSL_iff]
    simp [cubicTriangular]
  have hU : ∀ u ∈ unipotent F, α u = u := by
    intro u hu
    rw [← projective_range] at hu
    obtain ⟨v, rfl⟩ := hu
    have hf : projective F v = (projection F (cubicTriangular a ha 1))⁻¹ *
        projection F (cubicTriangular a ha v) := by
      rw [← map_inv, ← map_mul, ← cubicTriangular_factor a ha v, inv_mul_cancel_left]
      rfl
    rw [hf, map_mul, map_inv, hct, hct]
  obtain ⟨z, hz, rfl⟩ := exists_projectiveCenter_of_fixes_unipotent F hn hF α hU
  obtain ⟨v, hv, rfl⟩ := hz
  have hcomm := hct 1
  change projective F v * projection F (cubicTriangular a ha 1) *
    (projective F v)⁻¹ = projection F (cubicTriangular a ha 1) at hcomm
  have he : projection F (specialLinear F v * cubicTriangular a ha 1) =
      projection F (cubicTriangular a ha 1 * specialLinear F v) := by
    rw [map_mul, map_mul]
    change projective F v * projection F (cubicTriangular a ha 1) =
      projection F (cubicTriangular a ha 1) * projective F v
    exact mul_inv_eq_iff_eq_mul.mp hcomm
  have hcT : cubicTriangular a ha 1 ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff]
    simp [cubicTriangular]
  have hvT : specialLinear F v ∈ lineLocalSL F :=
    ((specialLinear_range F).le ⟨v, rfl⟩).2
  have hm : specialLinear F v * cubicTriangular a ha 1 =
      cubicTriangular a ha 1 * specialLinear F v :=
    congrArg Subtype.val (show
      (⟨_, (lineLocalSL F).mul_mem hvT hcT⟩ : lineLocalSL F) =
      ⟨_, (lineLocalSL F).mul_mem hcT hvT⟩ from lineLocal_projection_injective F he)
  have hc := congrArg (fun m : SL(3,F) => m.val 0 2) hm
  change (matrix F v * (cubicTriangular a ha 1).val) 0 2 =
    ((cubicTriangular a ha 1).val * matrix F v) 0 2 at hc
  simp [cubicTriangular, matrix, Matrix.mul_apply, Fin.sum_univ_three] at hc
  have hvc : v.c = 0 := by
    have heq : (a - 1) * v.c = 0 := by linear_combination -hc
    exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hne)
  have hv1 : v = 1 := by
    exact U.ext ((mem_Z F v).mp hv).1 ((mem_Z F v).mp hv).2 hvc
  rw [hv1, map_one, map_one]

/-- The order-three elements of the actual Sylow normalizer have trivial
pointwise automorphism fixer. -/
theorem eq_one_of_fixes_sylowNormalizer_cubics {n : ℕ} (hn : 0 < n)
    (heven : Even n) (hF : Nat.card F = 2 ^ n) (P : Sylow 2 PSL(3,F))
    (α : MulAut PSL(3,F))
    (hfix : ∀ b ∈ normalizer (P : Set PSL(3,F)), orderOf b = 3 → α b = b) :
    α = 1 := by
  obtain ⟨g, _, hB⟩ := Matrix.PSL3.CartanActions.BorelQuotient.sylow_normalizer_conjugate F hn hF P
  let f := MulAut.conj g
  have hβ : MulAut.congr f.symm α = 1 := by
    apply eq_one_of_fixes_borel_cubics hn heven hF
    intro b hb hb3
    have hfb : f b ∈ normalizer (P : Set PSL(3,F)) := by
      rw [← hB]
      exact mem_map_of_mem f.toMonoidHom hb
    have hfb3 : orderOf (f b) = 3 :=
      (orderOf_injective f.toMonoidHom f.injective b).trans hb3
    change f.symm (α (f b)) = b
    rw [hfix _ hfb hfb3, f.symm_apply_apply]
  exact (MulAut.congr f.symm).injective (hβ.trans (map_one _).symm)

end Matrix.PSL3.LinearThree.CubicBorel
