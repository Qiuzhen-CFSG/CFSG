module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.KernelAction.Setup
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Mathlib.Tactic.LinearCombination
/-!
# Cubic generation of the Sylow subgroup over the field of order four

Choose a nonidentity unit a of order three. If u is upper unitriangular,
then both d = diag(a,a²,1) and du have order three, also after passage to
PSL₃. Indeed their distinct diagonal entries are the three cube roots of
one, and direct multiplication gives their cubes. The literal identity
u = d⁻¹(du) puts the entire unipotent subgroup in θ(B).

Conjugacy of actual Sylow subgroups transports this inclusion to every
P ∈ Syl₂(PSL₃(F)). This changes neither the field nor the component's
quotient equivalence. Placement of the preimage of N(P) in M remains a
separate local obligation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of 15.3.37, printed p.1135. This is the cubic matrix calculation
for its central-cover branch, using the concrete flag and Sylow models.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.KernelAction.CentralSylow
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

private theorem unipotent_le_theta_borel_of_cubic (a : F) (ha : a^3 = 1)
    (hsum : a^2+a+1 = 0) (hne : a ≠ 1) :
    unipotent F ≤ theta (borel F) := by
  have ht (u : U F) : projection F (cubicTriangular a ha u) ∈ theta (borel F) := by
    apply Subgroup.subset_closure
    refine ⟨mem_map_of_mem (projection F) ?_, cubicTriangular_order a ha hsum hne u⟩
    rw [mem_borelSL_iff]
    simp [cubicTriangular]
  intro g hg
  rw [← projective_range] at hg
  obtain ⟨u, rfl⟩ := hg
  have hf : projective F u = (projection F (cubicTriangular a ha 1))⁻¹ *
      projection F (cubicTriangular a ha u) := by
    rw [← map_inv, ← map_mul, ← cubicTriangular_factor a ha u, inv_mul_cancel_left]
    rfl
  rw [hf]
  exact (theta (borel F)).mul_mem ((theta (borel F)).inv_mem (ht 1)) (ht u)

/-- The genuine cubic torus generates the entire upper-unitriangular group. -/
theorem unipotent_le_theta_borel_four (hF : Nat.card F = 4) :
    unipotent F ≤ theta (borel F) := by
  have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (hc ▸ dvd_rfl)
  have ha3 : (a : F)^3 = 1 := by
    exact congrArg Units.val (ha ▸ pow_orderOf_eq_one a)
  have hne : (a : F) ≠ 1 := by
    intro hh
    have : a = 1 := Units.ext hh
    simp [this] at ha
  have hsum : (a : F)^2 + a + 1 = 0 := by
    apply (mul_eq_zero.mp (show ((a : F)-1)*((a : F)^2+a+1) = 0 from by
      linear_combination ha3)).resolve_left
    exact sub_ne_zero.mpr hne
  exact unipotent_le_theta_borel_of_cubic (a : F) ha3 hsum hne

/-- Cubic generation is transported to the supplied Sylow, without changing coordinates. -/
theorem sylow_le_theta_normalizer_four (hF : Nat.card F = 4)
    (P : Sylow 2 PSL(3,F)) : (P : Subgroup PSL(3,F)) ≤ theta (normalizer (P : Set PSL(3,F))) := by
  let T := unipotentSylow F (n := 2) (by decide) hF
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(3,F) T P
  have he : (P : Subgroup PSL(3,F)) = (unipotent F).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  change (P : Subgroup PSL(3,F)) ≤ theta (normalizer ((P : Subgroup PSL(3,F)) : Set PSL(3,F)))
  rw [he, ← map_equiv_normalizer_eq, ← theta_map_of_injective _ (MulAut.conj g).injective]
  apply map_mono
  rw [normalizer_unipotent F (n := 2) (by decide) hF]
  exact unipotent_le_theta_borel_four hF
end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.KernelAction.CentralSylow
