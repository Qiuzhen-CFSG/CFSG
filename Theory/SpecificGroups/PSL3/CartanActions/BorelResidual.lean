module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.ScalarGeneration
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Two-perfect split Borels in degree three

Odd diagonal elements lie in the two-residual. Conjugation by two explicit
diagonal matrices scales the respective simple roots nontrivially whenever
q>2; their scalar commutators generate both roots and then the central root.
The whole SL₃ Borel is consequently two-perfect. Its actual projective image
has the same property. Conjugacy transports the result to every specified
Sylow two-subgroup, including over F₄.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

@[expose] public section
open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree
namespace Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F] [Finite F]

/-- The diagonal subgroup as an actual subgroup map into the SL₃ Borel. -/
def torusInBorelSL : (Fˣ × Fˣ) →* borelSL F :=
  (torusSL F).codRestrict (borelSL F) (torusSL_mem_borel F)

/-- The unitriangular embedding, with codomain the SL₃ Borel. -/
def unipotentInBorelSL : U F →* borelSL F :=
  (specialLinear F).codRestrict (borelSL F) (fun u =>
    unipotentSL_le_borelSL F ((specialLinear_range F).le ⟨u,rfl⟩))

/-- One diagonal parameter scales the first simple root by a. -/
theorem torus_firstRoot (a : Fˣ) (x : F) :
    torusInBorelSL F (1,a) * unipotentInBorelSL F (firstRoot F (Multiplicative.ofAdd x)) *
      (torusInBorelSL F (1,a))⁻¹ =
    unipotentInBorelSL F (firstRoot F (Multiplicative.ofAdd ((a : F) * x))) := by
  apply Subtype.ext
  change torusSL F (1,a) * specialLinear F _ * (torusSL F (1,a))⁻¹ = _
  rw [← map_inv]
  apply Subtype.ext
  change (torusSL F (1,a)).val * matrix F _ * (torusSL F (1,a)⁻¹).val =
    matrix F (firstRoot F (Multiplicative.ofAdd ((a : F) * x)))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusSL_val, Matrix.diagonal_mul, Matrix.mul_diagonal, matrix, firstRoot,
      mul_comm]

/-- The other diagonal parameter scales the second simple root by a⁻¹. -/
theorem torus_secondRoot (a : Fˣ) (x : F) :
    torusInBorelSL F (a,1) * unipotentInBorelSL F (secondRoot F (Multiplicative.ofAdd x)) *
      (torusInBorelSL F (a,1))⁻¹ =
    unipotentInBorelSL F (secondRoot F (Multiplicative.ofAdd ((a⁻¹ : Fˣ) * x))) := by
  apply Subtype.ext
  change torusSL F (a,1) * specialLinear F _ * (torusSL F (a,1))⁻¹ = _
  rw [← map_inv]
  apply Subtype.ext
  change (torusSL F (a,1)).val * matrix F _ * (torusSL F (a,1)⁻¹).val =
    matrix F (secondRoot F (Multiplicative.ofAdd ((a⁻¹ : Fˣ) * x)))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusSL_val, Matrix.diagonal_mul, Matrix.mul_diagonal, matrix, secondRoot,
      mul_comm]

/-- Every diagonal element has odd order in the binary case. -/
theorem torusInBorelSL_mem_twoResidual {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (d : Fˣ × Fˣ) : torusInBorelSL F d ∈ pResidual 2 (borelSL F) := by
  apply mem_pResidual_of_orderOf_coprime
  have ho : Odd (Nat.card (Fˣ × Fˣ)) := by
    rw [Nat.card_prod]
    exact (units_odd F hF).mul (units_odd F hF)
  exact ho.coprime_two_left.of_dvd_right
    ((orderOf_map_dvd (torusInBorelSL F) d).trans (orderOf_dvd_natCard d))

/-- Both simple roots, and hence their commutator root, lie in O²(B₀). -/
theorem unipotentInBorelSL_le_twoResidual {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hq : 2 < Nat.card F) : (unipotentInBorelSL F).range ≤ pResidual 2 (borelSL F) := by
  have hex : ∃ a : Fˣ, a ≠ 1 := by
    by_contra! h
    have : Subsingleton Fˣ := ⟨fun a b => (h a).trans (h b).symm⟩
    have hc := Nat.card_of_subsingleton (1 : Fˣ)
    rw [Nat.card_units] at hc
    omega
  obtain ⟨a,ha⟩ := hex
  apply range_le_of_roots F (unipotentInBorelSL F)
  · exact scalar_root_le_normal _ _ (torusInBorelSL F (1,a))
      (torusInBorelSL_mem_twoResidual F hF (1,a)) (a : F)
      (fun h => ha (Units.ext h)) (torus_firstRoot F a)
  · exact scalar_root_le_normal _ _ (torusInBorelSL F (a,1))
      (torusInBorelSL_mem_twoResidual F hF (a,1)) (a⁻¹ : Fˣ)
      (fun h => ha (inv_eq_one.mp (Units.ext h))) (torus_secondRoot F a)

/-- The whole SL₃ Borel is two-perfect whenever q>2. -/
theorem twoResidualSL_eq_top {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hq : 2 < Nat.card F) : pResidual 2 (borelSL F) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨d,u,hu,he⟩ := borelSL_factorization F g.val g.property
  obtain ⟨v,hv⟩ := (specialLinear_range F).ge hu
  have hg : g = unipotentInBorelSL F v * torusInBorelSL F d :=
    Subtype.ext (by
      change g.val = specialLinear F v * torusSL F d
      rw [hv]
      exact he)
  rw [hg]
  exact (pResidual 2 (borelSL F)).mul_mem
    (unipotentInBorelSL_le_twoResidual F hF hq ⟨v,rfl⟩)
    (torusInBorelSL_mem_twoResidual F hF d)

/-- The actual projective image is two-perfect, including q=4. -/
theorem twoResidual_eq_top {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hq : 2 < Nat.card F) : pResidual 2 (borel F) = ⊤ := by
  let π : borelSL F →* borel F := (projection F).subgroupMap (borelSL F)
  have hπ : Function.Surjective π := (projection F).subgroupMap_surjective (borelSL F)
  rw [← map_pResidual_of_surjective 2 π hπ, twoResidualSL_eq_top F hF hq,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hπ]

end Matrix.PSL3.CartanActions.BorelQuotient

namespace Matrix.PSL3.CartanActions.BorelQuotient
variable (F : Type*) [Field F] [Finite F]

/-- Transport the two-residual to the Borel at a specified SL₃ Sylow. -/
theorem sylowSLNormalizer_twoResidual {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (hq : 2 < Nat.card F) (S : Sylow 2 SL(3,F)) :
    pResidual 2 (normalizer (S : Set SL(3,F))) = ⊤ := by
  apply (pResidual_eq_top_iff _ _).mpr
  exact ((pResidual_eq_top_iff _ _).mp (twoResidualSL_eq_top F hF hq)).of_surjective
    (sylowSLNormalizerEquiv F hn hF S).symm.toMonoidHom
    (sylowSLNormalizerEquiv F hn hF S).symm.surjective

/-- Transport the two-residual to the Borel at a specified PSL₃ Sylow. -/
theorem sylowNormalizer_twoResidual {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (hq : 2 < Nat.card F) (S : Sylow 2 PSL(3,F)) :
    pResidual 2 (normalizer (S : Set PSL(3,F))) = ⊤ := by
  apply (pResidual_eq_top_iff _ _).mpr
  exact ((pResidual_eq_top_iff _ _).mp (twoResidual_eq_top F hF hq)).of_surjective
    (sylowNormalizerEquiv F hn hF S).symm.toMonoidHom
    (sylowNormalizerEquiv F hn hF S).symm.surjective

end Matrix.PSL3.CartanActions.BorelQuotient
