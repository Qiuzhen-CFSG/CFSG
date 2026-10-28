module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Reduction
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootOrientation.Signs
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The projective cube-root line for the elementary monomial branch

The matrix diag(a, a⁻¹, 1), with a of order three, has nontrivial projective
image. Signed coordinate transpositions invert this image, with scalar
corrections in two of the three coordinates. Their commutators put it in
every coordinate-sign derived centralizer.

An elementary subgroup of order nine in ambient three-rank two contains
this element whenever its conjugations fix or invert it. Exponent three
forces fixation; adjoining an element outside the subgroup would raise
the rank. Monomial normalization and Sylow-center position are separate
geometric obligations, not assumptions hidden in these constructions.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of refs/quasithin.pdf); the split decomposition stabilizer in
GLS3, Theorem 6.5.3(b), refs/KGroup/GLS3/chapter6.tex.
-/

public section

open Subgroup Matrix
open scoped MatrixGroups commutatorElement

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial.Monomial
variable {F : Type*} [Field F]

/-- A determinant-one diagonal matrix with one coordinate fixed. -/
@[expose] def cubeSL (a : Fˣ) : SL(3,F) :=
  ⟨Matrix.diagonal ![(a : F), (a⁻¹ : Fˣ), 1], by simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩
/-- Its image in the actual quotient by the full scalar center. -/
@[expose] def cubeElement (a : Fˣ) : PSL(3,F) := Matrix.PSL3.projection F (cubeSL a)

private theorem cubeSL_mul (a b : Fˣ) : cubeSL (a*b) = cubeSL a * cubeSL b := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

private theorem cubeSL_one : cubeSL (1 : Fˣ) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubeSL]

/-- The diagonal one-dimensional torus in the projective group. -/
@[expose] def cubeHom : Fˣ →* PSL(3,F) where
  toFun := cubeElement
  map_one' := by rw [cubeElement, cubeSL_one, map_one]
  map_mul' a b := by rw [cubeElement, cubeSL_mul, map_mul]; rfl

/-- The coordinate fixed at one prevents a nontrivial scalar kernel. -/
theorem cubeElement_injective : Function.Injective (cubeElement (F := F)) := by
  suffices Function.Injective (cubeHom (F := F)) from this
  apply (cubeHom (F := F)).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro a ha
  have hz : cubeSL a ∈ Subgroup.center SL(3,F) := by
    rw [← Matrix.PSL3.projection_ker F]
    exact ha
  obtain ⟨r, hr, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 2 2) he
  have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) he
  simp [cubeSL, Matrix.scalar] at h2 h0
  apply Units.ext
  exact h0.symm.trans h2

open Matrix.PSL3.OuterSolvable.OddPrimeCoverage

/-- Swap the two coordinates other than k and negate coordinate k. -/
@[expose] def swapSL : Fin 3 → SL(3,F)
  | 0 => ⟨!![-1,0,0;0,0,1;0,1,0], by simp [Matrix.det_fin_three]⟩
  | 1 => ⟨!![0,0,1;0,-1,0;1,0,0], by simp [Matrix.det_fin_three]⟩
  | 2 => ⟨!![0,1,0;1,0,0;0,0,-1], by simp [Matrix.det_fin_three]⟩

/-- Each signed transposition squares to the identity. -/
theorem swapSL_sq (k : Fin 3) : swapSL (F := F) k * swapSL k = 1 := by
  apply Subtype.ext
  change (swapSL k).val * (swapSL k).val = (1 : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [swapSL, Matrix.mul_apply, Fin.sum_univ_three]

/-- The signed transpositions are their own inverses. -/
theorem swapSL_inv (k : Fin 3) : (swapSL (F := F) k)⁻¹ = swapSL k :=
  inv_eq_of_mul_eq_one_left (swapSL_sq k)

/-- Diagonal elements commute with all three coordinate signs. -/
theorem cubeElement_mem_centralizer (a : Fˣ) (k : Fin 3) :
    cubeElement a ∈ centralizer ({signElement (F := F) k} : Set PSL(3,F)) := by
  apply mem_centralizer_singleton_iff.mpr
  change Matrix.PSL3.projection F (cubeSL a) * Matrix.PSL3.projection F (signSL k) =
    Matrix.PSL3.projection F (signSL k) * Matrix.PSL3.projection F (cubeSL a)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  simp only [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-- The signed transposition fixes its coordinate-sign involution. -/
theorem swapElement_mem_centralizer (k : Fin 3) :
    Matrix.PSL3.projection F (swapSL k) ∈
      centralizer ({signElement (F := F) k} : Set PSL(3,F)) := by
  apply mem_centralizer_singleton_iff.mpr
  change Matrix.PSL3.projection F (swapSL k) * Matrix.PSL3.projection F (signSL k) =
    Matrix.PSL3.projection F (signSL k) * Matrix.PSL3.projection F (swapSL k)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change (swapSL (F := F) k).val * (signSL k).val = (signSL k).val * (swapSL k).val
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [swapSL, signSL, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swap_cube_scalar (a : Fˣ) (ha : a ^ 3 = 1) (k : Fin 3) :
    cubeSL a * (swapSL k * cubeSL a * swapSL k) ∈ center SL(3,F) := by
  have hpow : (a : F) ^ 3 = 1 := congrArg Units.val ha
  have hinv : ((a⁻¹ : Fˣ) : F) = (a : F) ^ 2 := by
    have h : a⁻¹ = a ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      simpa only [← pow_succ'] using ha
    exact congrArg Units.val h
  have hfinv : (a : F)⁻¹ = (a : F) ^ 2 := by
    simpa only [Units.val_inv_eq_inv_val] using hinv
  have hmul : (a : F) * (a : F) * (a : F) = 1 := by simpa only [pow_succ, pow_zero, one_mul] using hpow
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  fin_cases k
  · refine ⟨(a : F)^2, ?_, ?_⟩
    · change ((a : F)^2)^3 = 1
      rw [← pow_mul, Nat.mul_comm 2 3, pow_mul, hpow, one_pow]
    · simp only [Matrix.SpecialLinearGroup.coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cubeSL, swapSL, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_three, Matrix.scalar, hfinv, pow_two]
  · refine ⟨(a : F), hpow, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubeSL, swapSL, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three, Matrix.scalar, hfinv, pow_two]
    linear_combination -(a : F) * (hmul)
  · refine ⟨1, by simp, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubeSL, swapSL, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three, Matrix.scalar]

/-- A signed transposition inverts the cube-root element projectively.
For k = 0 or 1 the corresponding linear equality has a scalar factor. -/
theorem swapElement_conj_cube (a : Fˣ) (ha : a ^ 3 = 1) (k : Fin 3) :
    Matrix.PSL3.projection F (swapSL k) * cubeElement a *
      (Matrix.PSL3.projection F (swapSL k))⁻¹ = (cubeElement a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have hh := (QuotientGroup.eq_one_iff _).mpr (swap_cube_scalar a ha k)
  change Matrix.PSL3.projection F (cubeSL a * (swapSL k * cubeSL a * swapSL k)) = 1 at hh
  rw [map_mul, map_mul, map_mul] at hh
  simpa only [← map_inv, swapSL_inv, cubeElement] using hh

/-- An explicit commutator puts the cube-root element in each of the three
coordinate-sign derived centralizers. -/
theorem cubeElement_mem_derived (a : Fˣ) (ha : a ^ 3 = 1) (k : Fin 3) :
    cubeElement a ∈ ⁅centralizer ({signElement (F := F) k} : Set PSL(3,F)),
      centralizer ({signElement k} : Set PSL(3,F))⁆ := by
  have hc : cubeElement a ^ 3 = 1 := by
    change cubeHom a ^ 3 = 1
    rw [← map_pow, ha, map_one]
  have hinv : (cubeElement a)⁻¹ * (cubeElement a)⁻¹ = cubeElement a := by
    have hh : cubeElement a * (cubeElement a * cubeElement a) = 1 := by
      simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hc
    exact inv_inj.mp (by simpa using (inv_eq_of_mul_eq_one_right hh).symm)
  have he : ⁅Matrix.PSL3.projection F (swapSL k), cubeElement a⁆ = cubeElement a := by
    rw [commutatorElement_def, swapElement_conj_cube a ha k, hinv]
  rw [← he]
  exact commutator_mem_commutator (swapElement_mem_centralizer k) (cubeElement_mem_centralizer a k)

private theorem commute_of_cube_eq_one_of_conj_eq_or_inv {G : Type*} [Group G]
    {u x : G} (hu : u ^ 3 = 1) (hc : u * x * u⁻¹ = x ∨ u * x * u⁻¹ = x⁻¹) :
    Commute u x := by
  apply (mul_inv_eq_iff_eq_mul).mp
  rcases hc with h | h
  · exact h
  · let f : MulAut G := MulAut.conj u
    have hf : f ^ 3 = 1 := by
      change (MulAut.conj u)^3 = 1
      rw [← map_pow, hu, map_one]
    have hfx : f x = x⁻¹ := h
    have h3 : f (f (f x)) = x := DFunLike.congr_fun hf x
    rw [hfx, map_inv, hfx, inv_inv, hfx] at h3
    exact h.trans h3

/-- If U fixes or inverts this element, its exponent three forces fixation.
Adjoining the fixed element would otherwise contradict the ambient three-rank. -/
theorem cubeElement_mem_elementary [Finite F]
    (U : Subgroup PSL(3,F)) (hU : IsElementaryAbelian 3 U) (hcard : Nat.card U = 9)
    (hrank : primeRank 3 PSL(3,F) = 2)
    (a : Fˣ) (ha : orderOf a = 3)
    (hconj : ∀ u ∈ U, u * cubeElement a * u⁻¹ = cubeElement a ∨
      u * cubeElement a * u⁻¹ = (cubeElement a)⁻¹) : cubeElement a ∈ U := by
  let _ := hU
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfix : U ≤ centralizer ({cubeElement a} : Set PSL(3,F)) := by
    intro u hu
    exact mem_centralizer_singleton_iff.mpr
      (commute_of_cube_eq_one_of_conj_eq_or_inv
        (elemPow_eq_one_of_isElementaryAbelian (p := 3) u hu) (hconj u hu))
  by_contra hn
  have ho : orderOf (cubeElement a) = 3 :=
    (orderOf_injective (cubeHom (F := F)) cubeElement_injective a).trans ha
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join U (cubeElement a) ho hn hfix
    (show Nat.card U = 3 ^ 2 by omega)
  rw [hrank] at hh
  omega

/-- The split congruence supplies an actual unit of order three. -/
theorem exists_unit_order_three [Finite F] (hmod : Nat.card F % 3 = 1) :
    ∃ a : Fˣ, orderOf a = 3 := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply exists_prime_orderOf_dvd_card'
  rw [Nat.card_units]
  exact Nat.dvd_of_mod_eq_zero (by omega)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial.Monomial
