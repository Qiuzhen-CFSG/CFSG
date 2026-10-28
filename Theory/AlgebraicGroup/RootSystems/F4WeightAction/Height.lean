module

public import Theory.AlgebraicGroup.RootSystems.F4WeightAction
public import Theory.AlgebraicGroup.RootSystems.WeylOrbitHeight
public import Mathlib.Tactic
/-!
# Height and dominance on the actual F4 weight lattice

The integer height is 11a₀+21a₁+15a₂+8a₃. Its value on each simple root
is one. The determinant-one Cartan calculation identifies it with root
height in the original real root space. The actual coroot comparison
identifies dominance with nonnegative fundamental coordinates. Thus orbit
maxima are dominant and have nonnegative height; a dominant point is the
unique point of greatest height in its Weyl orbit.

Source: Steinberg (1963), §3.9(b), highest-monomial reduction. These are the
literal lattice hypotheses for fundamental-orbit-sum generation.
-/

open scoped BigOperators Matrix
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
public noncomputable section
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
noncomputable local instance : Fintype typeF4Roots := Fintype.ofFinite _

@[expose] noncomputable def height : Weight →ₗ[ℤ] ℤ where
  toFun a := 11 * a 0 + 21 * a 1 + 15 * a 2 + 8 * a 3
  map_add' a b := by simp; ring
  map_smul' c a := by simp; ring

lemma height_root (i : Fin 4) : height (rootWeight (typeF4SimpleRootIndex i)) = 1 := by
  fin_cases i <;> norm_num [height, rootWeight_simple, typeF4CartanMatrix] <;> decide

private def invCartan : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2,3,4,2; 3,6,8,4; 2,4,6,3; 1,2,3,2]

private lemma fundamental_eq (i : Fin 4) :
    Pi.single i 1 = ∑ j : Fin 4, invCartan i j • rootWeight (typeF4SimpleRootIndex j) := by
  ext k
  fin_cases i <;> fin_cases k <;>
    norm_num [Fin.sum_univ_four, Pi.single_apply, rootWeight_simple, typeF4CartanMatrix,
      invCartan] <;> decide

private noncomputable def realHeight : Weight →ₗ[ℤ] ℝ where
  toFun a := (height a : ℝ)
  map_add' a b := by simp
  map_smul' c a := by
    change ((height (c • a) : ℤ) : ℝ) = c • ((height a : ℤ) : ℝ)
    rw [map_smul]
    simp only [smul_eq_mul, Int.cast_mul, zsmul_eq_mul]

lemma height_realization (a : Weight) :
    typeF4RootPairing_base.chamberFunctional (realization a) = (height a : ℝ) := by
  let f : Weight →ₗ[ℤ] ℝ :=
    (typeF4RootPairing_base.chamberFunctional.restrictScalars ℤ).comp realization
  have he : f = realHeight := by
    apply (Pi.basisFun ℤ (Fin 4)).ext
    intro i
    rw [Pi.basisFun_apply]
    change typeF4RootPairing_base.chamberFunctional (realization (Pi.single i 1)) =
      (height (Pi.single i 1) : ℝ)
    have hh (j : Fin 4) : typeF4RootPairing_base.chamberFunctional
        (typeF4RootPairing.root (typeF4SimpleRootIndex j)) = 1 :=
      typeF4RootPairing_base.chamberFunctional_root (typeF4RootPairing_baseEquiv j)
    have ht := congrArg
      (fun a => typeF4RootPairing_base.chamberFunctional (realization a)) (fundamental_eq i)
    simp only [map_sum, map_smul, realization_root, map_zsmul, hh] at ht
    rw [ht]
    fin_cases i <;> norm_num [invCartan, Fin.sum_univ_four, height, Pi.single_apply, Fin.ext_iff, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]
  exact LinearMap.congr_fun he a

lemma dominant_iff_nonneg (a : Weight) :
    realization a ∈ typeF4RootPairing_base.dominantChamber ↔ ∀ i, 0 ≤ a i := by
  have hformula (i : Fin 4) := RootPairing.two_mul_rootForm_apply_root
    typeF4RootPairing (typeF4SimpleRootIndex i) (realization a)
  have hcor (i : Fin 4) : typeF4RootPairing.coroot' (typeF4SimpleRootIndex i) (realization a) =
      (a i : ℝ) := realization_coroot a i
  constructor
  · intro ha i
    have hh := ha (typeF4RootPairing_baseEquiv i)
    change 0 ≤ typeF4RootPairing.RootForm (realization a)
      (typeF4RootPairing.root (typeF4SimpleRootIndex i)) at hh
    have he := hformula i
    rw [hcor] at he
    have hpos := RootPairing.rootForm_root_self_pos typeF4RootPairing (typeF4SimpleRootIndex i)
    have hai : 0 ≤ (a i : ℝ) := by nlinarith
    exact_mod_cast hai
  · intro ha j
    obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
    have he := hformula i
    rw [hcor] at he
    have hpos := RootPairing.rootForm_root_self_pos typeF4RootPairing (typeF4SimpleRootIndex i)
    have hai : 0 ≤ (a i : ℝ) := by exact_mod_cast ha i
    change 0 ≤ typeF4RootPairing.RootForm (realization a)
      (typeF4RootPairing.root (typeF4SimpleRootIndex i))
    nlinarith

lemma nonneg_of_maximal_height (a : Weight)
    (ha : ∀ w : Weyl, height (representation w a) ≤ height a) : ∀ i, 0 ≤ a i := by
  intro i
  have hi := ha (RootPairing.weylGroup.ofIdx typeF4RootPairing (typeF4SimpleRootIndex i))
  rw [representation_simple, map_sub, map_smul, height_root] at hi
  simp only [smul_eq_mul, mul_one] at hi
  omega

lemma height_nonneg_of_maximal (a : Weight)
    (ha : ∀ w : Weyl, height (representation w a) ≤ height a) : 0 ≤ height a := by
  have h := nonneg_of_maximal_height a ha
  change 0 ≤ 11 * a 0 + 21 * a 1 + 15 * a 2 + 8 * a 3
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  omega

lemma height_representation_le (a : Weight) (ha : ∀ i, 0 ≤ a i) (w : Weyl) :
    height (representation w a) ≤ height a := by
  have h := WeylOrbitHeight.height_le_of_dominant typeF4RootPairing_base
    (realization a) ((dominant_iff_nonneg a).mpr ha) w
  change typeF4RootPairing_base.chamberFunctional (w • realization a) ≤ _ at h
  rw [← realization_representation, height_realization, height_realization] at h
  exact_mod_cast h

lemma height_representation_eq_iff (a : Weight) (ha : ∀ i, 0 ≤ a i) (w : Weyl) :
    height (representation w a) = height a ↔ representation w a = a := by
  constructor
  · intro h
    apply realization_injective
    rw [realization_representation]
    apply (WeylOrbitHeight.height_eq_iff_of_dominant typeF4RootPairing_base
      (realization a) ((dominant_iff_nonneg a).mpr ha) w).mp
    change typeF4RootPairing_base.chamberFunctional (w • realization a) = _
    rw [← realization_representation, height_realization, height_realization, h]
  · intro h
    rw [h]

end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction
