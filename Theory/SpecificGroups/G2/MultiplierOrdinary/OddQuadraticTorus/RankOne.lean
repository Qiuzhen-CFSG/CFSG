module

public import Theory.SpecificGroups.GL2.QuadraticRegularRepresentation
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.Group

/-!
# Quadratic norm-one tori with determinant-one inverters

The norm-one units in a quadratic extension of a finite field form a cyclic
subgroup of order q+1. Regular multiplication embeds this group in SL₂.
Frobenius acts by inversion; multiplying its matrix by a regular multiplier
of inverse determinant puts the inverter in SL₂ as well. No order-two
claim is made about that corrected inverter.

This construction generalizes the checked prime-field argument in
`SymplecticFour/CentralCovers/OddPrime/LargeSections/OddNondefining/Nonsplit`.
Its consumer is the G₂ central-product torus calculation in the parent module.
Source: the nonsplit-torus calculation underlying Aschbacher–Smith I.1.1–4
and GLS III §6.1. `OrthogonalRankOne` supplies the embedding into G₂.
-/

@[expose] public section

open Matrix Subgroup

namespace Atlas.G2.MultiplierOrdinary.OddQuadraticTorus

variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Norm-one units in the actual quadratic extension. -/
noncomputable abbrev normOne :=
  rootsOfUnity (Nat.card F + 1) (FiniteField.Extension F p 2)

/-- The norm-one torus has the full nonsplit rank-one order. -/
theorem card_normOne : Nat.card (normOne F p) = Nat.card F + 1 := by
  change Nat.card (rootsOfUnity (Nat.card F + 1) (FiniteField.Extension F p 2)) = _
  rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, Nat.card_units,
    FiniteField.natCard_extension]
  apply Nat.gcd_eq_right
  rw [show Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) by
    simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1]
  exact dvd_mul_left _ _

private theorem exists_regular_norm
    (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (hdim : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) :
    ∃ (ρ : Kˣ →* GL (Fin 2) F) (w : GL (Fin 2) F),
      Function.Injective ρ ∧
      (∀ a, GeneralLinearGroup.det (ρ a) = Units.map (Algebra.norm F) a) ∧
      (∀ a, w * ρ a * w⁻¹ = ρ (Units.map σ.toRingHom.toMonoidHom a)) := by
  let b := Module.finBasisOfFinrankEq F K hdim
  let j : LinearMap.GeneralLinearGroup F K ≃* GL (Fin 2) F :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv
  let r : Kˣ →* LinearMap.GeneralLinearGroup F K :=
    Units.map (Algebra.lmul F K).toMonoidHom
  let v := LinearMap.GeneralLinearGroup.ofLinearEquiv σ.toLinearEquiv
  let ρ := j.toMonoidHom.comp r
  refine ⟨ρ, j v, j.injective.comp (Units.map_injective Algebra.lmul_injective), ?_, ?_⟩
  · intro a
    apply Units.ext
    change (LinearMap.toMatrix b b (Algebra.lmul F K (a : K))).det = Algebra.norm F (a : K)
    exact (Algebra.norm_eq_matrix_det b (a : K)).symm
  · intro a
    change j v * j (r a) * (j v)⁻¹ = j (r _)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg j
    apply Units.ext
    ext x
    change σ ((a : K) * σ.symm x) = σ (a : K) * x
    rw [map_mul, σ.apply_symm_apply]

/-- A faithful norm-one representation and its determinant-corrected inverter. -/
theorem exists_normOne_SL2 :
    ∃ (s : normOne F p →* SpecialLinearGroup (Fin 2) F)
      (v : SpecialLinearGroup (Fin 2) F),
      Function.Injective s ∧ ∀ c, v * s c * v⁻¹ = s c⁻¹ := by
  let K := FiniteField.Extension F p 2
  -- Retain Frobenius's extension algebra, rather than the other ZMod algebra instance.
  let : Algebra F K := FiniteField.instAlgebraExtension F p 2
  let C := normOne F p
  let σ := FiniteField.Extension.frob F p 2
  obtain ⟨ρ, w₀, hi, hdet, hconj⟩ := exists_regular_norm F K
    (FiniteField.finrank_extension F p 2) σ
  have hconj' (a : Kˣ) : w₀ * ρ a * w₀⁻¹ = ρ (a ^ Nat.card F) := by
    rw [hconj]
    apply congrArg ρ
    apply Units.ext
    change σ (a : K) = (a : K) ^ Nat.card F
    exact FiniteField.Extension.frob_apply F p 2
  have hexp : (Nat.card K - 1) / (Nat.card F - 1) = Nat.card F + 1 := by
    rw [FiniteField.natCard_extension,
      show Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) by
        simpa using Nat.sq_sub_sq (Nat.card F) 1]
    exact Nat.mul_div_cancel _ (Nat.sub_pos_of_lt (Finite.one_lt_card (α := F)))
  have hnorm (c : C) : Units.map (Algebra.norm F) c.val = 1 := by
    apply Units.ext
    apply (algebraMap F K).injective
    change algebraMap F K (Algebra.norm F (c.val : K)) = algebraMap F K 1
    rw [FiniteField.algebraMap_norm_eq_pow, hexp, map_one]
    exact congrArg Units.val ((mem_rootsOfUnity _ _).mp c.property)
  obtain ⟨a, ha⟩ := FiniteField.unitsMap_norm_surjective F K
    (GeneralLinearGroup.det w₀)⁻¹
  let w := ρ a * w₀
  have hwd : GeneralLinearGroup.det w = 1 := by
    change GeneralLinearGroup.det (ρ a * w₀) = 1
    rw [map_mul, hdet, ha, inv_mul_cancel]
  let r : C →* GL (Fin 2) F := ρ.comp (rootsOfUnity (Nat.card F + 1) K).subtype
  have hd (c : C) : GeneralLinearGroup.det (r c) = 1 := (hdet c.val).trans (hnorm c)
  let s : C →* SpecialLinearGroup (Fin 2) F := {
    toFun c := ⟨(r c).val, congrArg Units.val (hd c)⟩
    map_one' := Subtype.ext (congrArg Units.val r.map_one)
    map_mul' c d := Subtype.ext (congrArg Units.val (r.map_mul c d)) }
  let v : SpecialLinearGroup (Fin 2) F := ⟨w.val, congrArg Units.val hwd⟩
  have hs : Function.Injective s := by
    intro c d h
    apply Subtype.ext
    exact hi (Units.ext (congrArg Subtype.val h))
  refine ⟨s, v, hs, ?_⟩
  intro c
  apply SpecialLinearGroup.toGL_injective
  have hvGL : SpecialLinearGroup.toGL v = w := Units.ext rfl
  have hsGL (d : C) : SpecialLinearGroup.toGL (s d) = r d := Units.ext rfl
  simp only [map_mul, map_inv, hvGL, hsGL]
  change (ρ a * w₀) * ρ c.val * (ρ a * w₀)⁻¹ = (ρ c.val)⁻¹
  rw [← ρ.map_inv]
  have hc : c.val ^ Nat.card F = c.val⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact (mem_rootsOfUnity _ _).mp c.property
  calc
    (ρ a * w₀) * ρ c.val * (ρ a * w₀)⁻¹ =
        ρ a * (w₀ * ρ c.val * w₀⁻¹) * (ρ a)⁻¹ := by group
    _ = ρ a * ρ (c.val⁻¹) * (ρ a)⁻¹ := by rw [hconj', hc]
    _ = ρ (c.val⁻¹) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      simp [mul_comm]

end Atlas.G2.MultiplierOrdinary.OddQuadraticTorus

end
