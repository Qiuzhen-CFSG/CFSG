module

public import Theory.Representation.SL2NaturalFixedLifting
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Sylow fixed spaces in central extensions of the binary natural SL₂-module

Let a binary module map onto the natural plane over a field of characteristic
two, with pointwise fixed kernel. The upper-unipotent fixed space is precisely
the inverse image of the first coordinate line. This follows from fixed-point
lifting, including for nonsplit extensions.

A subspace of the fixed space, of the dimension of the defining field, on
which a nonidentity split diagonal acts with surjective displacement, is a
complement to the fixed kernel. The diagonal displacement of the entire Sylow
fixed space is then exactly that subspace.

This is the module calculation used in Aschbacher–Smith, *The Classification of
Quasithin Groups*, Lemma 14.7.65, printed pp.1069–1070 (1 March 2004 manuscript).
It uses the actual natural quotient map and does not require classification of
the universal cover in Remark 14.7.64.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix Matrix.SpecialLinearGroup Representation
open Representation.BinaryOffender

namespace Representation.SL2CentralExtension

variable {F W : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The fixed space of the actual upper-unipotent subgroup. -/
noncomputable abbrev upperFixed
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W) :=
  fixedSpace ρ (upperUnipotent F)

omit [CharP F 2] [Algebra (ZMod 2) F] in
private theorem upper_action (x : F) (v : Fin 2 → F) :
    transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one x • v =
      ![v 0 + x * v 1, v 1] := by
  ext i
  fin_cases i <;>
    simp [SpecialLinearGroup.smul_def, transvection_coe, mulVec, dotProduct,
      Fin.sum_univ_two]

/-- Fixed points lift through the central kernel for the whole upper Sylow
subgroup, not just for an individual involution. -/
theorem mem_upperFixed_iff
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (p : W →ₗ[ZMod 2] (Fin 2 → F)) (hp : Function.Surjective p)
    (he : ∀ g w, p (ρ g w) = g • p w)
    (hk : ∀ w, p w = 0 → ∀ g, ρ g w = w) (w : W) :
    w ∈ upperFixed ρ ↔ p w 1 = 0 := by
  constructor
  · intro hw
    have hw' := hw ⟨transvection zero_ne_one (1 : F),
      (mem_upperUnipotent F _).mpr ⟨1, rfl⟩⟩
    change ρ (transvection zero_ne_one (1 : F)) w = w at hw'
    have h := congrArg p hw'
    rw [he, upper_action] at h
    have h0 := congrFun h 0
    simpa using h0
  · intro hw g
    obtain ⟨x, hx⟩ := (mem_upperUnipotent F g.val).mp g.property
    apply SL2NaturalFixedLifting.fixed_lift_of_fixed_kernel ρ p.toAddMonoidHom hp
      (fun g w => he g w) hk
    change p (ρ g.val w) = p w
    rw [he, ← hx, upper_action]
    ext i
    fin_cases i <;> simp [hw]

omit [CharP F 2] [Algebra (ZMod 2) F] in
private theorem diagonal_fixed_eq_zero (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (v : Fin 2 → F) (h : diag2 a ha • v = v) : v = 0 := by
  have h0 : a * v 0 = v 0 := by
    simpa [SpecialLinearGroup.smul_def, diag2_coe', mulVec, dotProduct,
      Fin.sum_univ_two] using congrFun h 0
  have h1 : a⁻¹ * v 1 = v 1 := by
    simpa [SpecialLinearGroup.smul_def, diag2_coe', mulVec, dotProduct,
      Fin.sum_univ_two] using congrFun h 1
  have hv0 : v 0 = 0 := by
    have hz : (a - 1) * v 0 = 0 := by rw [sub_mul, one_mul, h0, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha1)
  have hv1 : v 1 = 0 := by
    have hz : (a⁻¹ - 1) * v 1 = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (inv_ne_one.mpr ha1))
  ext i
  fin_cases i <;> assumption

/-- An independent subspace of the expected dimension complements the fixed
kernel in the Sylow fixed space. -/
theorem upperFixed_decomposition [FiniteDimensional (ZMod 2) F]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (p : W →ₗ[ZMod 2] (Fin 2 → F)) (hp : Function.Surjective p)
    (he : ∀ g w, p (ρ g w) = g • p w)
    (hk : ∀ w, p w = 0 → ∀ g, ρ g w = w)
    (V : Submodule (ZMod 2) W)
    (hfix : V ≤ upperFixed ρ)
    (hdim : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) F)
    (hdisj : Disjoint V p.ker) :
    upperFixed ρ = V ⊔ p.ker := by
  have hcoord (v : V) : p v 1 = 0 :=
    (mem_upperFixed_iff ρ p hp he hk v).mp (hfix v.property)
  let f : V →ₗ[ZMod 2] F := (LinearMap.proj 0).comp (p.comp V.subtype)
  have hinj : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply (Submodule.disjoint_def.mp hdisj) _ (V.sub_mem v.property w.property)
    change p ((v : W) - w) = 0
    rw [map_sub, sub_eq_zero]
    ext i
    fin_cases i
    · exact hvw
    · exact (hcoord v).trans (hcoord w).symm
  have hsurj : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hinj, hdim]
  have hker : LinearMap.ker p ≤ upperFixed ρ := by
    intro w hw g
    exact hk w hw g
  have hsplit : upperFixed ρ = V ⊔ LinearMap.ker p := by
    apply le_antisymm
    · intro w hw
      obtain ⟨v, hv⟩ := hsurj (p w 0)
      have hpv : p v = p w := by
        ext i
        fin_cases i
        · exact hv
        · exact (hcoord v).trans ((mem_upperFixed_iff ρ p hp he hk w).mp hw).symm
      apply Submodule.mem_sup.mpr
      refine ⟨v, v.property, w - v, ?_, by simp⟩
      change p (w - v) = 0
      rw [map_sub, hpv, sub_self]
    · exact sup_le hfix hker
  exact hsplit

/-- A moved subspace has zero intersection with the central kernel: the
nonidentity split diagonal fixes no nonzero vector in the natural quotient. -/
theorem disjoint_kernel_of_diagonal_moved
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (p : W →ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g w, p (ρ g w) = g • p w)
    (hk : ∀ w, p w = 0 → ∀ g, ρ g w = w)
    (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1) (V : Submodule (ZMod 2) W)
    (hmove : LinearMap.range ((ρ (diag2 a ha) - LinearMap.id).comp V.subtype) = V) :
    Disjoint V p.ker := by
  apply Submodule.disjoint_def.mpr
  intro v hv hz
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp (hmove.symm ▸ hv)
  change ρ (diag2 a ha) u - u = v at hu
  have hpu : p u = 0 := by
    apply diagonal_fixed_eq_zero a ha ha1
    apply sub_eq_zero.mp
    rw [← he, ← map_sub, hu]
    exact hz
  rw [hk u hpu, sub_self] at hu
  exact hu.symm

/-- The fixed kernel is the full invariant subspace. -/
theorem invariants_eq_kernel
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (p : W →ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g w, p (ρ g w) = g • p w)
    (hk : ∀ w, p w = 0 → ∀ g, ρ g w = w)
    (a : F) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    ρ.invariants = p.ker := by
  apply le_antisymm
  · intro w hw
    apply diagonal_fixed_eq_zero a ha ha1
    rw [← he, hw]
  · intro w hw
    exact hk w hw

/-- The span of displacements of vectors in a subspace by a subgroup. -/
noncomputable def movedSpace
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (B : Subgroup (SpecialLinearGroup (Fin 2) F)) (C : Submodule (ZMod 2) W) :
    Submodule (ZMod 2) W :=
  ⨆ b : B, LinearMap.range ((ρ b.val - LinearMap.id).comp C.subtype)

end Representation.SL2CentralExtension
