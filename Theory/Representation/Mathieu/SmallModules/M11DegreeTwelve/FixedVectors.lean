module

public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Mathieu.M11.Properties.PrimeNormalizers
public import Mathlib.GroupTheory.PGroup

/-!
# Fixed vectors for the M11 eleven-normalizer through degree twelve

A faithful binary representation of degree at most twelve has an order-eleven
fixed space of dimension at most two. Its normalizer has order 55, coprime
to every binary general linear group in these dimensions, so it acts trivially
on that fixed space. In dimensions eleven and twelve, orbit counting modulo
eleven makes the fixed space nonzero.

This is the local input to the degree-twelve recognition problem associated
with James, J. Algebra 27 (1973), 57--111, and the sporadic sieve in
Aschbacher--Smith K.4, printed p.457. It does not assume a simple-module table.
-/

public section
namespace Representation.MathieuSmall.M11DegreeTwelve
open Sporadic.Mathieu BinaryOffender

private theorem action_eq_one_of_card_fiftyfive
    {N W : Type*} [Group N] [Finite N] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) N W)
    (hc : Nat.card N = 55) (hd : Module.finrank (ZMod 2) W ≤ 2) (g : N) :
    τ g = 1 := by
  let b := Module.finBasis (ZMod 2) W
  let e := Matrix.GeneralLinearGroup.toLin' b
  let φ := e.symm.toMonoidHom.comp τ.asGroupHom
  have h₁ : orderOf (φ g) ∣ 55 :=
    (orderOf_map_dvd φ g).trans (hc ▸ orderOf_dvd_natCard g)
  have hGL : Nat.card (Matrix.GeneralLinearGroup
      (Fin (Module.finrank (ZMod 2) W)) (ZMod 2)) ∣ 6 := by
    generalize Module.finrank (ZMod 2) W = d at hd ⊢
    interval_cases d <;> rw [Matrix.card_GL_field] <;> norm_num [Fin.prod_univ_succ]
  have h₂ := (orderOf_dvd_natCard (φ g)).trans hGL
  have ho : orderOf (φ g) = 1 := by
    have h := Nat.dvd_gcd h₁ h₂
    exact Nat.dvd_one.mp (by norm_num only [Nat.reduceGcd] at h ⊢; exact h)
  have he : φ g = 1 := orderOf_eq_one_iff.mp ho
  have hu : τ.asGroupHom g = 1 := e.symm.injective (by simpa [φ] using he)
  exact congrArg Units.val hu

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private noncomputable def fixedRepresentation (σ : Representation (ZMod 2) M11 V) :
    Subrepresentation (σ.comp m11Sylow11Normalizer.subtype) where
  toSubmodule := fixedSpace σ m11Sylow11Subgroup
  apply_mem_toSubmodule g v hv := by
    intro x
    have hx : (g : M11)⁻¹ * x * g ∈ m11Sylow11Subgroup := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (m11Sylow11Normalizer.inv_mem g.property) x).mp x.property
    have h := congrArg (σ g.val) (hv ⟨g.val⁻¹ * x * g.val, hx⟩)
    change σ g.val (σ (g.val⁻¹ * x * g.val) v) = σ g.val v at h
    change σ x (σ g.val v) = σ g.val v
    simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left] using h

/-- Through degree twelve, every vector fixed by the marked eleven-subgroup
is already fixed by its actual normalizer. -/
theorem normalizer_fixedSpace_eq (σ : Representation (ZMod 2) M11 V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V ≤ 12) :
    fixedSpace σ m11Sylow11Normalizer = fixedSpace σ m11Sylow11Subgroup := by
  apply le_antisymm
  · intro v hv x
    exact hv ⟨x, Subgroup.le_normalizer x.property⟩
  · have hlo := ten_le_fixedCodim_of_order_eleven σ hf
      m11Sylow11Generator m11Sylow11Generator_order
    have hsum := fixedCodim_add_finrank σ m11Sylow11Subgroup
    have hdim : Module.finrank (ZMod 2) (fixedSpace σ m11Sylow11Subgroup) ≤ 2 := by
      have he : Subgroup.zpowers m11Sylow11Generator = m11Sylow11Subgroup :=
        Subgroup.eq_of_le_of_card_ge
          (Subgroup.zpowers_le.mpr m11Sylow11Generator_mem_subgroup)
          (by rw [Nat.card_zpowers, m11Sylow11Generator_order, m11Sylow11Subgroup_card])
      rw [he] at hlo
      omega
    intro v hv g
    have h := action_eq_one_of_card_fiftyfive (fixedRepresentation σ).toRepresentation
      m11Sylow11_normalizer_card hdim g
    exact congrArg Subtype.val (LinearMap.congr_fun h ⟨v, hv⟩)

/-- The exceptional dimensions eleven and twelve force a nonzero normalizer
fixed vector. This is independent of irreducibility. -/
theorem normalizer_invariants_ne_bot (σ : Representation (ZMod 2) M11 V)
    (hf : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) V = 11 ∨ Module.finrank (ZMod 2) V = 12) :
    Representation.invariants (σ.comp m11Sylow11Normalizer.subtype) ≠ ⊥ := by
  change fixedSpace σ m11Sylow11Normalizer ≠ ⊥
  rw [normalizer_fixedSpace_eq σ hf (by omega)]
  let P := m11Sylow11Subgroup
  let : MulAction P V := {
    smul g v := σ g.val v
    one_smul v := by change σ 1 v = v; rw [map_one]; rfl
    mul_smul g h v := by change σ (g.val * h.val) v = σ g.val (σ h.val v); rw [map_mul]; rfl }
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hp : IsPGroup 11 P := IsPGroup.of_card (n := 1)
    (by simpa [P] using m11Sylow11Subgroup_card)
  intro hz
  let : Unique (MulAction.fixedPoints P V) := {
    default := ⟨0, fun g => map_zero (σ g.val)⟩
    uniq v := by
      apply Subtype.ext
      have hv : v.val ∈ fixedSpace σ P := v.property
      rw [hz] at hv
      exact hv }
  have h := hp.card_modEq_card_fixedPoints V
  have hcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    norm_num
  rw [hcard, Nat.card_unique (α := MulAction.fixedPoints P V)] at h
  rcases hd with hd | hd <;> rw [hd] at h <;> norm_num [Nat.ModEq] at h

end Representation.MathieuSmall.M11DegreeTwelve
