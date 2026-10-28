module
public import Theory.Representation.FixedFieldRestriction
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.PGroup

/-!
# Odd semilinear centralizers of fixed vectors

Let a two-group act semilinearly on a nonzero finite binary module. A
nonzero common fixed vector exists by orbit counting. Its multiples by the
fixed field of the coefficient image are again fixed. Consequently an actor
fixing all common fixed vectors has coefficient in that same two-group,
by the fixed-field theorem. An odd-order actor therefore has coefficient
one and is linear over the original scalar field.

This is the defining-field part of the field-factor elimination in
Aschbacher--Smith 10.2.3, printed p.745. It applies to the original module
action, without a choice of coordinates for the acting two-group.
-/

public noncomputable section

open Subgroup
namespace Representation.SemilinearFixedPointCentralizer
variable {F A V : Type*} [Field F] [Group A]
  [AddCommGroup V] [Module (ZMod 2) V] [Module F V] [Nontrivial V]

theorem coefficient_unique (ρ : Representation (ZMod 2) A V) (a : A)
    {σ τ : F ≃+* F}
    (hσ : ∀ c v, ρ a (c • v) = σ c • ρ a v)
    (hτ : ∀ c v, ρ a (c • v) = τ c • ρ a v) : σ = τ := by
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  have hc : ρ a (ρ a⁻¹ v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  ext c
  apply smul_left_injective F hv
  simpa only [hc] using (hσ c (ρ a⁻¹ v)).symm.trans (hτ c (ρ a⁻¹ v))

noncomputable def coefficient (ρ : Representation (ZMod 2) A V)
    (hsemi : ∀ a, ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v) :
    A →* (F ≃+* F) where
  toFun a := (hsemi a).choose
  map_one' := coefficient_unique ρ 1 (hsemi 1).choose_spec (by simp)
  map_mul' a b := coefficient_unique ρ (a*b) (hsemi (a*b)).choose_spec (by
    intro c v
    rw [map_mul]
    change ρ a (ρ b (c • v)) = (hsemi a).choose ((hsemi b).choose c) • ρ a (ρ b v)
    rw [(hsemi b).choose_spec,(hsemi a).choose_spec])

theorem coefficient_smul (ρ : Representation (ZMod 2) A V)
    (hsemi : ∀ a, ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v)
    (a : A) (c : F) (v : V) :
    ρ a (c • v) = coefficient ρ hsemi a c • ρ a v := (hsemi a).choose_spec c v

variable [Finite F]

omit [Nontrivial V] in
theorem mem_coefficient_image_of_fixes_invariants
    (ρ : Representation (ZMod 2) A V) (φ : A →* (F ≃+* F))
    (hφ : ∀ a c v, ρ a (c • v) = φ a c • ρ a v)
    (P : Subgroup A) (v : V) (hv : v ≠ 0)
    (hPv : ∀ p : P, ρ p v = v) (a : A)
    (ha : ∀ w, (∀ p : P, ρ p w = w) → ρ a w = w) : a ∈ (P.map φ).comap φ := by
  let K := P.map φ
  let E := FixedPoints.subfield K F
  let : Finite K := Finite.of_injective
    (fun g : K => (g.val : F → F))
    (fun x y h => Subtype.ext (DFunLike.coe_injective h))
  have hfix (c : E) : φ a c = c := by
    apply smul_left_injective F hv
    change φ a c • v = (c : F) • v
    calc
      φ a c • v = φ a c • ρ a v := by rw [ha v hPv]
      _ = ρ a ((c : F) • v) := (hφ a c v).symm
      _ = (c : F) • v := ha _ (by
        intro p
        rw [hφ, hPv]
        exact congrArg (fun x : F => x • v)
          (c.property ⟨φ p,mem_map_of_mem φ p.property⟩))
  let t : F →ₐ[E] F := { (φ a).toRingHom with commutes' := hfix }
  obtain ⟨g,hg⟩ := (FixedPoints.toAlgHom_bijective K F).2 t
  have he : (g : F ≃+* F) = φ a := by
    ext x
    exact DFunLike.congr_fun hg x
  change φ a ∈ K
  exact he ▸ g.property

theorem exists_nonzero_fixed [Finite V]
    (ρ : Representation (ZMod 2) A V) (P : Subgroup A) (hP : IsPGroup 2 P) :
    ∃ v : V, v ≠ 0 ∧ ∀ p : P, ρ p v = v := by
  let : MulAction P V := {
    smul p v := ρ p v
    one_smul v := by change ρ 1 v = v; simp
    mul_smul p q v := by change ρ (p.val*q.val) v = ρ p (ρ q v); rw [map_mul]; rfl }
  have hd : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 (Module.finrank_pos.ne')
  obtain ⟨v,hv,hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := V) hd (show (0 : V) ∈ MulAction.fixedPoints P V from fun p => map_zero (ρ p))
  exact ⟨v,Ne.symm hne,hv⟩

theorem odd_coefficient_eq_one_of_fixes_invariants [Finite V]
    (ρ : Representation (ZMod 2) A V) (φ : A →* (F ≃+* F))
    (hφ : ∀ a c v, ρ a (c • v) = φ a c • ρ a v)
    (P : Subgroup A) (hP : IsPGroup 2 P) (a : A)
    (hodd : Odd (orderOf (φ a)))
    (ha : ∀ w, (∀ p : P, ρ p w = w) → ρ a w = w) : φ a = 1 := by
  obtain ⟨v,hv,hPv⟩ := exists_nonzero_fixed ρ P hP
  have hm := mem_coefficient_image_of_fixes_invariants ρ φ hφ P v hv hPv a ha
  obtain ⟨k,hk⟩ := (hP.map φ) ⟨φ a,hm⟩
  have hd : orderOf (φ a) ∣ 2^k := by
    apply orderOf_dvd_of_pow_eq_one
    exact congrArg Subtype.val hk
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (hodd.coprime_two_right.pow_right k) dvd_rfl hd)
theorem linear_of_odd_of_fixes_invariants [Finite V] [Finite A]
    (ρ : Representation (ZMod 2) A V)
    (hsemi : ∀ a, ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v)
    (P : Subgroup A) (hP : IsPGroup 2 P) (b : A) (hodd : Odd (orderOf b))
    (hb : ∀ w, (∀ p : P, ρ p w = w) → ρ b w = w) :
    ∀ (c : F) (v : V), ρ b (c • v) = c • ρ b v := by
  have he := odd_coefficient_eq_one_of_fixes_invariants ρ (coefficient ρ hsemi)
    (coefficient_smul ρ hsemi) P hP b
    (hodd.of_dvd_nat (orderOf_map_dvd (coefficient ρ hsemi) b)) hb
  intro c v
  simpa only [he, RingAut.one_apply] using coefficient_smul ρ hsemi b c v
end Representation.SemilinearFixedPointCentralizer
