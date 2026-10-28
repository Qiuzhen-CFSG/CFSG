module

public import Theory.Representation.SL2NaturalOffenders.Internal
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The coefficient action of a binary semilinear representation

The scalar automorphism of each invertible actor is unique, so semilinearity
constructs a homomorphism to the actual field automorphism group. Its image on
an elementary abelian two-subgroup has order at most two: finite-field
Galois theory makes the target cyclic. A nontrivial coefficient automorphism
also bounds the common fixed space by the field order, by embedding two copies
of that space into the natural two-dimensional space.

These are intrinsic counting inputs for the natural-module case of
Aschbacher--Smith, *The Classification of Quasithin Groups*, B.4.2(1),
combined manuscript (1 March 2004), printed p.86. They do not assume a normal
SL₂ subgroup or offender containment.
-/

public section

open Representation.BinaryOffender
namespace Representation.SL2NaturalOffenders
variable {F H : Type*} [Field F] [Algebra (ZMod 2) F] [Group H]

/-- An invertible semilinear actor determines its scalar automorphism uniquely. -/
theorem semilinear_coefficient_unique
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (h : H)
    {σ τ : F ≃+* F}
    (hσ : ∀ c v, ρ h (c • v) = σ c • ρ h v)
    (hτ : ∀ c v, ρ h (c • v) = τ c • ρ h v) : σ = τ := by
  have hcancel (v : Fin 2 → F) : ρ h (ρ h⁻¹ v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  ext c
  have he := (hσ c (ρ h⁻¹ ![1, 0])).symm.trans (hτ c (ρ h⁻¹ ![1, 0]))
  simpa only [hcancel, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one]
    using congrFun he 0

/-- The actual action on field scalars supplied by semilinearity. -/
@[expose] noncomputable def fieldAction
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hsemi : ∀ h : H, ∃ σ : F ≃+* F, ∀ c v, ρ h (c • v) = σ c • ρ h v) :
    H →* (F ≃+* F) where
  toFun h := (hsemi h).choose
  map_one' := semilinear_coefficient_unique ρ 1 (hsemi 1).choose_spec (by simp)
  map_mul' a b := semilinear_coefficient_unique ρ (a * b) (hsemi (a * b)).choose_spec
    (by
      intro c v
      rw [map_mul]
      change ρ a (ρ b (c • v)) = (hsemi a).choose ((hsemi b).choose c) • ρ a (ρ b v)
      rw [(hsemi b).choose_spec, (hsemi a).choose_spec])

/-- The coefficient action satisfies the supplied semilinearity equation. -/
theorem fieldAction_smul
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hsemi : ∀ h : H, ∃ σ : F ≃+* F, ∀ c v, ρ h (c • v) = σ c • ρ h v)
    (h : H) (c : F) (v : Fin 2 → F) :
    ρ h (c • v) = fieldAction ρ hsemi h c • ρ h v := (hsemi h).choose_spec c v

/-- Trivial coefficient action is exactly linearity over the field. -/
theorem fieldAction_eq_one_iff
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hsemi : ∀ h : H, ∃ σ : F ≃+* F, ∀ c v, ρ h (c • v) = σ c • ρ h v)
    (h : H) : fieldAction ρ hsemi h = 1 ↔ ∀ (c : F) (v : Fin 2 → F), ρ h (c • v) = c • ρ h v := by
  constructor
  · intro he c v
    simpa only [he, RingAut.one_apply] using fieldAction_smul ρ hsemi h c v
  · exact fun hl => semilinear_coefficient_unique ρ h (fieldAction_smul ρ hsemi h) hl

/-- Automorphisms of a finite binary field form a cyclic group. -/
theorem binaryFieldAut_isCyclic [Finite F] : IsCyclic (F ≃+* F) := by
  let e : (F ≃+* F) ≃* (F ≃ₐ[ZMod 2] F) := {
    toFun σ := AlgEquiv.ofRingEquiv (f := σ) (by
      intro x
      have hh : σ.toRingHom.comp (algebraMap (ZMod 2) F) = algebraMap (ZMod 2) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun hh x)
    invFun σ := σ.toRingEquiv
    left_inv σ := by ext x; rfl
    right_inv σ := by ext x; rfl
    map_mul' σ τ := by ext x; rfl }
  exact e.isCyclic.mpr inferInstance

/-- An elementary abelian two-group has coefficient image of order at most two. -/
theorem fieldAction_range_card_le_two [Finite F]
    (A : Subgroup H) (hA : IsElementaryAbelian 2 A) (φ : A →* (F ≃+* F)) :
    Nat.card φ.range ≤ 2 := by
  let : IsCyclic (F ≃+* F) := binaryFieldAut_isCyclic
  have he : Monoid.exponent φ.range ∣ 2 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    rintro ⟨σ, a, rfl⟩
    apply Subtype.ext
    change φ a ^ 2 = 1
    rw [← map_pow]
    have ha : a ^ 2 = 1 := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p) a
    rw [ha, map_one]
  rw [IsCyclic.exponent_eq_card] at he
  exact Nat.le_of_dvd (by decide) he

/-- An elementary semilinear group is at most twice the size of its linear kernel. -/
theorem card_le_two_mul_fieldAction_ker [Finite F]
    (A : Subgroup H) (hA : IsElementaryAbelian 2 A) (φ : A →* (F ≃+* F)) :
    Nat.card A ≤ 2 * Nat.card φ.ker := by
  calc
    Nat.card A = Nat.card φ.ker * Nat.card φ.range := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    _ ≤ Nat.card φ.ker * 2 := Nat.mul_le_mul_left _ (fieldAction_range_card_le_two A hA φ)
    _ = 2 * Nat.card φ.ker := Nat.mul_comm _ _


/-- A nontrivial field action bounds the common fixed space by the field order. -/
theorem fixedSpace_card_le_of_nontrivial_coefficient [Finite F]
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (A : Subgroup H)
    (a : A) (σ : F ≃+* F) (hne : σ ≠ 1)
    (hσ : ∀ (c : F) (v : Fin 2 → F), ρ a (c • v) = σ c • ρ a v) :
    Nat.card (fixedSpace ρ A) ≤ Nat.card F := by
  obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
    by_contra! h
    exact hne (RingEquiv.ext h)
  have hfixed (v : fixedSpace ρ A) : ρ (a : H) v.val = v.val := v.property a
  let f : fixedSpace ρ A × fixedSpace ρ A → (Fin 2 → F) :=
    fun x => x.1.val + c • x.2.val
  have hf : Function.Injective f := by
    intro x y he
    change x.1.val + c • x.2.val = y.1.val + c • y.2.val at he
    have he' := congrArg (ρ (a : H)) he
    simp only [map_add, hσ, hfixed] at he'
    have hz : (σ c - c) • (x.2.val - y.2.val) = 0 := by
      calc
        _ = ((x.1.val + σ c • x.2.val) - (y.1.val + σ c • y.2.val)) -
            ((x.1.val + c • x.2.val) - (y.1.val + c • y.2.val)) := by
          simp only [sub_smul, smul_sub]
          abel
        _ = 0 := by rw [he, he']; simp
    have h2 : x.2.val = y.2.val :=
      sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc))
    have h1 : x.1.val = y.1.val := by rw [h2] at he; exact add_right_cancel he
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hb := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, pow_two] at hb
  nlinarith

end Representation.SL2NaturalOffenders
