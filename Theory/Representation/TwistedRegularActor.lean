module
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Mathlib.GroupTheory.Index

/-!
# Quadratic actors on regular coordinates with multiplicity twists

Coordinate evaluation detects two independent regular shifts even when an
arbitrary multiplicity representation twists their action. A selector on the
pairs of a fixed-point-free involution injects fixed vectors into displacement,
proving the half-dimension bound. Pure multiplicity movement contributes one
independent moved vector in every regular coordinate.

These are the regular-module calculations used for the full Suzuki Steinberg
isotypic part in the terminal quasithin argument, Aschbacher–Smith §13.6,
printed p.935. They do not assume faithfulness of either product factor.
-/

public noncomputable section
open Module Representation
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor
namespace Representation.TwistedRegular
variable {k Ω M : Type*} [Field k] [Fintype Ω]
  [AddCommGroup M] [Module k M]

/-- A fixed-point-free involution on the coordinate set moves at least half
of a function module, even with arbitrary linear twists on the fibers. -/
theorem finrank_le_twice_displacement [FiniteDimensional k M]
    (p : Ω ≃ Ω) (hp : ∀ x, p (p x) = x) (hne : ∀ x, p x ≠ x)
    (u : Ω → Module.End k M) (T : Module.End k (Ω → M))
    (hT : ∀ f x, T f x = u x (f (p x))) :
    Fintype.card Ω * finrank k M ≤ 2 * operatorFixedCodim T := by
  classical
  let e := Fintype.equivFin Ω
  let q : Module.End k (Ω → M) :=
    { toFun := fun f x => if e x < e (p x) then f x else 0
      map_add' := by intro f g; ext x; dsimp; split_ifs <;> simp_all
      map_smul' := by intro a f; ext x; dsimp; split_ifs <;> simp_all }
  let Z := LinearMap.ker (T - 1)
  let j : Z →ₗ[k] LinearMap.range (T - 1) :=
    ((T - 1).comp (q.comp Z.subtype)).codRestrict _ (fun z => ⟨q z, rfl⟩)
  have hj : Function.Injective j := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    have hzfix : T (z : Ω → M) = z := sub_eq_zero.mp z.property
    have hqfix : T (q z) = q z := by
      have h := congrArg Subtype.val hz
      exact sub_eq_zero.mp h
    apply Subtype.ext
    funext x
    change (z : Ω → M) x = 0
    have hxne : e (p x) ≠ e x := fun h => hne x (e.injective h)
    have hzx := congrFun hzfix x
    have hqx := congrFun hqfix x
    rw [hT] at hzx hqx
    by_cases hx : e x < e (p x)
    · have hpx : ¬e (p x) < e (p (p x)) := by rw [hp]; exact not_lt_of_ge hx.le
      simpa only [q, LinearMap.coe_mk, AddHom.coe_mk, hx, hpx, if_true, if_false,
        map_zero] using hqx.symm
    · have hpx : e (p x) < e (p (p x)) := by
        rw [hp]
        exact lt_of_le_of_ne (le_of_not_gt hx) hxne
      have hz0 : u x ((z : Ω → M) (p x)) = 0 := by
        simpa only [q, LinearMap.coe_mk, AddHom.coe_mk, hx, hpx, if_true, if_false] using hqx
      exact hzx.symm.trans hz0
  have hle := LinearMap.finrank_le_finrank_of_injective hj
  have hd := operatorFixedCodim_add_finrank T
  rw [Module.finrank_pi_fintype] at hd
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hd
  change finrank k Z ≤ operatorFixedCodim T at hle
  change operatorFixedCodim T + finrank k Z = _ at hd
  omega

variable {A P : Type*} [Group A] [Group P]

/-- A regular coordinate action with two independent shifts is not quadratic,
regardless of the action on its multiplicity space. -/
theorem not_quadratic_of_independent_shifts [Nontrivial M]
    (φ : A →* P) (τ : Representation k A M)
    (σ : Representation k A (P → M))
    (hσ : ∀ a f x, σ a f x = τ a (f ((φ a)⁻¹ * x)))
    (B : Subgroup A) (a b : A) (ha : a ∈ B) (hb : b ∈ B)
    (ha1 : φ a ≠ 1) (hb1 : φ b ≠ 1) (hab : φ a * φ b ≠ 1) :
    ¬ (∀ a ∈ B, ∀ b ∈ B, ∀ v, σ a (σ b v - v) = σ b v - v) := by
  classical
  intro hq
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  let f : P → M := Pi.single 1 v
  have h := congrFun (hq a ha b hb f) (φ a * φ b)
  simp only [hσ, map_sub, Pi.sub_apply] at h
  have hba : (φ b)⁻¹ * (φ a * φ b) ≠ 1 := by
    intro hz
    have hh := congrArg (fun x => φ b * x * (φ b)⁻¹) hz
    apply ha1
    simpa [mul_assoc] using hh
  have h0 : τ a (τ b v) = 0 := by
    simpa [f, mul_assoc, ha1, hb1, hab, hba] using h
  have hi : Function.Injective (τ a * τ b) := by
    rw [← map_mul]
    exact (LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom (a * b))).injective
  apply hv
  apply hi
  simpa only [Module.End.mul_apply, map_zero] using h0

/-- A quadratic twisted-regular actor has at most one nonidentity shift. -/
theorem quadratic_projection_has_two_values [Nontrivial M]
    (φ : A →* P) (τ : Representation k A M)
    (σ : Representation k A (P → M))
    (hσ : ∀ a f x, σ a f x = τ a (f ((φ a)⁻¹ * x)))
    (B : Subgroup A)
    (hq : ∀ a ∈ B, ∀ b ∈ B, ∀ v, σ a (σ b v - v) = σ b v - v) :
    ∃ p : P, ∀ a ∈ B, φ a = 1 ∨ φ a = p := by
  by_cases hall : ∀ a ∈ B, φ a = 1
  · exact ⟨1, fun a ha => Or.inl (hall a ha)⟩
  push Not at hall
  obtain ⟨a, ha, ha1⟩ := hall
  refine ⟨(φ a)⁻¹, ?_⟩
  intro b hb
  by_cases hb1 : φ b = 1
  · exact Or.inl hb1
  · right
    have hprod : φ a * φ b = 1 := by
      by_contra hne
      exact not_quadratic_of_independent_shifts φ τ σ hσ B a b ha hb ha1 hb1 hne hq
    exact by simpa using congrArg (fun x => (φ a)⁻¹ * x) hprod

/-- A nonidentity involutory shift moves at least half the regular fibers. -/
theorem shift_dimension_le_twice_displacement [Fintype P] [FiniteDimensional k M]
    (φ : A →* P) (τ : Representation k A M)
    (σ : Representation k A (P → M))
    (hσ : ∀ a f x, σ a f x = τ a (f ((φ a)⁻¹ * x)))
    (a : A) (ha : φ a ≠ 1) (ha2 : φ a * φ a = 1) :
    Fintype.card P * finrank k M ≤ 2 * operatorFixedCodim (σ a) := by
  apply finrank_le_twice_displacement (Equiv.mulLeft (φ a)⁻¹)
    (u := fun _ => τ a)
  · intro x
    change (φ a)⁻¹ * ((φ a)⁻¹ * x) = x
    rw [← mul_assoc, ← mul_inv_rev, ha2, inv_one, one_mul]
  · intro x hx
    apply ha
    have h : (φ a)⁻¹ = 1 := mul_right_cancel (show (φ a)⁻¹ * x = 1 * x by simpa using hx)
    exact inv_eq_one.mp h
  · exact hσ a

/-- Pure multiplicity movement moves at least one vector in every regular
coordinate, with no faithfulness requirement on the multiplicity action. -/
theorem card_le_displacement_of_pure_multiplicity [Fintype P] [FiniteDimensional k M]
    (φ : A →* P) (τ : Representation k A M)
    (σ : Representation k A (P → M))
    (hσ : ∀ a f x, σ a f x = τ a (f ((φ a)⁻¹ * x)))
    (a : A) (ha : φ a = 1) (hm : ∃ v, τ a v ≠ v) :
    Fintype.card P ≤ operatorFixedCodim (σ a) := by
  obtain ⟨v, hv⟩ := hm
  let f : (P → k) →ₗ[k] (P → M) :=
    { toFun := fun c x => c x • v
      map_add' := by intro c d; ext x; exact add_smul _ _ _
      map_smul' := by intro c d; ext x; exact mul_smul _ _ _ }
  let j : (P → k) →ₗ[k] LinearMap.range (σ a - 1) :=
    ((σ a - 1).comp f).codRestrict _ (fun c => ⟨f c, rfl⟩)
  have hj : Function.Injective j := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    have he := congrArg Subtype.val hc
    funext x
    have hx := congrFun he x
    change σ a (f c) x - f c x = 0 at hx
    rw [hσ, ha, inv_one, one_mul] at hx
    change τ a (c x • v) - c x • v = 0 at hx
    rw [map_smul, ← smul_sub] at hx
    exact (smul_eq_zero.mp hx).resolve_right (sub_ne_zero.mpr hv)
  have h := LinearMap.finrank_le_finrank_of_injective hj
  simpa only [Module.finrank_pi, operatorFixedCodim] using h

/-- Quadraticity bounds the full inner projection image by two. -/
theorem quadratic_projection_card_le_two [Nontrivial M]
    (φ : A →* P) (τ : Representation k A M)
    (σ : Representation k A (P → M))
    (hσ : ∀ a f x, σ a f x = τ a (f ((φ a)⁻¹ * x)))
    (hq : ∀ a b v, σ a (σ b v - v) = σ b v - v) :
    Nat.card φ.range ≤ 2 := by
  classical
  obtain ⟨p,hp⟩ := quadratic_projection_has_two_values φ τ σ hσ ⊤ (fun a _ b _ => hq a b)
  have hr (x : φ.range) : x.val = 1 ∨ x.val = p := by
    obtain ⟨a,ha⟩ := x.property
    exact ha ▸ hp a (Subgroup.mem_top _)
  let f : φ.range → Fin 2 := fun x => if x.val = 1 then 0 else 1
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    by_cases hx : x.val = 1
    · have hy : y.val = 1 := by
        by_contra hy
        have : (0 : Fin 2) = 1 := by simpa only [f, if_pos hx, if_neg hy] using h
        contradiction
      exact hx.trans hy.symm
    · have hy : y.val ≠ 1 := by
        intro hy
        have : (1 : Fin 2) = 0 := by simpa only [f, if_neg hx, if_pos hy] using h
        contradiction
      exact ((hr x).resolve_left hx).trans ((hr y).resolve_left hy).symm
  simpa using Nat.card_le_card_of_injective f hf

/-- The original actor rank is at most nine when the actual projection
kernel has at most 256 elements; its rank is not replaced by image rank. -/
theorem quadratic_actor_rank_le_nine [Nontrivial M]
    (φ : A →* P) (τ : Representation k A M)
    (σ : Representation k A (P → M))
    (hσ : ∀ a f x, σ a f x = τ a (f ((φ a)⁻¹ * x)))
    (hq : ∀ a b v, σ a (σ b v - v) = σ b v - v)
    (hker : Nat.card φ.ker ≤ 256) :
    Nat.log 2 (Nat.card A) ≤ 9 := by
  have hc : Nat.card A ≤ 512 := by
    rw [← φ.ker.card_mul_index, Subgroup.index_ker]
    have hr := quadratic_projection_card_le_two φ τ σ hσ hq
    nlinarith
  have h := Nat.log_mono_right (b := 2) hc
  exact h.trans (by decide)
end Representation.TwistedRegular
