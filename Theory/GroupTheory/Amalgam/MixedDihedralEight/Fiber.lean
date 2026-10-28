module

public import Theory.GroupTheory.Amalgam.DihedralTwelvePair
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Logic.Equiv.Prod

/-!
# Reconstruction of a cubic extension with a marked two-complement

A vertex with normal cubic residual and quotient S₃ embeds in the product
of its Sylow complement and S₃. Its image is the fiber product of the
complement character with the sign map. The construction keeps every
complement element fixed, so it is suitable for compatible amalgam maps.

Source: the exceptional vertices of Aschbacher–Smith F.6.5, printed p.305.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.RankTwoAmalgam
namespace CubicFiber

abbrev S3 := Equiv.Perm (Fin 3)

def reflection : ℤˣ →* S3 where
  toFun ε := if ε = 1 then 1 else Equiv.swap 0 1
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem sign_reflection : ∀ ε, Equiv.Perm.sign (reflection ε) = ε := by decide +kernel

variable {B B' : Type*} [Group B] [Group B']

def group (χ : B →* ℤˣ) : Subgroup (B × S3) :=
  (χ.comp (MonoidHom.fst B S3)).eqLocus
    (Equiv.Perm.sign.comp (MonoidHom.snd B S3))

def inclusion (χ : B →* ℤˣ) : B →* group χ :=
  ((MonoidHom.id B).prod (reflection.comp χ)).codRestrict (group χ)
    (fun b => (sign_reflection (χ b)).symm)

theorem inclusion_injective (χ : B →* ℤˣ) : Function.Injective (inclusion χ) :=
  fun _ _ he => congrArg (fun x : group χ => x.val.1) he

theorem card [Finite B] (χ : B →* ℤˣ) : Nat.card (group χ) = 3 * Nat.card B := by
  classical
  let : Fintype B := Fintype.ofFinite B
  have hc : ∀ ε : ℤˣ, Fintype.card {s : S3 // ε = Equiv.Perm.sign s} = 3 := by decide +kernel
  change Nat.card {x : B × S3 // χ x.1 = Equiv.Perm.sign x.2} = _
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun b s => χ b = Equiv.Perm.sign s)), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  omega

def congr (χ : B →* ℤˣ) (u : B ≃* B') :
    group χ ≃* group (χ.comp u.symm.toMonoidHom) where
  toFun x := ⟨(u x.val.1, x.val.2), by
    change χ (u.symm (u x.val.1)) = Equiv.Perm.sign x.val.2
    rw [u.symm_apply_apply]
    exact x.property⟩
  invFun x := ⟨(u.symm x.val.1, x.val.2), x.property⟩
  left_inv x := by apply Subtype.ext; apply Prod.ext <;> simp
  right_inv x := by apply Subtype.ext; apply Prod.ext <;> simp
  map_mul' x y := by
    apply Subtype.ext
    exact Prod.ext (u.map_mul x.val.1 y.val.1) rfl

theorem congr_inclusion (χ : B →* ℤˣ) (u : B ≃* B') (b : B) :
    congr χ u (inclusion χ b) = inclusion (χ.comp u.symm.toMonoidHom) (u b) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change reflection (χ b) = reflection (χ (u.symm (u b)))
    rw [u.symm_apply_apply]

private theorem normalize {B : Type*} [Group B]
    (f : B →* S3) (hc : Nat.card f.range = 2) :
    ∃ a : S3 ≃* S3, ∀ b, a (f b) = reflection (Equiv.Perm.sign (a (f b))) := by
  classical
  obtain ⟨t, ht, hunique⟩ := (Nat.card_eq_two_iff' (1 : f.range)).mp hc
  have ht2 : (t : S3) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := t)
    rw [hc] at hh
    exact congrArg Subtype.val hh
  have htn : (t : S3) ≠ 1 := fun he => ht (Subtype.ext he)
  have conjugate : ∀ x : S3, x ≠ 1 → x ^ 2 = 1 →
      ∃ g : S3, g * x * g⁻¹ = Equiv.swap 0 1 := by decide +kernel
  obtain ⟨g, hg⟩ := conjugate t htn ht2
  refine ⟨MulAut.conj g, ?_⟩
  intro b
  by_cases hb : f b = 1
  · simp only [hb, map_one]
  · have hh : (⟨f b, ⟨b, rfl⟩⟩ : f.range) = t :=
      hunique _ (fun he => hb (congrArg Subtype.val he))
    have he : (MulAut.conj g) (f b) = Equiv.swap 0 1 :=
      (congrArg (fun x : f.range => g * (x : S3) * g⁻¹) hh).trans hg
    rw [he]
    decide +kernel

/-- Reconstruction retains the entire marked complement and its exact kernel. -/
theorem exists_equiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (i : B →* A) (f : A →* S3)
    (hcard : Nat.card A = 3 * Nat.card B)
    (himage : Nat.card (f.comp i).range = 2) (hker : f.ker ≤ i.range)
    (r : A →* B) (hr : ∀ b, r (i b) = b) :
    ∃ χ : B →* ℤˣ, χ.ker = (f.comp i).ker ∧
      ∃ e : A ≃* group χ, ∀ b, e (i b) = inclusion χ b := by
  classical
  obtain ⟨a, ha⟩ := normalize (f.comp i) himage
  let f' := a.toMonoidHom.comp f
  let χ := Equiv.Perm.sign.comp (f'.comp i)
  have hχker : χ.ker = (f.comp i).ker := by
    ext b
    change Equiv.Perm.sign (a (f (i b))) = 1 ↔ f (i b) = 1
    constructor
    · intro hb
      apply a.injective
      rw [map_one]
      exact (ha b).trans (by change reflection (Equiv.Perm.sign (a (f (i b)))) = 1; rw [hb, map_one])
    · intro hb
      rw [hb, map_one, map_one]
  have hrs : Function.Surjective r := fun b => ⟨i b, hr b⟩
  have hrCard : Nat.card r.ker = 3 := by
    have hh := r.ker.card_mul_index
    have hi : r.ker.index = Nat.card B := by
      rw [index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r hrs).toEquiv]
    rw [hi, hcard] at hh
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := B)) hh
  have hsign (x : A) : χ (r x) = Equiv.Perm.sign (f' x) := by
    let y : r.ker := ⟨x * (i (r x))⁻¹, by
      change r (x * (i (r x))⁻¹) = 1
      rw [map_mul, map_inv, hr, mul_inv_cancel]⟩
    have hy3 : (y : A) ^ 3 = 1 := by
      have hh := pow_card_eq_one' (x := y)
      rw [hrCard] at hh
      exact congrArg Subtype.val hh
    have hs3 : (Equiv.Perm.sign (f' y)) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, hy3, map_one, map_one]
    have units3 : ∀ ε : ℤˣ, ε ^ 3 = 1 → ε = 1 := by decide +kernel
    have hh := units3 _ hs3
    change Equiv.Perm.sign (f' (x * (i (r x))⁻¹)) = 1 at hh
    rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at hh
    exact hh.symm
  let m : A →* group χ := (r.prod f').codRestrict (group χ) hsign
  have hm : Function.Injective m := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro x hx
    have hx1 : r x = 1 := congrArg (fun y : group χ => y.val.1) hx
    have hx2 : f x = 1 := by
      apply a.injective
      exact (congrArg (fun y : group χ => y.val.2) hx).trans a.map_one.symm
    obtain ⟨b, rfl⟩ := hker hx2
    rw [hr] at hx1
    simp only [hx1, map_one, mem_bot]
  let e := MulEquiv.ofBijective m ((Nat.bijective_iff_injective_and_card m).mpr
    ⟨hm, hcard.trans (card χ).symm⟩)
  refine ⟨χ, hχker, e, ?_⟩
  intro b
  apply Subtype.ext
  exact Prod.ext (hr b) (ha b)

end CubicFiber
end Theory.GroupTheory.RankTwoAmalgam
