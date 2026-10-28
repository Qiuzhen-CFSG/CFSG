module

public import Theory.Representation.BinaryOffender.Basic
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Quadratic semilinear groups with an outer field twist

Two operators with the same field twist have a field-stable difference
image. Quadraticity makes that image fixed by every actor. A nontrivial
field twist cannot fix a nonzero field subspace pointwise, so the twist
assignment is injective. Over a field of order four the group has order
at most two. No coordinate dimension or splitting assumption is used.

Source application: the order-two contradiction in MS93 (3.4), p.868.
This generalizes the scalar argument used for the SL3 paired module.
-/

public section

namespace Representation
open BinaryOffender
variable {G F V : Type*} [Group G] [Field F] [Finite F]
  [AddCommGroup V] [Module (ZMod 2) V] [Module F V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite F] in
theorem quadratic_same_twist_eq
    (A : Subgroup G) (hq : IsQuadratic ρ A) (hfaith : Function.Injective ρ)
    {a b d : G} (ha : a ∈ A) (hb : b ∈ A) (hd : d ∈ A)
    {σ τ : F ≃+* F} (hσ : σ ≠ RingEquiv.refl F)
    (hase : ∀ c v, ρ a (c • v) = σ c • ρ a v)
    (hbse : ∀ c v, ρ b (c • v) = τ c • ρ b v)
    (hdse : ∀ c v, ρ d (c • v) = τ c • ρ d v) : b = d := by
  obtain ⟨c,hc⟩ : ∃ c : F, σ c ≠ c := by
    by_contra! h
    exact hσ (RingEquiv.ext h)
  have hfix (v : V) : ρ a (ρ b v - ρ d v) = ρ b v - ρ d v := by
    have he : ρ b v - ρ d v = (ρ b v - v) - (ρ d v - v) := by abel
    rw [he,map_sub,hq a ha b hb v,hq a ha d hd v]
  apply hfaith
  apply LinearMap.ext
  intro v
  have h := hfix ((τ.symm c) • v)
  rw [hbse,hdse,τ.apply_symm_apply,← smul_sub,hase,hfix] at h
  have hz : (σ c-c) • (ρ b v-ρ d v) = 0 := by rw [sub_smul,h,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc))

theorem quadratic_card_le_ringAut_of_nontrivial_twist
    (A : Subgroup G) (hq : IsQuadratic ρ A) (hfaith : Function.Injective ρ)
    (hsemi : ∀ a ∈ A, ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v)
    {a : G} (ha : a ∈ A) {σ : F ≃+* F} (hσ : σ ≠ RingEquiv.refl F)
    (hase : ∀ c v, ρ a (c • v) = σ c • ρ a v) :
    Nat.card A ≤ Nat.card (F ≃+* F) := by
  classical
  let : Finite (F ≃+* F) :=
    Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  choose key hk using fun b : A => hsemi b b.property
  have hi : Function.Injective key := by
    intro b d he
    apply Subtype.ext
    apply quadratic_same_twist_eq ρ A hq hfaith ha b.property d.property hσ hase (hk b)
    rw [he]
    exact hk d
  exact Nat.card_le_card_of_injective key hi

theorem quadratic_card_le_two_of_nontrivial_four_twist
    (hF : Nat.card F = 4) (A : Subgroup G) (hq : IsQuadratic ρ A)
    (hfaith : Function.Injective ρ)
    (hsemi : ∀ a ∈ A, ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v)
    {a : G} (ha : a ∈ A) {σ : F ≃+* F} (hσ : σ ≠ RingEquiv.refl F)
    (hase : ∀ c v, ρ a (c • v) = σ c • ρ a v) : Nat.card A ≤ 2 := by
  have h := quadratic_card_le_ringAut_of_nontrivial_twist ρ A hq hfaith hsemi ha hσ hase
  rwa [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
    (show Nat.card F = 2^2 by simpa using hF)] at h

end Representation
