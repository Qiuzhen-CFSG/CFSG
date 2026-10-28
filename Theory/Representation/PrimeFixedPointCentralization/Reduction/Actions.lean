module

public import Theory.Representation.PrimeFixedPointCentralization.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Invariant subgroup and image reductions for prime actions

Restriction to an invariant subgroup preserves the semidirect-product embedding.
Minimality descends along an equivariant surjection, by taking preimages of
proper invariant subgroups. These are the finite-minimality transports in
Aschbacher, *Finite Group Theory*, second edition, 36.2, printed p.194.
-/

namespace Representation.PrimeFixedPointCentralization

variable {P A : Type*} [Group P] [Group A]

/-- The literal restricted action on an invariant subgroup. -/
@[expose] public def invariantSubgroupAction (φ : A →* MulAut P) (Q : Subgroup P)
    (hQ : ∀ a : A, ∀ z ∈ Q, φ a z ∈ Q) : A →* MulAut Q where
  toFun a :=
    { toFun := fun z => ⟨φ a z, hQ a z z.property⟩
      invFun := fun z => ⟨φ a⁻¹ z, hQ a⁻¹ z z.property⟩
      left_inv := by intro z; ext; simp
      right_inv := by intro z; ext; simp
      map_mul' := by intro x y; ext; exact map_mul (φ a) (x : P) (y : P) }
  map_one' := by ext z; simp
  map_mul' := by intro a b; ext z; simp

/-- The restriction embeds its semidirect product in the original one. -/
@[expose] public def invariantSubgroupInclusion (φ : A →* MulAut P) (Q : Subgroup P)
    (hQ : ∀ a : A, ∀ z ∈ Q, φ a z ∈ Q) :
    SemidirectProduct Q A (invariantSubgroupAction φ Q hQ) →*
      SemidirectProduct P A φ :=
  SemidirectProduct.map Q.subtype (MonoidHom.id A) (by intro a; rfl)

public theorem invariantSubgroupInclusion_injective (φ : A →* MulAut P)
    (Q : Subgroup P) (hQ : ∀ a : A, ∀ z ∈ Q, φ a z ∈ Q) :
    Function.Injective (invariantSubgroupInclusion φ Q hQ) := by
  intro x y h
  apply SemidirectProduct.ext
  · exact Subtype.ext (congrArg SemidirectProduct.left h)
  · exact congrArg (fun t : SemidirectProduct P A φ => t.right) h

/-- A nontrivial action of a prime-order group is faithful. -/
public theorem prime_action_injective_of_moving
    {r : ℕ} [Fact r.Prime] [Finite A] (hA : Nat.card A = r)
    (φ : A →* MulAut P) (hmoving : ∃ a z, φ a z ≠ z) : Function.Injective φ := by
  apply φ.ker_eq_bot_iff.mp
  let : Fact (Nat.card A).Prime := ⟨hA ▸ (Fact.out : r.Prime)⟩
  rcases φ.ker.eq_bot_or_eq_top_of_prime_card with h | h
  · exact h
  · obtain ⟨a, z, hz⟩ := hmoving
    have ha : φ a = 1 := by
      have : a ∈ φ.ker := h.symm ▸ Subgroup.mem_top a
      exact this
    exact (hz (by rw [ha]; rfl)).elim

/-- Minimality survives a surjective equivariant image. -/
public theorem IsMinimalAction.of_surjective {Q : Type*} [Group Q]
    {φ : A →* MulAut P} {ψ : A →* MulAut Q} (hmin : IsMinimalAction φ)
    (f : P →* Q) (hf : Function.Surjective f)
    (hequiv : ∀ a z, f (φ a z) = ψ a (f z)) : IsMinimalAction ψ := by
  intro R hR hproper a z hz
  obtain ⟨x, rfl⟩ := hf z
  have hinv : ∀ b : A, ∀ y ∈ R.comap f, φ b y ∈ R.comap f := by
    intro b y hy
    change f (φ b y) ∈ R
    rw [hequiv]
    exact hR b (f y) hy
  have hne : R.comap f ≠ ⊤ := by
    intro htop
    apply hproper
    apply Subgroup.comap_injective hf
    simpa using htop
  rw [← hequiv, hmin (R.comap f) hinv hne a x hz]

end Representation.PrimeFixedPointCentralization
