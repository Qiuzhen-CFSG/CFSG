module

public import Theory.GroupAction.ComponentRankAction.PrimeResidual
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal

/-!
# The original component and the residual of its ambient group

Full p-rank and p-prime center make the original component normal and its
actual conjugation kernel p-prime. If the concrete model's p-elements in this
same rank-two action image are inner, both the prime-generated closure and
the prime-to-p residual equal the original component. This is the transport
step for the non-cubic linear and the symplectic branches of A.3.18. The
model field-action theorem supplies the final inner-action hypothesis.

Source: Aschbacher–Smith, A.3.18, printed pp.51–53; 2.5.7, p.556.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupAction.ComponentRankAction
variable {G S : Type*} [Group G] [Group S]

/-- The same marked component action, extended over its whole ambient group
when the component is normal. -/
def normalAction (L : Subgroup G) [L.Normal] (e : L ⧸ center L ≃* S) :
    G →* MulAut S :=
  (action L e).comp ((MonoidHom.id G).codRestrict (normalizer (L : Set G))
    (fun x => by rw [L.normalizer_eq_top]; trivial))

/-- The ambient action kernel is exactly the original centralizer. -/
theorem normalAction_ker (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* S) :
    (normalAction L e).ker = centralizer (L : Set G) := by
  ext x
  change (⟨x, by rw [L.normalizer_eq_top]; trivial⟩ : normalizer (L : Set G)) ∈
    (action L e).ker ↔ x ∈ centralizer (L : Set G)
  rw [ker_eq]
  rfl

/-- The literal component has precisely the inner image, with its original marking. -/
theorem normalAction_component_image (L : Subgroup G) [L.Normal]
    (e : L ⧸ center L ≃* S) :
    L.map (normalAction L e) = MulAut.innerSubgroup S := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨e (QuotientGroup.mk' (center L) ⟨x, hx⟩),
      (action_on_component L e ⟨x, hx⟩).symm⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center L))) y
    exact ⟨x, x.property, action_on_component L e x⟩

variable [Finite G] {p : ℕ} [Fact p.Prime]

/-- The actual model action implication completes both residual and prime-closure
identifications. No normality or kernel premise is retained. -/
theorem component_eq_primeClosure_and_residual
    {L : Subgroup G} (hL : IsComponent G L)
    (hz : Nat.Coprime p (Nat.card (center L)))
    (hr : 2 ≤ primeRank p L) (hG : primeRank p G ≤ 2)
    (e : L ⧸ center L ≃* S)
    (hi : ∀ a ∈ (action L e).range, ∀ m : ℕ,
      a ^ (p ^ m) = 1 → a ∈ MulAut.innerSubgroup S) :
    L = closure {x : G | orderOf x = p} ∧ L = primeToResidual p G := by
  let := hL.2
  let : L.Normal := hL.normal_of_coprime_center_primeRank p hz (by omega)
  let f := normalAction L e
  have hk : Nat.Coprime p (Nat.card f.ker) := by
    rw [normalAction_ker]
    exact centralizer_coprime L hz hr hG
  have hd : p ∣ Nat.card L := by
    by_contra hh
    have hh' := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
    omega
  have hact (x : G) (m : ℕ) (hx : x ^ (p ^ m) = 1) : f x ∈ L.map f := by
    rw [normalAction_component_image]
    apply hi (f x)
      ⟨⟨x, by rw [L.normalizer_eq_top]; trivial⟩, rfl⟩ m
    rw [← map_pow, hx, map_one]
  have hres : primeToResidual p G = L :=
    primeToResidual_eq_component_of_primePower_action f hk L hz hd hact
  refine ⟨?_, hres.symm⟩
  apply le_antisymm (component_le_prime_closure L hz hd)
  rw [← hres]
  apply (closure_le _).mpr
  intro x hx
  change orderOf x = p at hx
  apply mem_primeToResidual_of_pow (n := 1)
  simpa only [pow_one, ← hx] using pow_orderOf_eq_one x

end Theory.GroupAction.ComponentRankAction
