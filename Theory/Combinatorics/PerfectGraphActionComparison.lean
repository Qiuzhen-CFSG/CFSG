module

public import Theory.Combinatorics.GraphAutomorphismTransport
public import Theory.GroupTheory.PerfectHalfOrderImage
public import Theory.Combinatorics.SimpleGraph.QuadrangleTwentySeven.Source

/-!
# Comparing a perfect native graph action with an action of the same order

Conjugate the source action through a graph isomorphism. If the native image
is perfect and the automorphism group has order at most twice its order,
the two images agree. The resulting group isomorphism intertwines the literal
vertex actions. In particular SRG(27,10,1,5) uniqueness and its 51840 bound
recognize every faithful action of order 25920 against a perfect native model.
-/

@[expose] public noncomputable section
namespace Theory.Combinatorics.PerfectGraphActionComparison
variable {V W G K : Type*} [Group G] [Group K]
variable {Γ : SimpleGraph V} {Δ : SimpleGraph W}

/-- A given graph isomorphism lifts to an isomorphism of the actual acting groups. -/
theorem equivariant_of_iso [Finite W] [Finite G] [Finite K] [Group.IsPerfect K]
    (q : Γ ≃g Δ) (ρ : G →* Equiv.Perm V) (σ : K →* Equiv.Perm W)
    (hρ : ∀ g x y, Γ.Adj (ρ g x) (ρ g y) ↔ Γ.Adj x y)
    (hσ : ∀ k x y, Δ.Adj (σ k x) (σ k y) ↔ Δ.Adj x y)
    (hiρ : Function.Injective ρ) (hiσ : Function.Injective σ)
    (hc : Nat.card G = Nat.card K) (hb : Nat.card (Δ ≃g Δ) ≤ 2 * Nat.card K) :
    ∃ e : G ≃* K, ∀ g x, σ (e g) (q x) = q (ρ g x) := by
  have : Finite (Δ ≃g Δ) := Finite.of_injective (fun a : Δ ≃g Δ => a.toEquiv)
    (fun a b h => by ext x; exact Equiv.congr_fun h x)
  let f := (graphAutomorphismEquiv q).toMonoidHom.comp (graphActionHom ρ hρ)
  let k := graphActionHom σ hσ
  have hf : Function.Injective f :=
    (graphAutomorphismEquiv q).injective.comp (graphActionHom_injective ρ hρ hiρ)
  have hk : Function.Injective k := graphActionHom_injective σ hσ hiσ
  have he := GroupTheory.PerfectHalfOrderImage.range_eq f k hf hk hc hb
  refine ⟨GroupTheory.PerfectHalfOrderImage.equivOfRangeEq f k hf hk he, ?_⟩
  intro g x
  have hh := congrArg (fun a : Δ ≃g Δ => a (q x))
    (GroupTheory.PerfectHalfOrderImage.equivOfRangeEq_apply f k hf hk he g)
  change σ (GroupTheory.PerfectHalfOrderImage.equivOfRangeEq f k hf hk he g) (q x) =
    q (ρ g (q.symm (q x))) at hh
  simpa only [RelIso.symm_apply_apply] using hh

/-- The 27-point quadrangle comparison, retaining its source and model vertex maps. -/
theorem equivariant_of_srg [Fintype V] [Fintype W] [Finite G] [Finite K]
    [DecidableRel Γ.Adj] [DecidableRel Δ.Adj] [Group.IsPerfect K]
    (hΓ : Γ.IsSRGWith 27 10 1 5) (hΔ : Δ.IsSRGWith 27 10 1 5)
    (ρ : G →* Equiv.Perm V) (σ : K →* Equiv.Perm W)
    (hρ : ∀ g x y, Γ.Adj (ρ g x) (ρ g y) ↔ Γ.Adj x y)
    (hσ : ∀ k x y, Δ.Adj (σ k x) (σ k y) ↔ Δ.Adj x y)
    (hiρ : Function.Injective ρ) (hiσ : Function.Injective σ)
    (hcG : Nat.card G = 25920) (hcK : Nat.card K = 25920) :
    ∃ (q : Γ ≃g Δ) (e : G ≃* K), ∀ g x, σ (e g) (q x) = q (ρ g x) := by
  obtain ⟨⟨a⟩, _⟩ := QuadrangleTwentySeven.source_recognition Γ hΓ
  obtain ⟨⟨b⟩, hb⟩ := QuadrangleTwentySeven.source_recognition Δ hΔ
  let q := a.symm.trans b
  have hbound : Nat.card (Δ ≃g Δ) ≤ 2 * Nat.card K := by rw [hcK]; exact hb
  obtain ⟨e, he⟩ := equivariant_of_iso q ρ σ hρ hσ hiρ hiσ (hcG.trans hcK.symm) hbound
  exact ⟨q, e, he⟩

end Theory.Combinatorics.PerfectGraphActionComparison
