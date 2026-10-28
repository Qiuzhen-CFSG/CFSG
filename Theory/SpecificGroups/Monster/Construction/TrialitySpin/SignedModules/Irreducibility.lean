module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Spin
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Irreducibility.RealExtraspecial

/-!
# Irreducibility of the real signed spin action

The real trace-duality theorem is applied to the actual 4096-dimensional
`SpinSpace`, then transported along a surjective homomorphism. The final
adapter identifies the constructed signed representation with a faithful
extraspecial quotient action and proves both its kernel and irreducibility.
The required central sign is obtained from the actual `z1` permutation.

The quotient, its extraspecial structure and order, its faithful action, and
the comparison with the signed action are explicit inputs. Constructing these
inputs belongs to the triality assembly. No irreducibility input is required.

Source: Aschbacher, *Sporadic Groups*, the irreducibility clause of Lemma 14.6
(printed pp. 62–63) and its use on the spin space in Section 27
(printed pp. 146–147).
-/

public section

namespace Sporadic.Monster.Construction.TrialitySpin

variable {Q : Type*} [Group Q] [Finite Q] [IsExtraspecial 2 Q]

/-- The extraspecial irreducibility implication on the concrete signed spin space. -/
theorem spinSpace_irreducible_of_extraspecial
    (σ : Representation ℝ Q SpinSpace) (hcard : Nat.card Q = 2 ^ 25)
    {z : Q} (hz : z ∈ Subgroup.center Q) (hz1 : z ≠ 1)
    (hσz : σ z = -(1 : Module.End ℝ SpinSpace)) : Representation.IsIrreducible σ :=
  Representation.isIrreducible_of_extraspecial_two_finrank_4096 σ hz hz1 hσz
    hcard finrank_spinSpace

/-- Transport the extraspecial action to any representation on the same spin space
identified with it by a surjective homomorphism. -/
theorem spinSpace_irreducible_of_quotient
    {G : Type*} [Group G] (ρ : Representation ℝ G SpinSpace)
    (π : G →* Q) (hπ : Function.Surjective π)
    (σ : Representation ℝ Q SpinSpace)
    (hcompare : ∀ g, σ (π g) = ρ g)
    (hcard : Nat.card Q = 2 ^ 25)
    {z : Q} (hz : z ∈ Subgroup.center Q) (hz1 : z ≠ 1)
    (hσz : σ z = -(1 : Module.End ℝ SpinSpace)) : Representation.IsIrreducible ρ := by
  have : Representation.IsIrreducible σ :=
    spinSpace_irreducible_of_extraspecial σ hcard hz hz1 hσz
  have heq : σ.comp π = ρ := MonoidHom.ext hcompare
  rw [← heq]
  exact Representation.isIrreducible_comp_of_surjective σ π hπ

/-- A faithful extraspecial quotient identified with the constructed signed action
has precisely the quotient kernel and acts irreducibly. The central involution
is the image of an element inducing the actual `z1` permutation. -/
theorem inducedSpin_extraspecial_quotient
    {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ bothAxesDomain.points ↔ ρ g a ∈ bothAxesDomain.points)
    (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
    (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a))
    (π : G →* Q) (hπ : Function.Surjective π)
    (σ : Representation ℝ Q SpinSpace) (hfaithful : Function.Injective σ)
    (hcompare : ∀ g, σ (π g) = bothAxesDomain.inducedRepresentation ρ hA hk hz g)
    (hcard : Nat.card Q = 2 ^ 25)
    (g₀ : G) (hcentral : π g₀ ∈ Subgroup.center Q) (hne : π g₀ ≠ 1)
    (hsign : ρ g₀ = z1) :
    (bothAxesDomain.inducedRepresentation ρ hA hk hz).ker = π.ker ∧
      Representation.IsIrreducible (bothAxesDomain.inducedRepresentation ρ hA hk hz) := by
  constructor
  · ext g
    change bothAxesDomain.inducedRepresentation ρ hA hk hz g = 1 ↔ π g = 1
    rw [← hcompare]
    constructor
    · intro h
      apply hfaithful
      simpa using h
    · intro h
      rw [h, σ.map_one]
  · apply spinSpace_irreducible_of_quotient _ π hπ σ hcompare hcard hcentral hne
    rw [hcompare]
    apply LinearMap.ext
    intro v
    exact bothAxesDomain.inducedRepresentation_of_z1 ρ hA hk hz g₀ hsign v

end Sporadic.Monster.Construction.TrialitySpin
