module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionOrder.Structure
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionOrder.OutsideInvolution
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionOrder.TwistFusion

/-!
# The order-two intersection under contrary involution fusion

The extension of the nontrivial intersection by a contrary fused involution
has an actual dihedral or semidihedral model. Its involution centralizer has
order four, and the fixed subgroup in the intersection has order two.
The outside-involution argument excludes Ω₁(A₁) ≤ A₂ and supplies an
involution v in A₁ − A₂. The twist calculation with x = vvᵗ then excludes
fusion of tz into either factor and forces the entire intersection to be
the fixed subgroup ⟨z⟩. Both arguments retain the original union hypothesis.

This assembles the intersection-order conclusion with `LocalControl` as the
authorized explicit local input. Its construction and the remaining central
diagonal argument belong to the global-closure assembly.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

/-- A contrary conjugate of a factor involution forces a nontrivial factor
intersection to have order two, as in the intersecting case on printed p.95. -/
theorem MinimalCounterexample.intersection_card_two_of_contrary
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : A₁ ⊓ A₂ ≠ ⊥) : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2 := by
  obtain ⟨v, hv, hvout, hv2⟩ :=
    m.exists_left_involution_outside_right_of_contrary l ha ha2 hg ht hcap
  exact m.intersection_card_two_of_contrary_of_left_involution l ha ha2 hg ht hcap
    v hv hvout hv2

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
