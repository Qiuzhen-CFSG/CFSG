module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import Theory.Representation.NormalConstituentDisplacement.FixedLine

/-!
# Selecting the minimal normal actor in 15.3.58

Minimal normality is relative to the actual actor quotient `H/O₂(H)`.
Finite subgroup minimality selects a nontrivial normal subgroup; faithfulness
and irreducibility make the sum of its literal displacement ranges all of
`U/Z`. The solvable-case exclusions and the direct-product bound are later
steps and are not premises of these results.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1149.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
variable {G : Type*} [Group G]

/-- Minimality is among nontrivial normal subgroups of the indicated actor,
not among subgroups normal in the original ambient simple group. -/
def IsMinimalNormal (K : Subgroup G) : Prop :=
  K.Normal ∧ K ≠ ⊥ ∧
    ∀ L : Subgroup G, L.Normal → L ≤ K → L = ⊥ ∨ L = K

/-- Finite nontrivial groups have a minimal nontrivial normal subgroup. -/
theorem exists_minimalNormal [Finite G] [Nontrivial G] :
    ∃ K : Subgroup G, IsMinimalNormal K := by
  obtain ⟨K, hK, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) ⟨⊤, inferInstance, top_ne_bot⟩
  refine ⟨K, hK.1, hK.2, ?_⟩
  intro L hL hLK
  by_cases hb : L = ⊥
  · exact Or.inl hb
  · exact Or.inr (le_antisymm hLK (hmin ⟨hL, hb⟩ hLK))

section Actor
open scoped IsMulCommutative
variable [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- The minimal normal subgroup in the opening of 15.3.58, with the full
commutator-generation conclusion for the literal quotient action. -/
theorem exists_minimalNormal_actor
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hρ : (actorRepresentation Z ZS hkernel).IsIrreducible)
    (v : ActorQuotient Z)
    (hrank : Module.finrank (ZMod 2)
      (LinearMap.range (actorRepresentation Z ZS hkernel v - LinearMap.id)) = 2) :
    ∃ K : Subgroup (ActorQuotient Z), IsMinimalNormal K ∧
      (⨆ a : K, LinearMap.range (actorRepresentation Z ZS hkernel a - LinearMap.id)) = ⊤ := by
  have hv : v ≠ 1 := by
    intro he
    rw [he, map_one, Module.End.one_eq_id, sub_self, LinearMap.range_zero, finrank_bot] at hrank
    omega
  let : Nontrivial (ActorQuotient Z) := ⟨⟨v, 1, hv⟩⟩
  obtain ⟨K, hK⟩ := exists_minimalNormal (G := ActorQuotient Z)
  let := hK.1
  exact ⟨K, hK, Representation.NormalConstituentDisplacement.normal_commutator_span_eq_top
    (actorRepresentation Z ZS hkernel) hρ (actorRepresentation_injective Z ZS hkernel) K hK.2.1⟩
end Actor

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
