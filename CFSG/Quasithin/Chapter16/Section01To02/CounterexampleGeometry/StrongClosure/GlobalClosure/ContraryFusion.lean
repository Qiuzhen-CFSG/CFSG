module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.Disjoint
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.CentralQuotient
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionBounds
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionOrder
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction

/-!
# Involution transporters from local control

An outside transporter of a factor involution is impossible. The disjoint
case follows from the unique-conjugate assertion for a four-subgroup. In the
intersecting case, the two-group and twist calculations force the intersection
to have order two. The diagonal construction then supplies a central involution
whose actual quotient contradicts minimality, with every quotient hypothesis
and induction alternative discharged in `CentralQuotient`.

The assembly handles involutions in either factor and takes only the explicit
`LocalControl` contract in addition to the minimal counterexample. The global
closure owner must construct that contract; applying
`Hypotheses.closed_of_involution_transporters` then gives source (e).

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the contrary-fusion argument preceding (e).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
open Subgroup
universe u

/-- Both source branches close once the intersecting geometry constructs its
actual central diagonal. -/
theorem MinimalCounterexample.involution_transporters_of_centralDiagonal
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    (geometry : ∀ a ∈ (A₁ : Set G) ∪ A₂, orderOf a = 2 →
      ∀ g : G, g ∉ intersectionGenerated A₁ A₂ → g⁻¹ * a * g ∈ S →
        A₁ ⊓ A₂ ≠ ⊥ → CentralDiagonal A₁ A₂ (g⁻¹ * a * g)) :
    ∀ a ∈ (A₁ : Set G) ∪ A₂, orderOf a = 2 →
      ∀ g : G, g⁻¹ * a * g ∈ S → g ∈ intersectionGenerated A₁ A₂ := by
  intro a ha ha2 g ht
  by_contra hg
  by_cases hd : A₁ ⊓ A₂ = ⊥
  · exact hg (l.involution_transporters_of_disjoint m.setup hd ha ha2 ht)
  · exact m.not_centralDiagonal l ht (geometry a ha ha2 g hg ht hd)

/-- Local control rules out an outside transporter taking an involution of
either factor into the Sylow subgroup. The intersecting-case construction and
central-quotient induction discharge the contrary configuration on p.95. -/
theorem MinimalCounterexample.involution_transporters_of_localControl
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂) :
    ∀ a ∈ (A₁ : Set G) ∪ A₂, orderOf a = 2 →
      ∀ g : G, g⁻¹ * a * g ∈ S → g ∈ intersectionGenerated A₁ A₂ := by
  apply m.involution_transporters_of_centralDiagonal l
  intro a ha ha2 g hg ht hcap
  exact m.centralDiagonal_of_intersection_card_two l ha ha2 hg ht
    (m.intersection_card_two_of_contrary l ha ha2 hg ht hcap)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
