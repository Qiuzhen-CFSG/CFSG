module

public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteLinear

/-!
# The central involutions of the two actual first parabolics

The marked derived vector is the last root. Its centrality and order two
in the coordinate local group pass through the verified full-Ree comparison
and its restriction to the mixed character kernel for the Tits parabolic.
These facts allow an arbitrary parabolic isomorphism to recover the source
marking intrinsically, without an additional compatibility assumption.

Source: Aschbacher--Smith 14.2.21, printed p.989, and the verified root
comparisons of Aschbacher (1982), Section 3.
-/

public section
open Subgroup
namespace ReeTwo.ParabolicConcrete
open Centralizer ParabolicMarkedComparison Tits.ExceptionalParabolics

private theorem center_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) {z : A} (hz : z ∈ center A) : e z ∈ center B := by
  apply mem_center_iff.mpr
  intro b
  obtain ⟨a,rfl⟩ := e.surjective b
  simpa only [map_mul] using congrArg e (mem_center_iff.mp hz a)

theorem ree_marked_central_involution :
    reeDerivedEmbedding (Multiplicative.ofAdd markedVector) ∈ center FullRee.first ∧
      orderOf (reeDerivedEmbedding (Multiplicative.ofAdd markedVector)) = 2 := by
  change Verified.firstEquiv (root 9) ∈ center FullRee.first ∧
    orderOf (Verified.firstEquiv (root 9)) = 2
  exact ⟨center_map_equiv _ root_twelve_central,
    (Verified.firstEquiv.orderOf_eq _).trans root_twelve_order⟩

theorem tits_marked_central_involution :
    titsDerivedEmbedding (Multiplicative.ofAdd markedVector) ∈
        center Tits.ExceptionalParabolics.first ∧
      orderOf (titsDerivedEmbedding (Multiplicative.ofAdd markedVector)) = 2 := by
  let z := mixedDerivedEmbedding (Multiplicative.ofAdd markedVector)
  have hz : z ∈ center Centralizer.IndexTwo.mixedLocal := by
    apply mem_center_iff.mpr
    intro g
    apply Subtype.ext
    exact mem_center_iff.mp root_twelve_central g
  have ho : orderOf z = 2 := by
    have hh := orderOf_injective Centralizer.IndexTwo.mixedLocal.subtype
      Centralizer.IndexTwo.mixedLocal.subtype_injective z
    exact hh.symm.trans root_twelve_order
  change Verified.titsFirstEquiv z ∈ center Tits.ExceptionalParabolics.first ∧
    orderOf (Verified.titsFirstEquiv z) = 2
  exact ⟨center_map_equiv Verified.titsFirstEquiv hz,(Verified.titsFirstEquiv.orderOf_eq z).trans ho⟩

end ReeTwo.ParabolicConcrete
