module
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Two-group outer action on a normal simple square

Every automorphism of a centerless quasisimple square preserves its factors
or interchanges them. Squaring makes it factor preserving, and a common
power of two makes both factor actions inner. The resulting outer group
is therefore a two-group. The faithful outer action of a self-centralizing
normal square gives the same conclusion for its literal ambient quotient.

Source application: Aschbacher--Smith D.3.21, printed p.206. This isolates
the elementary outer-action closing step without any module assumptions.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.AutomorphismSquare
variable {S : Type*} [Group S] [Finite S] [IsQuasisimple S]

private def diagonal : (MulAut S × MulAut S) →* MulAut (S × S) where
  toFun ab := ab.1.prodCongr ab.2
  map_one' := by ext x <;> rfl
  map_mul' := by intros; rfl

/-- A square of a centerless quasisimple group still has two-group outer
automorphisms when each factor does. Squaring removes the factor exchange. -/
theorem outer_isPGroup_two (hZ : center S = ⊥)
    (houter : IsPGroup 2 (MulAut.Outer S)) :
    IsPGroup 2 (MulAut.Outer (S × S)) := by
  obtain ⟨k,hk⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp houter
  have hp (a : MulAut S) : a ^ 2 ^ k ∈ MulAut.innerSubgroup S := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (MulAut.innerSubgroup S)) (a ^ 2 ^ k) = 1
    rw [map_pow]
    exact hk _
  have hdiag (a b : MulAut S) :
      (diagonal (a,b)) ^ 2 ^ k ∈ MulAut.innerSubgroup (S × S) := by
    obtain ⟨x,hx⟩ := hp a
    obtain ⟨y,hy⟩ := hp b
    refine ⟨(x,y),?_⟩
    rw [←map_pow]
    change MulAut.conj (x,y) = (a ^ 2 ^ k).prodCongr (b ^ 2 ^ k)
    rw [←hx,←hy]
    rfl
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro z
  obtain ⟨f,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (S × S)) z
  refine ⟨k+1,?_⟩
  rw [←map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hsquare : ∃ a b : MulAut S, f ^ 2 = diagonal (a,b) := by
    rcases normal_form hZ f with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩
    · exact ⟨a*a,b*b,rfl⟩
    · exact ⟨a*b,b*a,rfl⟩
  obtain ⟨a,b,hab⟩ := hsquare
  rw [pow_succ, Nat.mul_comm, pow_mul,hab]
  exact hdiag a b

/-- The actual quotient by a normally embedded square is a two-group when
its centralizer is trivial and the factor outer group is a two-group. -/
theorem quotient_isPGroup_two_of_normal_embedding
    {Q : Type*} [Group Q]
    (i : S × S →* Q) (hi : Function.Injective i) [i.range.Normal]
    (hZ : center S = ⊥) (houter : IsPGroup 2 (MulAut.Outer S))
    (hc : centralizer (i.range : Set Q) = ⊥) : IsPGroup 2 (Q ⧸ i.range) := by
  let e : S × S ≃* i.range := MonoidHom.ofInjective hi
  have h := (outer_isPGroup_two hZ houter).of_surjective
    (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).surjective
  exact h.of_injective (MulAut.outerAction i.range) (MulAut.outerAction_injective _ hc)

end Theory.GroupTheory.AutomorphismSquare
