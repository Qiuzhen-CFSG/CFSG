module
public import Theory.GroupTheory.AutomorphismSquareOuterTwo
public import Theory.Alternating.Aut

/-!
# The outer quotient of an actual normal A₅ pair

Aut(A₅)=S₅ makes the outer group a quotient of S₅/A₅, hence a two-group.
The square theorem then proves that an ambient group containing a normal
A₅×A₅ with trivial centralizer has two-group quotient by that exact image.
This is the group-theoretic closing step in the A₅ specialization of
Aschbacher--Smith D.3.21, printed p.206.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.AlternatingFive
/-- The actual outer automorphism group of A₅ is a two-group. -/
theorem outer_isPGroup_two : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 5))) := by
  let A := alternatingGroup (Fin 5)
  have htwo : IsPGroup 2 (Equiv.Perm (Fin 5) ⧸ A) := by
    apply IsPGroup.of_card (n := 1)
    rw [←A.index_eq_card,alternatingGroup.index_eq_two]
    rfl
  apply htwo.of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ,rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
      (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A σ,rfl⟩

/-- A normally embedded A₅ pair with trivial centralizer leaves a two-group
quotient, retaining the original embedding and its literal range. -/
theorem quotient_isPGroup_two_of_normal_pair
    {Q : Type*} [Group Q]
    (i : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* Q)
    (hi : Function.Injective i) [i.range.Normal]
    (hc : centralizer (i.range : Set Q) = ⊥) : IsPGroup 2 (Q ⧸ i.range) := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  exact GroupTheory.AutomorphismSquare.quotient_isPGroup_two_of_normal_embedding i hi
    (alternatingGroup.center_eq_bot (by simp)) outer_isPGroup_two hc
end Theory.AlternatingFive
