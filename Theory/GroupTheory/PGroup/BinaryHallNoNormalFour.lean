module

public import Theory.GroupTheory.PGroup.SymplecticType
public import Theory.GroupTheory.PGroup.NoNormalFourClassification
public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification

/-!
# Hall factors without normal elementary four-groups

A finite two-group without a normal elementary four-group is cyclic,
generalized quaternion, dihedral, or semidihedral. Split according to the
existence of an elementary four and use the corresponding recognition theorem.
The central-product decomposition then has trivial extraspecial factor.

Sources: GLS2, Chapter C, Lemma 10.11; Gorenstein, *Finite Groups*, Section 5.4.
-/

namespace IsPGroup

/-- In the absence of normal four-groups, the whole two-group is a Hall factor. -/
public theorem isBinaryHallFactor_of_no_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4) :
    IsBinaryHallFactor P := by
  by_cases hfour : ∃ U : Subgroup P, IsElementaryAbelian 2 U ∧ Nat.card U = 4
  · obtain ⟨U, hU, hcard⟩ := hfour
    let : IsElementaryAbelian 2 U := hU
    rcases hP.exists_dihedral_or_semidihedral_of_no_normal_four hno U hcard with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases hP.isCyclic_or_quaternion_of_no_elementary_four
      (fun U hU hc => hfour ⟨U, hU, hc⟩) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- The internal decomposition in the no-normal-four case has trivial first factor. -/
public theorem isBinarySymplecticType_of_no_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4) :
    IsBinarySymplecticType P :=
  (hP.isBinaryHallFactor_of_no_normal_four hno).isBinarySymplecticType

end IsPGroup
