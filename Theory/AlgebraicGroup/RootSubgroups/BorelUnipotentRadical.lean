module

public import Theory.AlgebraicGroup.RootSubgroups.BorelContainment
public import Theory.AlgebraicGroup.Unipotent.Radical

universe u

/-! Torus root subgroups inside Borel unipotent radicals. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A torus root subgroup contained in a Borel subgroup lies in every
unipotent radical of that Borel subgroup. -/
public lemma IsUnipotentRadicalOf.torusRootSubgroup_le
    {K : Variety k} [AlgebraicGroup K]
    {B T X U : ClosedSubgroup K}
    (hU : IsUnipotentRadicalOf B U)
    (hB : IsBorelSubgroup B)
    (hX : IsTorusRootSubgroup T X)
    (hXB : X ≤ B) : X ≤ U :=
  hU.contains_unipotent_closedSubgroup hB.connected hB.solvable hXB
    hX.2.isUnipotentAlgebraicGroup

/-- A subtorus and one of its root subgroups lie in a Borel subgroup whose
unipotent radical contains the root subgroup. -/
public theorem exists_borelSubgroup_with_unipotentRadical_containing_torusRootSubgroup
    {K : Variety k} [AlgebraicGroup K]
    (T X : ClosedSubgroup K)
    (hT : IsSubtorus T) (hX : IsTorusRootSubgroup T X) :
    ∃ B : ClosedSubgroup K,
      IsBorelSubgroup B ∧ T ≤ B ∧
        ∃ U : ClosedSubgroup K, IsUnipotentRadicalOf B U ∧ X ≤ U := by
  obtain ⟨B, hB, hTB, hXB⟩ :=
    exists_borelSubgroup_containing_torusRootSubgroup T X hT hX
  obtain ⟨U, hU, _⟩ :=
    exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
  exact ⟨B, hB, hTB, U, hU, hU.torusRootSubgroup_le hB hX hXB⟩

end Theory.AlgebraicGroup
