module

public import Theory.AlgebraicGroup.Borel.StandardPositiveSystemClassification.Defs
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup
public import Theory.AlgebraicGroup.Unipotent.SolvableTorusDecomposition

universe u

/-!
Root support of a Borel subgroup and construction of its radical witness.

Every root subgroup in a Borel lies in its unipotent radical, because it is
unipotent and the Borel is connected solvable. Thus the difficult direction of
root generation is just containment of the radical in the generated root
subgroup. Once that containment is proved, the solvable torus decomposition
supplies the full `IsBorelOfPositiveSystem` witness. Positivity of the support
and this reverse containment remain separate geometric assertions.

Sources: GLS3, Theorem 1.11.2; Borel, *Linear Algebraic Groups*, Theorem 10.6(4)
and §§13.18, 14.4–14.5.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- The actual root subgroups contained in the specified closed subgroup. -/
@[expose]
public def RootGroupData.borelRootSupport (D : RootGroupData G T)
    (B : ClosedSubgroup G) : Set D.Root :=
  {a | D.rootSubgroup a ≤ B}

variable [IsAlgClosed k] {D : RootGroupData G T}

/-- Roots in a Borel and roots in its unipotent radical have the same support. -/
public theorem RootGroupData.borelRootSupport_eq_radicalSupport
    (hD : D.IsRealization) {B U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U) :
    D.borelRootSupport B = D.borelRootSupport U := by
  ext a
  constructor
  · intro ha
    exact hU.contains_unipotent_closedSubgroup hB.connected hB.solvable ha
      (hD.2.2.1 a).1.2.isUnipotentAlgebraicGroup
  · intro ha
    exact fun _ hx => hU.1 (ha hx)

/-- The root-generated subgroup of a Borel's support lies in its radical. -/
public theorem RootGroupData.rootGenerated_borelRootSupport_le_radical
    (hD : D.IsRealization) {B U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hU : IsUnipotentRadicalOf B U) :
    RootSubgroupGenerated D (D.borelRootSupport B) ≤ U.toSubgroup := by
  rw [D.borelRootSupport_eq_radicalSupport hD hB hU]
  exact (RootSubgroupGenerated_le_iff D _ U.toSubgroup).mpr fun _ ha => ha

/-- Reverse root-generation containment suffices for the full Borel witness;
torus factorization is proved from the given ambient maximal torus. -/
public theorem RootGroupData.borelWitness_of_radical_le_rootGenerated
    (hD : D.IsRealization) {B U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hU : IsUnipotentRadicalOf B U)
    (hgenerate : U.toSubgroup ≤ RootSubgroupGenerated D (D.borelRootSupport B)) :
    Nonempty (IsBorelOfPositiveSystem D (D.borelRootSupport B) B) := by
  refine ⟨{
    unipotent := U
    root_generated := le_antisymm hgenerate
      (D.rootGenerated_borelRootSupport_le_radical hD hB hU)
    borel := hB
    radical := hU
    torus_unipotent_generate := ?_ }⟩
  exact (maximalTorus_unipotentRadical_decomposition_of_connected_solvable
    hB.connected hB.solvable hU hT hTB).2.1

end Theory.AlgebraicGroup
