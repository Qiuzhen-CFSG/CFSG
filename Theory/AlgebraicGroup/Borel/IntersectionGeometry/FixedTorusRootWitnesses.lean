module

public import Theory.AlgebraicGroup.Borel.RootSupport
public import Theory.AlgebraicGroup.Borel.SolvableRootContainment
public import Theory.AlgebraicGroup.RootSubgroups.PositiveSystemOpposition

universe u

/-!
Construction of compatible Borel witnesses from fixed-torus root geometry.

The remaining geometric inputs are explicit: a realized complete root datum,
positivity and radical generation for Borel root supports, and solvability of
positive-root-generated subgroups. Solvable containment places each positive
system in a Borel; inclusion between positive systems then identifies its
support. The radical and torus decomposition construct the full witness.
Opposition is obtained by negating roots, using complete addition.

This conditional assembly is not an unconditional proof of GLS3, Theorem
1.11.2. The three inputs must be constructed from reductivity and maximality
of the ambient torus before the fixed-torus source theorem is complete.
Sources: `refs/KGroup/GLS3/Chapter1.tex`, §§1.9–1.11, and
`refs/KGroup/Bor1/Chapter4.tex`, §§13.18, 14.1, 14.4–14.5.
-/

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- Once the three root-geometric inputs are proved, construct witnesses for
the specified Borel, all Borels over the same torus, and the opposite system.
The hypotheses do not assume Borel witnesses or opposite geometry. -/
public theorem fixedTorusRootWitnesses_of_root_geometry
    (D : RootGroupData G T) (hD : D.IsRealization)
    (hadd : D.IsRootAdditionComplete)
    {B : ClosedSubgroup G} (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hsupport : ∀ C : ClosedSubgroup G, IsBorelSubgroup C → T ≤ C →
      IsPositiveSystem D (D.borelRootSupport C))
    (hspan : ∀ C : ClosedSubgroup G, IsBorelSubgroup C → T ≤ C →
      ∀ U : ClosedSubgroup G, IsUnipotentRadicalOf C U →
        U.toSubgroup ≤ RootSubgroupGenerated D (D.borelRootSupport C))
    (hsolvable : ∀ P : Set D.Root, IsPositiveSystem D P →
      Group.IsSolvable (RootSubgroupGenerated D P)) :
    ∃ P : Set D.Root,
      IsPositiveSystem D P ∧ Nonempty (IsBorelOfPositiveSystem D P B) ∧
      (∀ C : ClosedSubgroup G, IsBorelSubgroup C → T ≤ C →
        ∃ Q : Set D.Root,
          IsPositiveSystem D Q ∧ Nonempty (IsBorelOfPositiveSystem D Q C)) ∧
      ∃ C : ClosedSubgroup G,
        IsPositiveSystem D (D.neg ⁻¹' P) ∧
          Nonempty (IsBorelOfPositiveSystem D (D.neg ⁻¹' P) C) := by
  have hback (C : ClosedSubgroup G) (hC : IsBorelSubgroup C) (hTC : T ≤ C) :
      Nonempty (IsBorelOfPositiveSystem D (D.borelRootSupport C) C) := by
    obtain ⟨U, hU, _⟩ :=
      exists_unipotentRadical_of_connected_solvable C hC.connected hC.solvable
    exact D.borelWitness_of_radical_le_rootGenerated hD hC hT hTC hU
      (hspan C hC hTC U hU)
  have hforward (P : Set D.Root) (hP : IsPositiveSystem D P) :
      ∃ C : ClosedSubgroup G, Nonempty (IsBorelOfPositiveSystem D P C) := by
    obtain ⟨C, hC, hTC, hPC⟩ :=
      exists_borelSubgroup_containing_solvable_roots D hD hT.1 P (hsolvable P hP)
    have hsubset : P ⊆ D.borelRootSupport C := by
      intro a ha
      exact fun _ hx => hPC (rootSubgroup_le_RootSubgroupGenerated D ha hx)
    have heq := hP.eq_of_subset (hsupport C hC hTC) hsubset
    rw [heq]
    exact ⟨C, hback C hC hTC⟩
  let P := D.borelRootSupport B
  have hP : IsPositiveSystem D P := hsupport B hB hTB
  have hneg := hP.neg_preimage hD hadd
  obtain ⟨C, hC⟩ := hforward (D.neg ⁻¹' P) hneg
  refine ⟨P, hP, hback B hB hTB, ?_, C, hneg, hC⟩
  intro C hC hTC
  exact ⟨D.borelRootSupport C, hsupport C hC hTC, hback C hC hTC⟩

end Theory.AlgebraicGroup.BorelIntersectionGeometry
