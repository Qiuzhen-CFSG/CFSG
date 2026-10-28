module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.Construction
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.BlockKernel
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.UnitaryGeometry
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.UnitaryCandidates

/-!
# Comparing the central permutation quotient with the literal unitary model

The original degree-756 group modulo its displayed central E₉ is now identified
unconditionally with its generated action on 252 central blocks. The proof uses
two connected graphs to exhaust the action kernel; it does not recognize a group
by order or by its ATLAS label.

The remaining geometric comparison is assembled here from two independent
inputs with fixed coordinates: a faithful projective exterior action of the
literal PSU₄(3), and two actual generating SU matrices whose exterior actions
match the block permutations after one point relabeling. The theorem below is
conditional until those witnesses are constructed. In particular this module
does not yet discharge the PSU₄(3) identification required by I.1.4(5).

Source: Aschbacher–Smith I.1.4(5), printed p.408 (PDF p.419), GLS3 Tables 6.1.3
and 6.2.2, and the exterior-square construction in GLS3 §2.7. Numerical ATLAS
provenance is retained in `ThreeCover/source/` and replayed in the new descendant
`ProjectiveComparison/source/replay.py`.
-/

public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryGeometry

/-- A faithful exterior action and a checked generating pair complete the actual
quotient identification. Both extra inputs must be discharged by their producers. -/
noncomputable def modelEquivOfExteriorGenerators
    (ρ : UnitaryFourThree.Carrier 4 →* Equiv.Perm Index)
    (hρ : Function.Injective ρ) (hgeom : RealizesExterior ρ)
    (C : GeneratorComparison) : Projective ≃* UnitaryFourThree.Carrier 4 := by
  let τ : UnitaryFourThree.Carrier 4 →* Equiv.Perm BlockAction.Block :=
    (MulAut.conj C.labeling.symm).toMonoidHom.comp ρ
  have hτ : Function.Injective τ :=
    (MulAut.conj C.labeling.symm).injective.comp hρ
  have hfirst : τ (UnitaryFourThree.project 4 C.first) = BlockAction.blockA := by
    apply Equiv.ext
    intro i
    change C.labeling.symm (ρ (UnitaryFourThree.project 4 C.first) (C.labeling i)) = _
    have h := point_eq_of_sign_choices (hgeom C.first (C.labeling i)) (C.first_action i)
    rw [h, C.labeling.symm_apply_apply]
  have hsecond : τ (UnitaryFourThree.project 4 C.second) = BlockAction.blockB := by
    apply Equiv.ext
    intro i
    change C.labeling.symm (ρ (UnitaryFourThree.project 4 C.second) (C.labeling i)) = _
    have h := point_eq_of_sign_choices (hgeom C.second (C.labeling i)) (C.second_action i)
    rw [h, C.labeling.symm_apply_apply]
  have hrange : τ.range = BlockAction.blockGenerated := by
    rw [MonoidHom.range_eq_map, ← C.generates, MonoidHom.map_closure,
      Set.image_insert_eq, Set.image_singleton, hfirst, hsecond]
    rfl
  let e : UnitaryFourThree.Carrier 4 ≃* BlockAction.Model :=
    (MulEquiv.ofBijective τ.rangeRestrict
      ⟨fun _ _ h => hτ (congrArg Subtype.val h), τ.rangeRestrict_surjective⟩).trans
      (MulEquiv.subgroupCongr hrange)
  exact BlockAction.quotientEquiv.trans e.symm

/-- The saved pair already satisfies all numerical and unitary clauses.
Its projective generation and the faithful exterior action are the two remaining
inputs, kept explicit until the independent producers establish them. -/
noncomputable def modelEquivOfCandidateGeneration
    (ρ : UnitaryFourThree.Carrier 4 →* Equiv.Perm Index)
    (hρ : Function.Injective ρ) (hgeom : RealizesExterior ρ)
    (hgen : Subgroup.closure ({UnitaryFourThree.project 4 UnitaryCandidates.first,
      UnitaryFourThree.project 4 UnitaryCandidates.second} :
        Set (UnitaryFourThree.Carrier 4)) = ⊤) :
    Projective ≃* UnitaryFourThree.Carrier 4 :=
  modelEquivOfExteriorGenerators ρ hρ hgeom (UnitaryCandidates.comparisonOfGeneration hgen)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover
