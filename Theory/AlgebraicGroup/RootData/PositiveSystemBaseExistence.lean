module

public import Theory.AlgebraicGroup.RootData.PositiveSystemBase
public import Theory.AlgebraicGroup.RootSystems.Weyl

/-!
An abstract positive subsystem of a finite reduced crystallographic root
pairing is the positive subsystem of some base.  For a root-group datum whose
addition, reflection, negation, and height data are realized by the pairing,
we transport a chosen positive system along the root-index equivalence to such
a subsystem.  The surjectivity theorem for `Base.toPositiveSubsystem` then
provides the aligned base; the final equivalence is just transport along the
given equivalence.  This avoids assuming an alignment premise and is the
interface used by later realized-root and unipotent-product constructions.
-/

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k]

/-- Every positive system realized by a root-group datum is the positivity set
of an abstract root-system base after transporting indices along `e`. -/
public theorem exists_base_isPos_iff_of_positiveSystem
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) {positiveRoots : Set D.Root}
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hPositive : IsPositiveSystem D positiveRoots)
    (hActual : IsRootSystemRealization D P e base)
    (hAdd : IsRootAdditionRealization D P e) :
    ∃ positiveBase : P.Base,
      ∀ alpha, alpha ∈ positiveRoots ↔ positiveBase.IsPos (e alpha) := by
  let S : P.PositiveSubsystem :=
    { carrier := {i | e.symm i ∈ positiveRoots}
      add_mem := by
        intro i j gamma hi hj hroot
        apply hPositive.2.2 (e.symm i) hi (e.symm j) hj (e.symm gamma)
        apply (hAdd (e.symm i) (e.symm j) (e.symm gamma)).mpr
        simpa using hroot
      mem_xor_neg := by
        intro i
        let alpha := e.symm i
        have hnegIndex :
            e.symm (P.reflectionPerm i i) = D.neg alpha := by
          apply e.injective
          rw [e.apply_symm_apply]
          simpa [alpha] using (hActual.2.2.1 alpha).symm
        change Xor (alpha ∈ positiveRoots)
          (e.symm (P.reflectionPerm i i) ∈ positiveRoots)
        rw [hnegIndex]
        have hcover : alpha ∈ positiveRoots ∨ D.neg alpha ∈ positiveRoots := by
          have hmem : alpha ∈ positiveRoots ∪ D.neg ⁻¹' positiveRoots := by
            rw [hPositive.2.1]
            exact Set.mem_univ alpha
          simpa only [Set.mem_union, Set.mem_preimage] using hmem
        have hdisjoint :
            ¬(alpha ∈ positiveRoots ∧ D.neg alpha ∈ positiveRoots) := by
          intro hboth
          have hmem : alpha ∈ positiveRoots ∩ D.neg ⁻¹' positiveRoots :=
            ⟨hboth.1, hboth.2⟩
          rw [hPositive.1] at hmem
          exact hmem
        rcases hcover with hpos | hneg
        · exact Or.inl ⟨hpos, fun h => hdisjoint ⟨hpos, h⟩⟩
        · exact Or.inr ⟨hneg, fun h => hdisjoint ⟨h, hneg⟩⟩ }
  obtain ⟨positiveBase, hbase⟩ := base_toPositiveSubsystem_surjective P S
  refine ⟨positiveBase, ?_⟩
  intro alpha
  calc
    alpha ∈ positiveRoots ↔ e.symm (e alpha) ∈ positiveRoots := by simp
    _ ↔ e alpha ∈ S := by rfl
    _ ↔ e alpha ∈ positiveBase.toPositiveSubsystem := by rw [hbase]
    _ ↔ positiveBase.IsPos (e alpha) :=
      positiveBase.mem_toPositiveSubsystem (e alpha)

end Theory.AlgebraicGroup
