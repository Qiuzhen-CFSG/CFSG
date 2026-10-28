module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Basic
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.MatrixGeneration
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection

/-!
# The canonical Sp₆(2) universal kernel has order at most two

Evaluate the two free generators at preimages in the canonical universal
cover. Each source relator evaluates into its central kernel, so this map
factors through F/[F,R]. If the presentation is faithful, an element mapping
into the canonical kernel already lies above the identity in F/R. Perfectness
allows its preimage to be chosen in the derived subgroup. Thus a two-element
collection result there gives the required upper bound on the actual kernel.

The checked coset certificates prove presentation faithfulness, and the checked
central word identities prove the required collection result. The final theorem
`kernel_card_le_two` discharges both premises of the retained conditional
reduction and bounds the kernel of the canonical projection to the literal
symplectic matrix group.
Source: Aschbacher–Smith I.1.1, printed p.407, and the ATLAS presentation cited
in `KernelUpperBound.Presentation`.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover

open KernelPresentation

noncomputable def coverGenerator (i : Bool) : CoverGroup :=
  Classical.choose (projection_surjective (matrixGenerator i))

@[simp] theorem projection_coverGenerator (i : Bool) :
    projection (coverGenerator i) = matrixGenerator i :=
  Classical.choose_spec (projection_surjective (matrixGenerator i))

noncomputable def coverFreeEvaluation : Free →* CoverGroup := FreeGroup.lift coverGenerator

theorem coverFreeEvaluation_fac : projection.comp coverFreeEvaluation = matrixEvaluation := by
  apply FreeGroup.ext_hom
  intro i
  simpa only [MonoidHom.comp_apply, coverFreeEvaluation, FreeGroup.lift_apply_of,
    matrixEvaluation] using projection_coverGenerator i

private theorem coverFreeEvaluation_relator_central (i : Fin 7) :
    coverFreeEvaluation (relator i) ∈ Subgroup.center CoverGroup := by
  apply projection_ker_le_center
  change projection (coverFreeEvaluation (relator i)) = 1
  rw [← MonoidHom.comp_apply, coverFreeEvaluation_fac, matrixEvaluation_relator]

/-- The presentation's free central group maps to the actual canonical cover. -/
noncomputable def coverCentralEvaluation : Central →* CoverGroup :=
  descend coverFreeEvaluation (by exact coverFreeEvaluation_relator_central)

/-- The map retains the literal matrix projection, not merely the abstract group type. -/
theorem coverCentralEvaluation_fac :
    projection.comp coverCentralEvaluation = matrixMap.comp centralProjection := by
  apply MonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective centralRelations x
  change projection (coverFreeEvaluation x) = matrixMap (toPresented x)
  rw [matrixMap_toPresented]
  exact DFunLike.congr_fun coverFreeEvaluation_fac x

theorem coverCentralEvaluation_surjective :
    Function.Surjective coverCentralEvaluation :=
  PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    projection coverCentralEvaluation
    (by rw [coverCentralEvaluation_fac]; exact matrixMap_surjective.comp centralProjection_surjective)
    projection_ker_le_center

/-- The explicit source-presentation element, mapped into the canonical kernel. -/
noncomputable def kernelDefect : projection.ker :=
  ⟨coverCentralEvaluation defect, by
    change projection (coverCentralEvaluation defect) = 1
    rw [← MonoidHom.comp_apply, coverCentralEvaluation_fac, MonoidHom.comp_apply]
    rw [show centralProjection defect = 1 from defect_mem_kernel, map_one]⟩

/-- Faithfulness and collection of the zero-exponent central relations imply the
upper bound for the canonical cover. Both substantial premises remain explicit. -/
theorem kernel_card_le_two_of_presentation
    (hi : Function.Injective matrixMap)
    (hcollect : ∀ x : Central, x ∈ commutator Central → centralProjection x = 1 →
      x = 1 ∨ x = defect) : Nat.card projection.ker ≤ 2 := by
  have hsurj := coverCentralEvaluation_surjective
  have hD : (commutator Central).map coverCentralEvaluation = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hsurj]
    exact Group.IsPerfect.commutator_eq_top
  have hall (y : projection.ker) : y = 1 ∨ y = kernelDefect := by
    have hy : y.val ∈ (commutator Central).map coverCentralEvaluation := by
      rw [hD]
      trivial
    obtain ⟨x, hxD, hxy⟩ := hy
    have hx : centralProjection x = 1 := by
      apply hi
      rw [map_one]
      have hfac := DFunLike.congr_fun coverCentralEvaluation_fac x
      change projection (coverCentralEvaluation x) = matrixMap (centralProjection x) at hfac
      rw [← hfac, hxy]
      exact y.property
    rcases hcollect x hxD hx with h | h
    · left
      apply Subtype.ext
      simpa [h] using hxy.symm
    · right
      apply Subtype.ext
      simpa only [h, kernelDefect] using hxy.symm
  let f : Bool → projection.ker := fun i => if i then kernelDefect else 1
  have hf : Function.Surjective f := by
    intro y
    rcases hall y with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  simpa using Nat.card_le_card_of_surjective f hf

/-- The canonical universal central cover of the literal Sp₆(2) matrix group
has kernel of order at most two. Presentation faithfulness and central-relation
collection are both proved, so no additional premise remains. -/
theorem kernel_card_le_two : Nat.card projection.ker ≤ 2 :=
  kernel_card_le_two_of_presentation matrixMap_injective
    CentralCollection.derived_kernel_eq_one_or_defect

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover
