module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane.Intersection

/-!
# The original returning plane supplies the Asc94 type

The natural flag selects an element of L₂ that moves V₁ while preserving
V₂. The quaternion cores meet exactly in that plane. Substitution in the
actual Asc94 constructor therefore gives IsType for the original line
involution, with no selected conjugator, fusion, or intersection premise.

The nine-clause source theorem13.5.15 remains an explicit input, and the
ordinary natural setup remains the earlier13.2.1/13.3.3 input. This module
discharges the additional returning-plane step of13.5.16, not those two
source obligations or the subsequent45.11 recognition theorem.

Source: Aschbacher–Smith,13.5.16, printed p.921.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch
open Theory.GroupTheory.Recognition
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

include d

/-- The source plane and its returning element are constructed inside the
original L₂. Their core intersection is an output, not a source premise. -/
theorem ReturningPlane.exists_returning_plane (h : D.Hypothesis)
    (b : Conclusions D M 6 g) (hM : M = D.L) :
    ∃ y : G, y ∈ Section08.TransvectionParabolic.EarlierCore.localResidual D.L V₂ ∧
      y ∈ normalizer (V₂ : Set G) ∧ y ∉ D.H ∧
      D.UH ⊓ UnitaryFourThree.conjugate D.UH y = V₂ := by
  obtain ⟨a,ha,_,y,hy,hyr,hyP,hyG⟩ := ReturningPlane.exists_original_returning d h
  exact ⟨y.val,hy,hyP,(by simpa only [b.six.1] using hyG),
    ReturningPlane.original_core_intersection d h b hM a ha y hyr hyP hyG⟩

/-- Literal Chapter13 consumer: the natural normal branch now supplies every
field of the actual Asc94 type, including the universal core intersection. -/
theorem TypeU4.isType_of_natural_normal_branch (h : D.Hypothesis)
    (b : Conclusions D M 6 g) (hM : M = D.L)
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1) : UnitaryFourThree.IsType z := by
  obtain ⟨y,_,hy,hyH,hpair⟩ := ReturningPlane.exists_returning_plane d h b hM
  exact TypeU4.isType_of_returning_plane h b hM z hz hz1 V₂
    d.line_le_plane d.plane_le_seed d.plane_card y hy hyH hpair

end CFSG.Quasithin.Chapter13.Section05.NormalBranch
end
