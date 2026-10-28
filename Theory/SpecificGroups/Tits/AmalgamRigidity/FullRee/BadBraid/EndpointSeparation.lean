module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.SourceMaps
/-!
# Separation of the two original endpoint images

The first four marked generators lie in the first image. The fifth cannot:
otherwise second-endpoint generation would force its image into the first,
contradicting the independently verified endpoint orders 12288 and 20480.
No finiteness or recognition hypothesis on the completion is used.

Source: Aschbacher–Smith F.4.4 and the binary Ree parabolics of F.4.8.
-/
@[expose] public section
noncomputable section
namespace Tits.AmalgamRigidity.FullRee.BadBraid
open ReeTwo Subgroup.CosetWordCertificate
variable {G : Type*} [Group G]

theorem first_generators_mem (c : Completion (G := G)) (j : Nat) (hj : j < 4) :
    generator c j ∈ c.left.range := by
  interval_cases j
  · exact c.middle_le_left ⟨borelEquiv SylowModel.rootOne, rfl⟩
  · exact c.middle_le_left ⟨borelEquiv (SylowModel.root 0), rfl⟩
  · exact c.middle_le_left ⟨borelEquiv (SylowModel.root 2), rfl⟩
  · exact ⟨ParabolicMarkedComparison.Verified.firstEquiv Centralizer.weyl, rfl⟩

theorem reflection_not_mem_left (c : Completion (G := G)) :
    generator c 4 ∉ c.left.range := by
  intro hr
  have ht : (⊤ : Subgroup SecondExtension.Endpoint) ≤ c.left.range.comap c.right := by
    rw [← SecondExtension.endpoint_generated]
    apply (Subgroup.closure_le _).mpr
    rintro x (rfl | ⟨y,rfl⟩)
    · exact hr
    · change c.right (SecondExtension.inclusion y) ∈ c.left.range
      rw [← middle_right]
      exact c.middle_le_left ⟨borelEquiv y,rfl⟩
  have hle : c.right.range ≤ c.left.range := by
    rintro x ⟨y,rfl⟩
    exact ht (Subgroup.mem_top y)
  have hd := Subgroup.card_dvd_of_le hle
  rw [c.right_card, c.left_card] at hd
  change Nat.card ExceptionalParabolics.FullRee.second ∣
    Nat.card ExceptionalParabolics.FullRee.first at hd
  rw [ExceptionalParabolics.FullRee.second_card,
    ExceptionalParabolics.FullRee.first_card] at hd
  norm_num at hd

theorem generator_square_root_nine (c : Completion (G := G)) :
    generator c 2 ^ 2 = middleMap c (SylowModel.root 9) := by
  change middleMap c (SylowModel.root 2) ^ 2 = _
  rw [← map_pow, (by decide +kernel : SylowModel.root 2 ^ 2 = SylowModel.root 9)]

end Tits.AmalgamRigidity.FullRee.BadBraid
