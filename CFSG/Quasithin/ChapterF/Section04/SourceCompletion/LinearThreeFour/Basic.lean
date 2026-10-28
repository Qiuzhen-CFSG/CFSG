module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.PSL3.LinearThreeBorelOrder
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CoreFaithfulness
public import Theory.GroupAction.RankTwoCosetGeometry
public import Theory.GroupAction.RankTwoCosetCover.PathTransport

/-!+# The marked PSL₃(4) completion and its action kernel

The endpoints are the literal projective point and line parabolics and the
middle is their whole Borel, of order 192. The Borel has trivial normal core
in the simple native model. Transport through the compatible endpoint maps
proves that its image has trivial normal core in every faithful completion.
Once the whole-intersection identity is established, the action on the actual
typed coset graph is therefore faithful.

The smallness argument from the two involutions and the identification of the
resulting plane are separate obligations. They are not assumed in the kernel
theorem. Source: Aschbacher–Smith F.3.3, F.4.8 and F.4.26, pp.270, 278, 288.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
open Theory.GroupTheory
open Matrix.PSL3.LinearThree
open Subgroup.CosetGeometry

local notation "F" => Matrix.PSL3Four.F
local notation "PSL" => Matrix.PSL3Four.PSL

/-- A faithful completion of the actual projective flag amalgam over GF(4). -/
abbrev Completion (G : Type*) [Group G] :=
  RankTwoAmalgam.FaithfulCompletion (GreenBook.LieModels.LinearThree.amalgam F) (G := G)

/-- The native model with both literal subgroup inclusions. -/
def modelCompletion : Completion PSL :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _
    (GreenBook.LieModels.LinearThree.borel_le_point F)
    (GreenBook.LieModels.LinearThree.borel_le_line F)
    (parabolics_sup_eq_top F)

namespace Completion
variable {G : Type*} [Group G] (c : Completion G)

/-- False is the point-parabolic type, true the line-parabolic type. -/
def family : Bool → Subgroup G := fun i => bif i then c.right.range else c.left.range
abbrev Vertex := RankTwo.Vertex c.family
abbrev graph := RankTwo.graph c.family

@[simp] theorem family_false : c.family false = c.left.range := rfl
@[simp] theorem family_true : c.family true = c.right.range := rfl

theorem connected : c.graph.Connected := RankTwo.connected c.family c.generated

theorem bipartite : c.graph.IsBipartiteWith
    {v : c.Vertex | v.type = false} {v : c.Vertex | v.type = true} :=
  RankTwo.coset_bipartition c.family

theorem middle_card : Nat.card c.middle.range = 192 :=
  (RankTwoAmalgam.FaithfulCompletion.middle_card c).trans
    (Matrix.PSL3.CartanActions.BorelQuotient.card_borel_linear_three_four F
      (by simpa using Matrix.PSL3Four.card_F))

end Completion

@[simp] theorem model_left_range : modelCompletion.left.range = pointParabolic F :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range _ _ _ _ _ _

@[simp] theorem model_right_range : modelCompletion.right.range = lineParabolic F :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range _ _ _ _ _ _

@[simp] theorem model_middle_range : modelCompletion.middle.range = borel F :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups_middle_range _ _ _ _ _ _

theorem model_overlap :
    modelCompletion.left.range ⊓ modelCompletion.right.range = modelCompletion.middle.range := by
  rw [model_left_range, model_right_range, model_middle_range]
  exact GreenBook.LieModels.LinearThree.parabolic_intersection F

/-- The whole Borel, including its odd torus, has trivial core in the model. -/
theorem model_middle_normalCore : modelCompletion.middle.range.normalCore = ⊥ := by
  let : IsSimpleGroup PSL := Atlas.psl_simple_high_rank 3 (by decide)
  rcases (inferInstance : modelCompletion.middle.range.normalCore.Normal).eq_bot_or_eq_top
    with h | h
  · exact h
  · have htop : modelCompletion.middle.range = ⊤ :=
      top_unique (h ▸ modelCompletion.middle.range.normalCore_le)
    have hc := modelCompletion.middle_card
    rw [htop, Subgroup.card_top, Matrix.PSL3Four.card_PSL] at hc
    omega

namespace Completion
variable {G : Type*} [Group G] (c : Completion G)

/-- No nontrivial normal subgroup of a completion lies in its marked Borel image. -/
theorem middle_normalCore : c.middle.range.normalCore = ⊥ :=
  c.middle_normalCore_eq_bot_of_model modelCompletion model_middle_normalCore

/-- The whole-overlap identity removes the kernel of the literal coset action. -/
theorem vertex_action_injective_of_overlap
    (ho : c.left.range ⊓ c.right.range = c.middle.range) :
    Function.Injective (MulAction.toPermHom G c.Vertex) := by
  rw [← MonoidHom.ker_eq_bot_iff, RankTwo.global_kernel]
  change (c.left.range ⊓ c.right.range).normalCore = ⊥
  rw [ho]
  exact c.middle_normalCore

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
