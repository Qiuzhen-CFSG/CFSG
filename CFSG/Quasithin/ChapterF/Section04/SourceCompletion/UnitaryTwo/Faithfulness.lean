module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.CommonCover
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.SylowGeometry
public import Theory.GroupAction.RankTwoCosetCover.Faithfulness

/-!
# Faithful action of an actual U₄(2) completion on its coset graph

The native overlap has trivial normal core. Its coset action is consequently
faithful. The actual common amalgam covering transfers this fact to every
faithful completion, using the actions on all finite based walks. This is
the kernel input to the 27-point quadrangle recognition in F.4.24.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
open Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
open GreenBook.LieModels.UnitaryFour
local notation "h1" => (Nat.le_refl 1)

theorem native_vertex_action_injective :
    Function.Injective (MulAction.toPermHom (ProjectiveGroup 1 h1) modelCompletion.Vertex) := by
  rw [← MonoidHom.ker_eq_bot_iff, global_kernel]
  have he : modelCompletion.family false ⊓ modelCompletion.family true = overlap 1 h1 := by
    change (pointParabolic 1 h1).subtype.range ⊓ (planeParabolic 1 h1).subtype.range = _
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact (Subgroup.map_inf _ _ _ (projection_injective 1 h1)).symm
  rw [he]
  exact overlap_normalCore_eq_bot 1 h1

theorem Completion.vertex_action_injective {G : Type*} [Group G] (c : Completion G) :
    Function.Injective (MulAction.toPermHom G c.Vertex) := by
  have hgcd : (Nat.card (pointParabolic 1 h1)).gcd (Nat.card (planeParabolic 1 h1)) =
      Nat.card (GreenBook.LieModels.UnitaryFour.overlap 1 h1) := by
    rw [BinaryCompletion.point_card, BinaryCompletion.plane_card, BinaryCompletion.middle_card]
    norm_num
  exact (RankTwoAmalgam.Universal.coverData (amalgam 1 h1) hgcd c).injective_action_transfer
    (RankTwoAmalgam.Universal.coverData (amalgam 1 h1) hgcd modelCompletion)
    (base (RankTwoAmalgam.Universal.cosetFamily (amalgam 1 h1)) false)
    modelCompletion.connected native_vertex_action_injective

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
