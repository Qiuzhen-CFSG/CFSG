module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.EndpointAction.Path
/-!
# Literal source stabilizers under the original ambient map

The compatible left endpoint map identifies the image of its base stabilizer
with the original F1. Translating the point stabilizer commutes with the same
ambient homomorphism. Thus an actual j carrying the base to the fourth point
identifies the mapped fourth stabilizer with F1 conjugated by f(j).
No faithfulness beyond the supplied compatible endpoint marking is needed.
Source: Aschbacher--Smith J.4.7 proof, printed pp.444--445.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee Subgroup.CosetGeometry.RankTwo
variable {D:Type*} [Group D] (q:Completion D)
  {G:Type*} [Group G] {F:Subgroup G} (e:first≃*F) (f:D→*G)
  (hleft:∀a:first,f (q.left a)=(e a:G))
include hleft

theorem left_range_map : q.left.range.map f=F := by
  apply le_antisymm
  · rintro x ⟨y,⟨a,rfl⟩,rfl⟩
    rw [hleft]
    exact (e a).property
  · intro x hx
    obtain ⟨a,ha⟩:=e.surjective ⟨x,hx⟩
    exact ⟨q.left a,⟨a,rfl⟩,(hleft a).trans (congrArg Subtype.val ha)⟩

theorem mapped_stabilizer_translate (j:D) :
    (stabilizer q.family (j • base q.family false)).map f=F.conjBy (f j) := by
  rw [stabilizer_translate]
  simp only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base,Completion.family_false]
  rw [map_map]
  have hh:f.comp (MulAut.conj j).toMonoidHom=(MulAut.conj (f j)).toMonoidHom.comp f := by
    ext x
    exact map_mul f _ _ |>.trans (by rw [map_mul,map_inv];rfl)
  rw [hh,←map_map,left_range_map q e f hleft]
  rfl

theorem mapped_fourth_of_point_transport (j:D)
    (hj:j • base q.family false=completionFourthWord q • base q.family false) :
    (stabilizer q.family (completionFourthWord q • base q.family false)).map f=F.conjBy (f j) := by
  rw [←hj]
  exact mapped_stabilizer_translate q e f hleft j
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.ParabolicFamily.Placement
