module
public import CFSG.Quasithin.ChapterF.Section05.ModelVertexFlag
/-!
# The original completion's independent local complement

Transport the explicit native plane subgroup through the actual right endpoint
of a faithful completion. Any completion comparison that agrees with this
endpoint sends precisely that subgroup to the second model factor; its order
is24 by injectivity. This is the marked-complement input for F.5.7's local-map
adjustment, with agreement with the original endpoint kept explicit.

Source: Aschbacher–Smith F.5.7(2), printed p.303.
-/
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05
open GreenBook.LieModels.UnitaryFour
open ExceptionalLocal
public noncomputable section
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

/-- The independent complement through the original source plane inclusion. -/
def sourceLocalComplement : Subgroup G :=
  (nativeLocalComplement.subgroupOf (Extension.plane 1 hn)).map (i.comp c.right)

/-- A marked completion comparison has exactly the same independent complement;
only agreement with the original right endpoint map is needed. -/
theorem sourceLocalComplement_eq_map (j : Extension.ProjectiveExtension 1 hn →* G)
    (hj : ∀ a : Extension.plane 1 hn, j a.val = i (c.right a)) :
    sourceLocalComplement c i = nativeLocalComplement.map j := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    exact ⟨a.val,ha,hj a⟩
  · rintro _ ⟨a,ha,rfl⟩
    refine ⟨⟨a,nativeLocalComplement_le_plane ha⟩,ha,?_⟩
    exact (hj _).symm

/-- The source complement has its original order as soon as the original
embedding is faithful. -/
theorem sourceLocalComplement_card (hi : Function.Injective i) :
    Nat.card (sourceLocalComplement c i) = 24 := by
  rw [sourceLocalComplement,card_map_of_injective (f := i.comp c.right) (hi.comp c.right_injective)]
  rw [Nat.card_congr (subgroupOfEquivOfLe nativeLocalComplement_le_plane).toEquiv]
  exact nativeLocalComplement_card

/-- Through any marked completion comparison, the actual model second factor
maps onto the source complement defined with the literal endpoint map. -/
theorem sourceLocalComplement_model_image (j : Extension.ProjectiveExtension 1 hn →* G)
    (hj : ∀ a : Extension.plane 1 hn, j a.val = i (c.right a)) :
    sourceLocalComplement c i =
      (nativeLocalComplement.map markedModelUnitaryExtensionEquivVertex.toMonoidHom).map
        (j.comp markedModelUnitaryExtensionEquivVertex.symm.toMonoidHom) := by
  rw [map_map,sourceLocalComplement_eq_map c i j hj]
  congr 1
  apply MonoidHom.ext
  intro a
  exact congrArg j (markedModelUnitaryExtensionEquivVertex.symm_apply_apply a).symm

end
end CFSG.Quasithin.ChapterF.Section05
