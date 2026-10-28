module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramActor
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.SylowNormalRestriction
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Sylow intersections in a marked parabolic residual

The marked Borel places the original Sylow-component intersection in the
parabolic preimage. That preimage normalizes its perfect residual, so Sylow
restriction gives the required Sylow subgroup of the residual. The two-core
of the original minimal parabolic lies in its normal core and consequently
in the residual's Sylow normalizer.

Source: Aschbacher–Smith, 14.2.8(3), printed p.983.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

omit [Finite H] [Finite D] in
theorem markedParabolicPreimage_normalizes_residual (M K : Subgroup H)
    (e : sourceImage M K ≃* D) (P : Subgroup D) :
    (markedParabolicPreimage M K e P).map K.subtype ≤
      normalizer (markedParabolicResidual M K e P : Set H) := by
  let R := markedParabolicPreimage M K e P
  apply le_normalizer_iff.mpr
  rintro _ ⟨g,hg,rfl⟩ _ ⟨x,hx,rfl⟩
  let r : R := ⟨g,hg⟩
  exact ⟨r*x*r⁻¹,(inferInstance : (solvableResidual R).Normal).conj_mem x hx r,rfl⟩

omit [Finite H] [Finite D] in
theorem sylow_inf_component_le_markedParabolicPreimage
    (M K T : Subgroup H) (hTM : T ≤ M)
    (e : sourceImage M K ≃* D) {P B : Subgroup D}
    (he : (componentOverlap M K).map e.toMonoidHom = B) (hBP : B ≤ P) :
    T ⊓ K ≤ (markedParabolicPreimage M K e P).map K.subtype := by
  intro x hx
  refine ⟨⟨x,hx.2⟩,?_,rfl⟩
  apply hBP
  exact (markedParabolicMap_mem_borel M K e he _).mpr (hTM hx.1)

omit [Finite D] in
theorem original_twoCore_le_markedResidual_normalizer (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃* D) (P : Subgroup D) :
    pCore 2 H ≤ (T : Subgroup H) ⊓ normalizer
      (markedParabolicResidual (ChapterB.minimalParabolicMax T hP) K e P : Set H) := by
  exact le_inf (pCore_isPGroup.le_sylow_of_normal T)
    ((ChapterB.minimalParabolicTwoCore_le_core T hP).trans
      (sourceKernel_le_normalizer_markedParabolicResidual _ K e P))

omit [Finite D] in
theorem markedParabolicResidual_sylow_intersection
    (T : Sylow 2 H) (M K : Subgroup H) [K.Normal] (hTM : (T : Subgroup H) ≤ M)
    (e : sourceImage M K ≃* D) {P B : Subgroup D}
    (he : (componentOverlap M K).map e.toMonoidHom = B) (hBP : B ≤ P) :
    Chapter1.IsSylowIn 2
      (((T : Subgroup H) ⊓ normalizer (markedParabolicResidual M K e P : Set H)) ⊓
        markedParabolicResidual M K e P) (markedParabolicResidual M K e P) := by
  let A := (markedParabolicPreimage M K e P).map K.subtype
  let L := markedParabolicResidual M K e P
  have hAL : A ≤ normalizer (L : Set H) := markedParabolicPreimage_normalizes_residual M K e P
  have hLA : L ≤ A := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x.val,x.property,rfl⟩
  have hi : (T : Subgroup H) ⊓ K ≤ A :=
    sylow_inf_component_le_markedParabolicPreimage M K T hTM e he hBP
  have hs : Chapter1.IsSylowIn 2 ((T : Subgroup H) ⊓ K) K :=
    T.exists_sylow_map_eq_inf_of_normal K
  have hsA := hs.restrict hi (map_subtype_le _)
  have hn : (L.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hLA).mpr hAL
  have hsl := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hsA hLA
    hn.isSubnormal
  have hh : (((T : Subgroup H) ⊓ normalizer (L : Set H)) ⊓ L) =
      (((T : Subgroup H) ⊓ K) ⊓ L) := by
    ext x
    constructor
    · rintro ⟨⟨ht,_⟩,hl⟩
      exact ⟨⟨ht,markedParabolicResidual_le M K e P hl⟩,hl⟩
    · rintro ⟨⟨ht,_⟩,hl⟩
      exact ⟨⟨ht,L.le_normalizer hl⟩,hl⟩
  exact hh.symm ▸ hsl
end CFSG.Quasithin.Chapter14.Section02
