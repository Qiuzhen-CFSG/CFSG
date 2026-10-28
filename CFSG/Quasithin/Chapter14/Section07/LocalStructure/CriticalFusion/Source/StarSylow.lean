module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceMarking
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# The original starred Sylow subgroup preceding 14.7.65

The constructed upper-root marking identifies R₁* with the image of the
actual upper unipotent Sylow of SL₂(4). The same original quotient map
identifies K* with A₅. Faithful transport gives the relative Sylow statement
without changing either ambient subgroup or the star map.

Source: Aschbacher–Smith, paragraph preceding 14.7.65, printed p.1069.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Rechoice.Goldschmidt.LeftChiefFactors
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelFactors

private theorem root_sylow (r : ChapterJ.L2FourAction) :
    Chapter1.IsSylowIn 2 (BorelRefinements.root r) (alternatingGroup (Fin 5)) := by
  let P := Matrix.SpecialLinearGroup.upperUnipotentSylow SL2FourNatural.F 2
  have hP : Chapter1.IsSylowIn 2 U0 (⊤ : Subgroup SL) := by
    apply Chapter1.isSylowIn_iff.mpr
    refine ⟨P.isPGroup', le_top, ?_⟩
    intro B hB hPB _
    exact P.is_maximal' hB hPB
  have hm := (Chapter1.IsSylowIn.map_iff (BorelRefinements.markingHom r)
    (BorelRefinements.markingHom_injective r)).mpr hP
  have he : (⊤ : Subgroup SL).map (BorelRefinements.markingHom r) =
      alternatingGroup (Fin 5) := by
    rw [BorelRefinements.markingHom, ← map_map,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr r.marking.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  rw [he] at hm
  exact hm

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The original R₁ image is a Sylow subgroup of the original K image. -/
theorem Data.source_Ri_star_sylow (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Chapter1.IsSylowIn 2 (star F (F.Ri L 1)) (star F (K F)) := by
  let d' := BorelRefinements.upperRemark d structural
  have hm := BorelRefinements.upperRemark_upperMarking d structural
  have hs := root_sylow d'.naturalQuotient
  apply (Chapter1.IsSylowIn.map_iff d.model.toMonoidHom d.model.injective).mp
  have hR : (star F (F.Ri L 1)).map d.model.toMonoidHom =
      BorelRefinements.root d'.naturalQuotient := by
    rw [star, map_map]
    exact hm
  have hK : (star F (K F)).map d.model.toMonoidHom = alternatingGroup (Fin 5) := by
    rw [star, map_map]
    exact d.K_image
  rw [hR,hK]
  exact hs

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
