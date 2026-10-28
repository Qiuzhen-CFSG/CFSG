module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.ProperImages

/-!
# Saturation transfer from the original marked radical

The original odd-index witness supplies the normalizer-core comparison in the
non-Sylow branch.  Combining that comparison with the exact saturation premise
identifies the characteristic replacement radical with the original radical
restricted to the replacement overgroup.  The compatible marked projection
then identifies their symplectic images.  No containment of `O₂(H)` in the
replacement overgroup is used.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

/-- Saturation turns the original normalizer-core comparison into literal
equality with the original radical restricted to the replacement overgroup. -/
theorem replacement_radical_eq_original_restriction_of_saturated
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    d.radical = R.subgroupOf d.overgroup := by
  rw [← hsat]
  exact replacement_normalizer_core_eq_original_restriction h d g hb hnsyl

/-- In the nonsylow original branch, saturated replacement and original
radicals have the same image in the supplied Sp₄ marking. -/
theorem replacement_marked_image_eq_original_of_saturated
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    (d.ambient.subgroupOf K).map (componentProjection h) =
      (R.subgroupOf K).map (componentProjection h) := by
  obtain ⟨f,hf,hk,hm,hmark⟩ := exists_replacement_marked_projection h d g (by omega)
  have hrad := replacement_radical_eq_original_restriction_of_saturated h d g hb hsat hnsyl
  have hmap := replacement_original_radical_map h d g (by omega) f hk hm
  have hsatmap := congrArg (fun A : Subgroup d.overgroup => A.map f) hrad
  calc
    (d.ambient.subgroupOf K).map (componentProjection h) = d.radical.map f := hmark.symm
    _ = (R.subgroupOf d.overgroup).map f := hsatmap
    _ = (R.subgroupOf K).map (componentProjection h) := hmap

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
