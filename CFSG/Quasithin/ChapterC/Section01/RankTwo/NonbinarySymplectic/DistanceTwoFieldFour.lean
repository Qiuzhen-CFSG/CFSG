module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.FieldFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.FieldFour

/-!
# Original nonbinary symplectic recognition at distance two

The original marked radical image either is a Sylow subgroup of the
symplectic quotient or is not. Both original-star arguments now restrict
the original field to order four and recognize the original component.
No Sylow alternative or field restriction is left as an input. The general
distance reduction is still required for the full C.1.32 theorem.

Source: MS93 (3.7), printed pp.872--877; Aschbacher--Smith C.1.32.
-/

public section
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open DistanceTwoRecognition MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ}

/-- At distance two the actual original component is an Sp₄(4) block.
Both alternatives for the original marked radical image are discharged. -/
theorem Input.field_and_block_of_distance_two (h : Input K R n F)
    (d : CharacteristicReduction K R) (g : Geometry d.radical)
    (hb : g.b d.radical = 2) :
    n = 2 ∧ Nat.card F = 4 ∧ IsSp4FourBlock K := by
  by_cases hs : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)
  · exact OriginalSylow.original_sylow_distance_two_field_and_block h d g hb hs
  · exact OriginalStar.original_nonsylow_distance_two_field_and_block h d g hb hs

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
