module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoDisplacementBounds

/-!
# Field-sized critical indices in the large-movement branch

The large-movement alternative in MS93 (3.7)(2) identifies the first
critical quotient with the original field.  Reversing the same critical path
and applying the reciprocal small-index comparison identifies the opposite
quotient as well.  This packages both equalities together with the exact
large-movement premise, so source (3.7)(5)--(6) can consume one literal
configuration without re-proving the path reversal arithmetic.

The premise remains the actual centralizer index on `Q`, and the saturated
radical is not replaced by an order-field subgroup.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Both actual critical images are of order `q` in the large-movement
branch.  The first equality is the source-(2) image comparison; the second
is obtained from the reciprocal path, whose critical index is strictly below
`q²` by the first equality and nonbinary degree. -/
theorem source_two_large_critical_indices
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)) :
    (Q d.radical z).relIndex (Z d.radical a) = 2^n ∧
      (Q d.radical a).relIndex (Z d.radical z) = 2^n := by
  have hfirst := (source_two_large_movement_images h d g hb hsat path hat hzt c c' hlarge).2.2.1
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < (2^n)^2 := by
    rw [hfirst]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2 : ℕ))
      (by have := h.nonbinary; omega)
    nlinarith
  exact ⟨hfirst,
    (replacement_critical_indices_eq_field_of_small h d path (by omega) hsmall).2⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
