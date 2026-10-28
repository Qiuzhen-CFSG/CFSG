module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Inclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.StarCut

/-!
# The original characteristic-star reduction

The original input constructs a full Sylow seed. Its characteristic star
satisfies the two source comparisons on the original graph, so the literal
centralizer cut preserves the full intrinsic core and removes outer action
in the star overgroup. All earlier graph and natural-cover premises are
discharged here. This is the reduction of MS93 (3.4); preservation of the
original marked radical image in (3.7) is a separate obligation.

Source: MS93 (3.4), printed pp.868--869, and opening of (3.7), p.872.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- The selected original star satisfies the source cut and removes outer
image, with the original graph and both full cores retained. -/
theorem star_pair_core_le
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    let Tstar := (starCentralizer R Y).map R.subtype
    let Mstar := K ⊔ Tstar
    Mstar.Normal ∧ pCore 2 Mstar ≤ Tstar.subgroupOf Mstar ∧
      Tstar ≤ K ⊔ pCore 2 H := by
  exact star_pair_core_le_of_span_le h P Y hY
    (h.original_starSpan_le_moving_fixed geometry hb Y P hY hn)

/-- The original MS input supplies the literal source seed and characteristic
centralizer cut; no star inclusion, replacement or saturation is assumed. -/
theorem exists_source_star_reduction :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      Nat.card (Y.map (embedS R)) ≤ Nat.card F ^ 2 ∧
      (let Tstar := (starCentralizer R Y).map R.subtype
       let Mstar := K ⊔ Tstar
       Mstar.Normal ∧ pCore 2 Mstar ≤ Tstar.subgroupOf Mstar ∧
         Tstar ≤ K ⊔ pCore 2 H) := by
  obtain ⟨geometry,hb,_⟩ := h.positive_even_geometry
  obtain ⟨P,Y,hY,hn,hcard,_⟩ := exists_source_seed h
  exact ⟨P,Y,hY,hn,hcard,star_pair_core_le h geometry hb P Y hY hn⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
