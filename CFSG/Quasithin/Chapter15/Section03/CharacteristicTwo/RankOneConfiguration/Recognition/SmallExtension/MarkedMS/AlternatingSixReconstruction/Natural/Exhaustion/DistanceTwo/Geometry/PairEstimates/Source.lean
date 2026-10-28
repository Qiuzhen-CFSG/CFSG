module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Inputs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.CentralSquares

/-!
# Conditional source assembly of all three paired estimates

The unconditional selected-orbit application below proves order-eight images,
a fixed index of four, abelianness of the paired commutator, and the common
central-attachment bound for its squares.

The faithful quotient action gives order-eight orbit images. The existing
local-image source input bounds the edge quotient, so these images are full.
The two independent central-cover calculations then move the maximal plane
and make the paired commutator elementary. All indices, conjugations and
subgroups are the literal original ones. The final application selects the
OrderedOrbit using Geometry.exists_orderedOrbit.

This module does not discharge its three source inputs. In particular it is
not an unconditional proof of PairEstimateInput KnownSimple.IsKnownSimple.
Source: MS93 (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
universe u

/-- The literal favorable orbit already has both sharp image indices and an
abelian paired commutator with centrally trapped squares. This application
requires only the authorized local calculations, with no full-image,
plane-movement, or exponent-two premise. -/
theorem exists_ordered_early_estimates {κ : GroupClass.{u}}
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ⊔
        X d.radical (alpha d.radical))
    (hl : LocalCalculations d.radical (replacementGeometry h d)) :
    ∃ o : OrderedOrbit (replacementGeometry h d),
      (Q d.radical (alpha d.radical)).relIndex o.opposite = 8 ∧
      (Q d.radical o.c).relIndex (criticalOrbit d.radical o.c o.b) = 8 ∧
      (commutatorPreimage (criticalOrbit d.radical o.c o.b) o.opposite
        (Z d.radical (alpha d.radical))).relIndex (criticalOrbit d.radical o.c o.b) = 4 ∧
      IsMulCommutative (⁅criticalOrbit d.radical o.c o.b,o.opposite⁆ :
        Subgroup (FreeAmalgam d.radical)) ∧
      ∀ x ∈ ⁅criticalOrbit d.radical o.c o.b,o.opposite⁆,
        x ^ 2 ∈ Z d.radical o.b ⊓
          centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ⊓
          centralizer (Ltilde d.radical o.c : Set (FreeAmalgam d.radical)) := by
  obtain ⟨o⟩ := exists_orderedOrbit (replacementGeometry h d)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hl hb
  let a := earlyPair (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
    hl hb hlarge o
  let := a.quotient_elementary
  obtain ⟨hB,hA,hfix⟩ := (sourceImageModel h e hz hn d a).strict_indices
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
  exact ⟨o,hB,hA,hfix,
    a.commutator_commutative (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hl,
    fun _ hx => a.commutator_square_common_attachment
      (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hl hx⟩

/-- Assemble the exact contract, discharging image fullness internally and
retaining only the independent source calculations. -/
theorem pairEstimate_of_inputs {κ : GroupClass.{u}}
    (hi : LocalImageInput κ) (hm : PlaneMovementInput κ)
    (he : PairedExponentInput κ) : PairEstimateInput κ := by
  intro G _ _ L R h e hz hn d hcentral hb hlarge hl c b B hc hab hcb hr hs ho
  have hd := hi G L R h e hz hn d hcentral hb hlarge
  let o := orderedOfRebased (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
    hl c b B hc hab hcb hr hs ho
  have hfull := source_images_full h e hz hn d hl hb hlarge hd.radical_derived o
  exact {
    full_image := hfull.2
    moved_plane := hm G L R h e hz hn d hcentral hb hlarge hl hd c b hc hab hcb hfull.2
    elementary_commutator :=
      (earlyPair (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
        hl hb hlarge o).elementary_commutator_of_squares
          (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hl
          (he hm G L R h e hz hn d hcentral hb hlarge hl hd
            c b B hc hab hcb hr hs ho hfull.2 hfull.1) }

/-- Apply the conditional estimates to the literal favorable orbit chosen by
minimum relative index, with its retained reversed/rebased witness. -/
theorem exists_ordered_estimates {κ : GroupClass.{u}}
    (hi : LocalImageInput κ) (hm : PlaneMovementInput κ) (he : PairedExponentInput κ)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hcentral : CentralLayer d) (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ⊔
        X d.radical (alpha d.radical))
    (hl : LocalCalculations d.radical (replacementGeometry h d)) :
    ∃ o : OrderedOrbit (replacementGeometry h d), PairEstimates d.radical o.c o.b o.opposite := by
  obtain ⟨o⟩ := exists_orderedOrbit (replacementGeometry h d)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hl hb
  exact ⟨o,pairEstimate_of_inputs hi hm he G L R h e hz hn d hcentral hb hlarge hl
    o.c o.b o.opposite o.critical o.adjacent_left o.adjacent_right o.rebased
    o.strict_index o.ordered_index⟩

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
