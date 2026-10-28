module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable.Generation

/-!
# The favorable orientation of MS93 (4.4.1)

Choose a moving element of Z_a with a nonzero coordinate on the actual
W/(W intersect B_c), then a marked parabolic fixing that coordinate. The
inner relative marking gives fixed points on U_c and on the image of Z_c.
The W-section transport constructs all of SourceData for (1.7)(i), with the
second pairing group exactly image(Q_c). The completed pairing theorem
then supplies the fixed-part centralization needed for the origin and
generation bounds of PairingWitness.

The stronger construction retains the favorable fixed-space interpretation
on the literal WB_c/B_c under the same flag. The final consumer lifts both
commutator conclusions through G_c/D_c. Only the supplied frame's favorable
orientation is assumed; exclusion of the opposite orientation remains with
the natural-section assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), pp.890--891; the earlier (1.7)(i) application on p.883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase
open RankOnePairing Escape.PairingControl.FirstPairing
open Orientation.QuotientApplication NaturalGeneration Favorable
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}

/-- The favorable orientation supplies the genuine local pairing witness of (4.4.1). -/
theorem pairingWitness_with_fixed_spaces (common : CommonFacts R source geometry)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R)
    (hn : ¬ ⁅Z R a,Q R c⁆ ≤ fixedCore R c) (f : FrameAt a c) (hsame : f.SameOrientation) :
    ∃ p : PairingWitness source hc f,
      (U R c).subgroupOf (stabilizer R c) ⊓ centralizer
        (parabolic f.sectionData.projection p.flag p.side : Set (stabilizer R c)) ≠ ⊥ ∧
      Opposite.barSpan geometry a c ⊓ centralizer
        ((parabolic f.sectionData.projection p.flag p.side).map
          (Opposite.fixedQuotientMap geometry c) : Set (Opposite.FixedQuotient geometry c)) ≠ ⊥ := by
  have hb2 : 2 < geometry.b R := by omega
  let := quotientImage_normal c (Z R c) (Z_normalized R c)
  let := quotientImage_normal c (Q R c) (Q_normalized R c)
  let := quotientImage_normal c (localZSpan R a c) (localZSpan_normalized R a c)
  obtain ⟨x,hx,hxN,hmove⟩ := exists_selected source hc hd hb2 hn f
  have hxW := map_mono (comap_mono (Z_le_localZSpan R a c)) hx
  let n := quotientNaturalW source hc hd hb2 f
  have hne : n.coordinates ⟨x,hxW⟩ ≠ 1 := by
    intro h
    have hk : (⟨x,hxW⟩ : quotientImage c (localZSpan R a c)) ∈ n.coordinates.ker := h
    rw [n.kernel] at hk
    exact hxN hk
  obtain ⟨flag,i,_w,_hw,hfix,_hfw⟩ := Selection.exists_fixed_flag n.marking
    (n.coordinates ⟨x,hxW⟩).toAdd
  let hflag := binaryWeakBN flag
  let ds := naturalSeedData source hc hd hb2 f flag hflag i x hxW hne hfix
  obtain ⟨d⟩ := sourceData_nonempty common ha hc hd hb f hsame flag hflag i x hx hne hfix hmove
  have hf : quotientImage c (Z R c) ⊓ centralizer
      (localResidual (localParabolic (f.extension source hc flag hflag) i) : Set (LocalQuotient c)) ≠ ⊥ := by
    intro h
    apply fixed_Z_of_same common hc hd hb2 f hsame flag i x hxW hne hfix
    apply le_bot_iff.mp
    rw [← h]
    rw [f.extension_parabolic source hc flag hflag]
    exact inf_le_inf_left _ (centralizer_le (map_subtype_le _))
  have hseed : seed f flag i x ≤ quotientImage c (localZSpan R a c) := Seed.le_group ds
  have hxseed : x ∈ seed f flag i x := Seed.cyclic_le ds (mem_zpowers x)
  have hNC := fixedSpan_centralizes_of_pairing source ha hc hd hb2 hn f flag hflag i
    (seed f flag i x) d hf hseed x hxseed hxN
  obtain ⟨horigin,hgeneration⟩ := seed_bounds source hc hd hb2 f flag hflag i x hx hne hfix hNC
  have hv : (n.coordinates ⟨x,hxW⟩).toAdd ≠ 0 := by
    intro h
    exact hne (congrArg Multiplicative.ofAdd h)
  refine ⟨⟨flag,hflag,i,seed f flag i x,d,hf,hseed,horigin,hgeneration⟩, ?_, ?_⟩
  · exact Selection.fixed_subgroup_of_inner f.naturalU n.marking hsame
      (n.coordinates ⟨x,hxW⟩).toAdd hv (fun g hg => hfix _ hg)
  · exact barSpan_fixed_ne_bot source hc hd hb2 f flag i
      (n.coordinates ⟨x,hxW⟩).toAdd hv hfix

/-- The favorable frame constructs every field of the actual source pairing witness. -/
theorem pairingWitness_nonempty (common : CommonFacts R source geometry)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R)
    (hn : ¬ ⁅Z R a,Q R c⁆ ≤ fixedCore R c) (f : FrameAt a c) (hsame : f.SameOrientation) :
    Nonempty (PairingWitness source hc f) := by
  obtain ⟨p,_,_⟩ := pairingWitness_with_fixed_spaces common ha hc hd hb hn f hsame
  exact ⟨p⟩

/-- The conditional favorable branch proves both literal commutator conclusions. -/
theorem localControl_of_sameOrientation (common : CommonFacts R source geometry)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R)
    (hn : ¬ ⁅Z R a,Q R c⁆ ≤ fixedCore R c) (f : FrameAt a c) (hsame : f.SameOrientation) :
    LocalControlAt R a c := by
  obtain ⟨p⟩ := pairingWitness_nonempty common ha hc hd hb hn f hsame
  exact p.localControl ha hc hd hb

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase
