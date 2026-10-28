module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable.Quotient
/-!
# The W-section consumer of the localization and rank-one transport

The literal quotient G_c/D_c supplies every structural input to the section
transport. A chosen element in image(Z_a), with a nonzero natural coordinate
fixed by the selected favorable parabolic and nontrivial Q_c displacement,
then supplies all fields of the actual SourceData for (1.7)(i). The small
commutator bound is derived from the distance-two geometry, and the Frattini
bound from the elementary W-image. Neither is an additional input.

The source seed is image(Z_c) joined with the first parabolic's closure of
the chosen cyclic group. The opposite closure's rank-one factor retains the
literal fixedPreimage kernel and the untilded residual action. Favorable
orientation transfers the nonzero fixed coordinate to the actual Z_c image.

Selection of the element and flag, and the origin and generation bounds
required by PairingWitness, remain with the favorable-orientation assembly.
This module proves the conditional W-section transport and its concrete
SourceData application; it does not assert the whole of (4.4.1).

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), pp.890--891,
applying (1.7)(i), pp.847--848, as on p.883.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable
open RankOnePairing
open Escape.PairingControl.FirstPairing
open Orientation.QuotientApplication
open NaturalGeneration
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}

/-- The literal seed to be chosen by the favorable-orientation assembly. -/
noncomputable def seed (f : FrameAt a c) (flag : SL) (i : Bool) (x : LocalQuotient c) :
    Subgroup (LocalQuotient c) :=
  quotientImage c (Z R c) ⊔ localGenerated (parabolic f.projection flag i) (zpowers x)

omit [Finite M] in
/-- The elementary property belongs to the actual image of the entire W-section. -/
theorem span_elementary (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R) :
    IsElementaryAbelian 2 (quotientImage c (localZSpan R a c)) := by
  let := localZSpan_elementary R hc hd.le hb
  let := IsElementaryAbelian.subgroupOf (p := 2)
    ((localZSpan_le_Q R hc hd.le (by omega : 2 < geometry.b R)).trans (fun _ hx => hx.1))
  exact IsElementaryAbelian.map (quotientMap c)

omit [Finite M] in
theorem span_le_kernel (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R) (f : FrameAt a c) :
    quotientImage c (localZSpan R a c) ≤ f.projection.ker := by
  rw [FrameAt.projection, quotientProjection_kernel]
  exact map_mono (comap_mono (localZSpan_le_Q R hc hd.le hb))

@[simp] theorem extension_flag (source : LocalSource L R) (hc : color R c = false)
    (f : FrameAt a c) (flag : SL) (hflag : BinaryWeakBN flag) :
    (f.extension source hc flag hflag).flag = flag := rfl

/-- The transport input retains the quotient map, coordinate kernel and selected element. -/
noncomputable def naturalSeedData (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (flag : SL) (hflag : BinaryWeakBN flag) (i : Bool)
    (x : LocalQuotient c) (hx : x ∈ quotientImage c (localZSpan R a c))
    (hne : (quotientNaturalW source hc hd hb f).coordinates ⟨x,hx⟩ ≠ 1)
    (hfix : ∀ g ∈ modelParabolic flag i,
      ((quotientNaturalW source hc hd hb f).marking g).val.mulVec
        ((quotientNaturalW source hc hd hb f).coordinates ⟨x,hx⟩).toAdd =
          ((quotientNaturalW source hc hd hb f).coordinates ⟨x,hx⟩).toAdd) :
    NaturalSeedData f.projection flag i (quotientImage c (localZSpan R a c))
      (fixedSpan geometry a c) (quotientImage c (Z R c)) x := by
  refine {
    natural := quotientNaturalW source hc hd hb f
    projection_surjective := quotientProjection_surjective c _
      f.sectionData.module_section.projection_surjective _
    residual_image := ?_
    fixed_le_group := fixedSpan_le
    z_le_fixed := Z_le_fixedSpan hc hd hb
    z_le_kernel := (Z_le_fixedSpan hc hd hb).trans (fixedSpan_le.trans (span_le_kernel hc hd hb f))
    element_mem := hx
    element_kernel := span_le_kernel hc hd hb f hx
    nonzero := hne
    fixed := hfix }
  intro j
  have h := localResidual_map (f.extension source hc flag hflag) j
  simpa only [f.extension_parabolic source hc flag hflag, FrameAt.extension_projection, extension_flag] using h

/-- Nonzero coordinates of the favorable marking give genuine fixed points on Z_c. -/
theorem fixed_Z_of_same (common : CommonFacts R source geometry)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hsame : f.SameOrientation)
    (flag : SL) (i : Bool) (x : LocalQuotient c)
    (hx : x ∈ quotientImage c (localZSpan R a c))
    (hne : (quotientNaturalW source hc hd hb f).coordinates ⟨x,hx⟩ ≠ 1)
    (hfix : ∀ g ∈ modelParabolic flag i,
      ((quotientNaturalW source hc hd hb f).marking g).val.mulVec
        ((quotientNaturalW source hc hd hb f).coordinates ⟨x,hx⟩).toAdd =
          ((quotientNaturalW source hc hd hb f).coordinates ⟨x,hx⟩).toAdd) :
    quotientImage c (Z R c) ⊓
      centralizer (parabolic f.projection flag i : Set (LocalQuotient c)) ≠ ⊥ := by
  apply Selection.fixed_subgroup_of_inner (f.naturalZ common hc)
    (quotientNaturalW source hc hd hb f).marking hsame
    ((quotientNaturalW source hc hd hb f).coordinates ⟨x,hx⟩).toAdd
  · exact fun h => hne (congrArg Multiplicative.ofAdd h)
  · intro p hp
    exact hfix _ hp

/-- The selected element and its favorable coordinate yield all (1.7) fields.
The parent chooses the element and flag; no localization or rank-one hypothesis is assumed. -/
theorem sourceData_nonempty (common : CommonFacts R source geometry)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R)
    (f : FrameAt a c) (hsame : f.SameOrientation)
    (flag : SL) (hflag : BinaryWeakBN flag) (i : Bool)
    (x : LocalQuotient c) (hx : x ∈ quotientImage c (Z R a))
    (hne : (quotientNaturalW source hc hd (by omega : 2 < geometry.b R) f).coordinates
      ⟨x, map_mono (comap_mono (Z_le_localZSpan R a c)) hx⟩ ≠ 1)
    (hfix : ∀ g ∈ modelParabolic flag i,
      ((quotientNaturalW source hc hd (by omega : 2 < geometry.b R) f).marking g).val.mulVec
        ((quotientNaturalW source hc hd (by omega : 2 < geometry.b R) f).coordinates
          ⟨x, map_mono (comap_mono (Z_le_localZSpan R a c)) hx⟩).toAdd =
            ((quotientNaturalW source hc hd (by omega : 2 < geometry.b R) f).coordinates
              ⟨x, map_mono (comap_mono (Z_le_localZSpan R a c)) hx⟩).toAdd)
    (hmove : ⁅zpowers x, quotientImage c (Q R c)⁆ ≠ ⊥) :
    letI := quotientImage_normal c (Z R c) (Z_normalized R c)
    letI := quotientImage_normal c (Q R c) (Q_normalized R c)
    Nonempty (SourceData (f.extension source hc flag hflag) i
      (quotientImage c (Z R c)) (quotientImage c (Q R c)) (seed f flag i x)) := by
  let := quotientImage_normal c (Z R c) (Z_normalized R c)
  let := quotientImage_normal c (Q R c) (Q_normalized R c)
  let := quotientImage_normal c (localZSpan R a c) (localZSpan_normalized R a c)
  let := fixedSpan_normal (geometry := geometry) (a := a) (c := c)
  let := span_elementary hc hd hb
  have hb2 : 2 < geometry.b R := by omega
  have hxW : x ∈ quotientImage c (localZSpan R a c) :=
    map_mono (comap_mono (Z_le_localZSpan R a c)) hx
  let d := naturalSeedData source hc hd hb2 f flag hflag i x hxW hne hfix
  have hker : f.projection.ker = quotientImage c (Q R c) := quotientProjection_kernel c _ _
  have hp : IsPGroup 2 f.projection.ker := quotientProjection_kernel_isPGroup source c hc _ _
  have hE := component_eq_residual source hc f flag
  have hN := fixedSpan_commutator (geometry := geometry) source hc hd f flag
  have hHQ : ⁅quotientImage c (localZSpan R a c), f.projection.ker⁆ ≤ fixedSpan geometry a c := by
    rw [hker]
    exact span_commutator_le_fixedSpan hd f
  have hZQ := Z_centralizes_kernel (geometry := geometry) hc f
  have hfixed := fixed_Z_of_same common hc hd hb2 f hsame flag i x hxW hne hfix
  have hcard : Nat.card (⁅zpowers x, f.projection.ker⁆ : Subgroup (LocalQuotient c)) ≤ 4 := by
    rw [hker]
    exact seed_commutator_card_le_four common ha hc hd hb (zpowers x)
      ((zpowers_le.mpr hx).trans le_sup_left)
  have hnorm := Seed.cyclic_normalized d hp hE hN hHQ hZQ (f.naturalZ common hc) hfixed hcard
  have hlocal := Seed.cyclic_le_natural d hp hE (span_le_kernel hc hd hb2 f) hN hHQ hZQ
    (kernel_fixed_eq_bot source hc f flag) (f.naturalZ common hc) hfixed hcard
  have heq := Seed.commutator_eq_cyclic d hZQ hnorm
  have hseed : d.seed = seed f flag i x := rfl
  rw [hseed, hker] at heq
  rw [hker] at hlocal hcard
  obtain ⟨rank⟩ := Seed.rankOne_nonempty d hN
  have hs := Seed.le_group d
  rw [hseed] at hs
  have hn := Seed.normalized d
  rw [hseed] at hn
  refine ⟨{
    z_le := le_sup_left
    x_le := ?_
    w_le := ?_
    x_normal := ?_
    natural := ?_
    frattini_le := ?_
    commutator_le := heq.le.trans hlocal
    commutator_nontrivial := ?_
    commutator_card_le := by rw [heq]; exact hcard
    seed_fixed := ?_
    rank_one_natural := ?_ }⟩
  · rw [f.extension_core source hc flag hflag, ← hker]
    exact Seed.le_kernel d
  · rw [f.extension_core source hc flag hflag]
  · rw [f.extension_parabolic source hc flag hflag]
    exact normal_subgroupOf_of_le_normalizer hn
  · let z := f.naturalZ common hc
    exact { z with
      normalized := le_top.trans z.normalized
      action := fun l _ u v hv => z.action l (mem_top _) u v hv }
  · rw [generated_frattini_eq_bot hc hd hb _ hs, Subgroup.map_bot]
    exact bot_le
  · intro h
    apply hmove
    rw [← heq]
    exact card_eq_one.mp h
  · simpa only [f.extension_parabolic source hc flag hflag, FrameAt.extension_projection,
      extension_flag, hseed] using Seed.seed_fixed d hN
  · simpa only [f.extension_parabolic source hc flag hflag, FrameAt.extension_projection,
      extension_flag, hseed] using rank

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Favorable
