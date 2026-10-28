module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Module

/-!
# The actual pairing application for the single-section propagation branch

For a chosen conjugate seed with the local module properties specified by
`SeedModuleData`, this module constructs every field of the original (1.7)
`SourceData`. Its generated group is V₀, its pairing group W is V_alpha,
and its natural central group is U_alpha, all inside the original finite M.
The untilded local residuals are the full marked parabolics. Case (i) gives
[V_alpha,L,V₀] = 1; mapping through embedM is exactly [V₀,V_alpha-circ] = 1.

`singleSection_pairing` constructs the seed's module data from the full
`SingleSection` hypothesis and the selected kernel, then applies the pairing
through `singleSection_pairing_of_seedModule`. Thus no local module witness or
pairing conclusion remains as an extra premise. The final propagation assembly,
including the other source branch, remains in the parent module.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(i), pp.847--848, and
(4.6.8), claim (2), printed p.906.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation
namespace Pairing
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The untilded actor is the full local parabolic in this two-group-kernel extension. -/
theorem localResidual_eq_parabolic (source : LocalSource L R) (j : Bool) :
    localResidual (localParabolic (pairingExtension source) j) =
      localParabolic (pairingExtension source) j := by
  rw [pairing_parabolic, localResidual,
    primeToResidual_parabolic_eq_top source.projection source.projection_surjective
      (by rw [source.projection_kernel]; exact pCore_isPGroup),
    ← MonoidHom.range_eq_map, range_subtype]

/-- Being fixed modulo Z_alpha gives the required relative parabolic normality. -/
theorem SeedModuleData.seed_normal {p : FlagCriticalData source geometry i}
    (d : SeedModuleData p) :
    ((seed p d.conjugator).subgroupOf (localParabolic (pairingExtension source) (!i))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [← localResidual_eq_parabolic source (!i)]
  exact d.seed_fixed.trans le_sup_left

/-- Construct all source hypotheses from the local module choice and the proved group bounds. -/
noncomputable def SeedModuleData.sourceData (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) {p : FlagCriticalData source geometry i}
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R)) (d : SeedModuleData p) :
    SourceData (pairingExtension source) (!i) (naturalLayer (R := R))
      (radiusLayer (R := R)) (seed p d.conjugator) where
  z_le := naturalLayer_le_seed p d.conjugator
  x_le := seed_le_core common p d.conjugator
  w_le := radiusLayer_le_core common
  x_normal := d.seed_normal
  natural := naturalCoordinates common
  frattini_le := by
    rw [generated_seed common p d.conjugator]
    exact spanLayer_frattini common p hseed
  commutator_le := seed_commutator_le common p hseed d.conjugator
  commutator_nontrivial := seed_commutator_nontrivial common p d.conjugator
  commutator_card_le := seed_commutator_card_le common early p d.conjugator
  seed_fixed := d.seed_fixed.trans (centralLayer_le_fixedPreimage common p d.conjugator)
  rank_one_natural := by
    simpa only [Bool.not_not, pairingExtension_projection, pairingExtension_flag] using d.local_natural

end Pairing

open Pairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The literal (1.7)(i) application, with its remaining local module choice explicit. -/
theorem singleSection_pairing_of_seedModule (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R)) (d : SeedModuleData p) :
    ⁅midpointSpan p, Vcirc R (alpha R)⁆ = ⊥ := by
  have ht := (RankOnePairing.theorem_1_7_i (d.sourceData common early hseed)
    d.fixed_nonzero).2.1
  have hm := congrArg (Subgroup.map (embedM R)) ht
  rw [map_commutator, map_commutator, generated_seed common p d.conjugator,
    map_spanLayer common p, map_radiusLayer common, pairingExtension_projection,
    pairingExtension_flag, map_component,
    Subgroup.map_bot] at hm
  rwa [commutator_comm] at hm

/-- The single-section branch of (4.6.8)(2): the midpoint span centralizes
V_alpha-circ. The seed and all (1.7)(i) hypotheses are constructed from the
source data, with the original quotient marking and intrinsic denominators. -/
theorem singleSection_pairing (common : CommonFacts R source geometry)
    (_hb : geometry.b R = 4) (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (_natural : FlagNaturalSection source i) (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (hs : SingleSection p) : ⁅midpointSpan p, Vcirc R (alpha R)⁆ = ⊥ := by
  obtain ⟨d⟩ := seedModuleData common early p hkernel hseed hs
  exact singleSection_pairing_of_seedModule common early p hseed d

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation
