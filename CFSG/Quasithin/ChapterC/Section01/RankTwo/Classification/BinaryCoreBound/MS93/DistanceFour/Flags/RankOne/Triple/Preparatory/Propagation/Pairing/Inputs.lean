module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Groups

/-!
# The local module choice for the single-section pairing

`SeedModuleData` specifies the remaining representation calculation. It selects
an actual M-conjugate of the midpoint. Its seed is fixed modulo Z_alpha by the
opposite full parabolic, and its closure under the first parabolic has genuine
natural two-space coordinates modulo the literal global fixed preimage. The
nonzero fixed subgroup in U_alpha specifies case (i) of the pairing theorem.

This is an intermediate output type, not a consequence of `SingleSection`
proved here. Its producer must use the supplied single natural section and
flag natural section, retain their quotient markings, and establish all three
fields. The group bounds and final pairing application are independent of
that producer.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(i), pp.847--848, and
(4.6.8), claim (2), printed p.906.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
open RankOnePairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The actual local module choice still required for the p.906 application.
None of its fields assumes a commutator-pairing conclusion. -/
structure SeedModuleData (p : FlagCriticalData source geometry i) where
  conjugator : M
  seed_fixed : ⁅seed p conjugator,
    localResidual (localParabolic (pairingExtension source) (!i))⁆ ≤ centralLayer (R := R)
  local_natural : RankOneFactor
    (localResidual (localParabolic (pairingExtension source) i))
    (localGenerated (localParabolic (pairingExtension source) i) (seed p conjugator))
    (fixedPreimage (component source.projection source.flag) (seed p conjugator)
      (naturalLayer (R := R)))
  fixed_nonzero : naturalLayer (R := R) ⊓
    centralizer (localResidual (localParabolic (pairingExtension source) (!i)) : Set M) ≠ ⊥

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Pairing
