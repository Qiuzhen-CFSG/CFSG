module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Application
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Bounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural

/-!
# Finite incident pairing application for MS93 (4.6.8)(3)

The incident representative identifies the original finite group with the
actual alpha stabilizer. In its quotient by the fixed core D_alpha, the seed
is the image of Z_alpha joined with [V_beta,Q_delta2]. Its ambient normal
closure is the image of the literal incident span.

The four seed bounds and the natural section with its exact intrinsic
fixed-preimage kernel now construct every field of the finite (1.7) source.
The nonzero opposite fixed space selects part (i); its triple conclusion
lifts to the fixed-core bound in the free amalgam. Together with the
unquotiented moving containment this supplies exactly the two quantified
premises of `Pairing.exists_delta2_triple_of_pairing`.

The hypothetical triple retains the tilded incident residual. The local
actors in (1.7) are the full untilded residuals, identified with their
parabolics in this two-group-kernel specialization. No later radius facts
or delta0 selection are used.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.7)(i), printed pp.847--848, and (4.6.8)(3), printed p.906.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The genuine finite pairing source, with all local bounds and the exact
fixed-preimage natural factor proved from the original incident inputs. -/
noncomputable def sourceData (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (p : FlagCriticalData source geometry i)
    (d : M) (hd : flagIncident source i 1 d)
    (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    RankOnePairing.SourceData
      (Quotient.extension source (representative source i d hd)) (!i)
      (Quotient.image (Z R (alpha R))) (Quotient.image (V R (alpha R)))
      (Quotient.seed source i d) := by
  have hmoving := Natural.moving_le_span source geometry common.large_distance i hkernel d hd
  obtain ⟨hPhi, hcomm, hnontrivial, hcard⟩ :=
    Quotient.Bounds.seed_bounds source geometry common early i hkernel d hd p hmoving
  exact Quotient.sourceData_of_bounds source geometry common i hkernel d hd htriple
    hPhi hcomm hnontrivial hcard
    (Natural.seed_fixed source geometry common early i hkernel d hd htriple)
    (Classical.choice
      (Natural.rankOneFactor_nonempty source geometry common early i hkernel natural d hd htriple))

/-- The first universally quantified premise of
`Pairing.exists_delta2_triple_of_pairing`, in the original free amalgam. -/
theorem moving_premise (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : FlagCriticalData source geometry i) :
    ∀ d, flagIncident source i 1 d →
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) →
      ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
        localFlagResidual source (!i) d⁆ ≤ Z R (alpha R) →
      ⁅V R (beta R), flagResidual source i⁆ ≤ Pairing.span source i d := by
  intro d hd _ _
  exact Natural.moving_le_span source geometry common.large_distance i hkernel d hd

/-- The second universally quantified premise of
`Pairing.exists_delta2_triple_of_pairing`. Apply the genuine finite (1.7)(i)
and lift its triple bound through the quotient by the actual fixed core. -/
theorem pairing_premise (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i) (p : FlagCriticalData source geometry i) :
    ∀ d, flagIncident source i 1 d →
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) →
      ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
        localFlagResidual source (!i) d⁆ ≤ Z R (alpha R) →
      ⁅Vcirc R (alpha R), Pairing.span source i d⁆ ≤ fixedCore R (alpha R) := by
  intro d hd _ htriple
  let s := sourceData source geometry common early i hkernel natural p d hd htriple
  have hz := Natural.opposite_fixed_nonzero source geometry common early i hkernel d hd
  exact Quotient.pairing_bound_of_quotient source geometry common.large_distance i hkernel d hd
    (RankOnePairing.theorem_1_7_i s hz).2.1

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport
