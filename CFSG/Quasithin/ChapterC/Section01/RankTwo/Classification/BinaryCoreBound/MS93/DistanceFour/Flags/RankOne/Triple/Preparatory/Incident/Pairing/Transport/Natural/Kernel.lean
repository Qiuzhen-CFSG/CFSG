module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.FixedSummand

/-!
# Comparing the incident intrinsic kernels

On the actual local span, the supplied flag-section denominator equals the
global component-fixed denominator used in (1.7). The binary S₃ calculation
places the residual-fixed local summand in the seed and fixes it under the
full first actor. The contrary triple fixes the seed under the full opposite
actor; their generation gives global component fixation. The quotient
comparison accounts for D_alpha using two-perfect commutator idempotence.

The conclusion restricts both denominators to the local span; it does not
identify their entire ambient subgroups or require natural-module coordinates.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(3), printed p.906,
and the intrinsic fixed denominator of (1.7), printed pp.847--848.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The exact intrinsic-denominator comparison on the incident local span.
Both full incident actors fix its residual-fixed summand modulo `Z_alpha`,
so the given section kernel restricts to the global component-fixed kernel.
The passage through `D_alpha` is included in the quotient comparison. -/
theorem sectionKernel_subgroupOf_eq
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d)
    (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    (sectionKernel source i).subgroupOf (RankOnePairing.localGenerated
      (RankOnePairing.localParabolic (Quotient.extension source (representative source i d hd)) i)
      (Quotient.seed source i d)) =
    (Quotient.fixed source i d hd).subgroupOf (RankOnePairing.localGenerated
      (RankOnePairing.localParabolic (Quotient.extension source (representative source i d hd)) i)
      (Quotient.seed source i d)) := by
  obtain ⟨hseed, hfirst⟩ := local_fixed_summand source geometry common early i hkernel d hd
  exact sectionKernel_subgroupOf_eq_of_local_fixed_summand
    source geometry common early i hkernel d hd htriple hseed hfirst

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
