module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Targets
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.SourceData
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Escape.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Escape.FixedPreimage

/-!
# The two auxiliary escapes in MS93 (4.6.8)

Assuming the p.907 local structure, X cannot lie in the midpoint core:
`Escape.Geometry` turns that containment into a contradiction to the
chosen first-actor triple. The same module identifies the printed product
X Q_middle with the subgroup join using relative normalization inside
Q_beta, and derives the endpoint commutator bound from containment of Y.
`Escape.FixedPreimage` then forces D = U, contradicting the nontrivial
natural factor X/Z_alpha. Thus both escapes follow with every intermediate
premise discharged; the p.907 local structure remains an explicit input.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.908.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Conditional assembly through the fixed-preimage calculation.
The first escape and the antecedent of that calculation are discharged here;
`auxiliaryEscapes` supplies the calculation from the natural-section data. -/
theorem auxiliaryEscapes_of_endpoint_fixed_preimage
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i)
    (hlocal : ∀ d : M, flagIncident source i 1 d → Nonempty (LocalStructure source i d))
    (hfixed : ∀ d : M, flagIncident source i 1 d →
      ¬ Z R p.endpoint ≤ localFlagKernel source (!i) d →
      Y source i d ≤ X source i d ⊔ Q R p.middle →
      ⁅Y source i d,Z R p.endpoint⁆ ≤ Z R p.middle ⊔ X source i d →
      D source i d = secondFlagLayer source i d)
    (d : M) (hd : flagIncident source i 1 d)
    (hE : ¬ Z R p.endpoint ≤ localFlagKernel source (!i) d) :
    (¬ X source i d ≤ Q R p.middle) ∧
      (¬ Y source i d ≤ X source i d ⊔ Q R p.middle) := by
  obtain ⟨s⟩ := hlocal d hd
  refine ⟨X_not_le_middle_kernel source geometry common hb early i hkernel p d hd s hE, ?_⟩
  intro hY
  exact s.D_ne_second geometry common.large_distance
    (hfixed d hd hE hY
      (Y_endpoint_commutator_le_of_contained source geometry hb early i hkernel p d hd hY))

/-- Both auxiliary escapes in the final paragraph of MS93 (4.6.8), p.908,
from the explicit p.907 local structure and the original natural section. -/
theorem auxiliaryEscapes
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (hlocal : ∀ d : M, flagIncident source i 1 d → Nonempty (LocalStructure source i d))
    (d : M) (hd : flagIncident source i 1 d)
    (hE : ¬ Z R p.endpoint ≤ localFlagKernel source (!i) d) :
    (¬ X source i d ≤ Q R p.middle) ∧
      (¬ Y source i d ≤ X source i d ⊔ Q R p.middle) := by
  exact auxiliaryEscapes_of_endpoint_fixed_preimage source geometry common hb early i
    hkernel p hlocal
    (D_eq_second_of_endpoint_bound source geometry common hb early i hkernel natural p hlocal)
    d hd hE

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
