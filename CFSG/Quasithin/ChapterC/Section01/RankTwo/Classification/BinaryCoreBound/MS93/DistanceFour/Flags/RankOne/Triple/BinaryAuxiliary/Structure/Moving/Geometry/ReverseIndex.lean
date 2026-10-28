module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Crossing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Nontrivial
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained

/-!
# The reverse midpoint comparison on MS93 p.907

The original selected second layer meets Z_middle in exactly Z_beta.
If the transported second layer escapes the original opposite core, an
index-two coset calculation proves the reverse comparison. Independently,
the source nonzero triple and the genuine S3 quotient make the right-hand
index at least two at every selected escaping actor.

When the transported second layer lies in the original opposite core, the
derived edge bound and the actual first-core nonquadraticity bound the left
index by two. Combining these branches with the genuine midpoint Sylow
selection proves the requested incident actor's reverse comparison. The
conditional assembly is retained, and its remaining premise is discharged
in `exists_reverse_middle_comparison`.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907,
first paragraph. Both original Z-denominators are preserved.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Assembly of the incident selection and the reverse comparison, conditional
only on the left-hand bound in the contained-second-layer branch. -/
theorem exists_reverse_middle_comparison_of_contained_bound
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i)
    (hcontained : ∀ e : M, flagIncident source i 1 e →
      secondFlagLayer source i p.delta0 ≤
        (localFlagActor source (!i) e).map (middleTransport p).conjugation.toMonoidHom →
      ¬ secondFlagLayer source i p.delta0 ≤
        (localFlagKernel source (!i) e).map (middleTransport p).conjugation.toMonoidHom →
      (secondFlagLayer source i e).map (middleTransport p).conjugation.toMonoidHom ≤
        localFlagKernel source (!i) p.delta0 →
      (Z R (alpha R)).relIndex
        ⁅secondFlagLayer source i p.delta0,
          (Y source i e).map (middleTransport p).conjugation.toMonoidHom⁆ ≤ 2) :
    ∃ e : M, flagIncident source i 1 e ∧
      secondFlagLayer source i p.delta0 ≤
        (localFlagActor source (!i) e).map (middleTransport p).conjugation.toMonoidHom ∧
      ¬ secondFlagLayer source i p.delta0 ≤
        (localFlagKernel source (!i) e).map (middleTransport p).conjugation.toMonoidHom ∧
      (Z R (alpha R)).relIndex
        ⁅secondFlagLayer source i p.delta0,
          (Y source i e).map (middleTransport p).conjugation.toMonoidHom⁆ ≤
      (Z R p.middle).relIndex
        ⁅secondFlagLayer source i p.delta0,
          (secondFlagLayer source i e).map (middleTransport p).conjugation.toMonoidHom⁆ := by
  let t := middleTransport p
  obtain ⟨e, he, hactor, hescape⟩ :=
    exists_middle_actor source geometry common.large_distance i hkernel p t
  refine ⟨e, he, hactor, hescape, ?_⟩
  by_cases hc : (secondFlagLayer source i e).map t.conjugation.toMonoidHom ≤
      localFlagKernel source (!i) p.delta0
  · exact (hcontained e he hactor hescape hc).trans
      (middle_second_commutator_index_ge_two source geometry common early
        i hkernel p t e hactor hescape)
  · exact reverse_comparison_of_second_core_escape source geometry common early
      i hkernel p t e hc

/-- The incident actor and reverse commutator-index comparison in the first
paragraph of MS93 p.907, with the original Z_alpha and Z_middle denominators.
The contained-layer bound is proved from the source inputs, so no comparison
or moving-factor premise remains. -/
theorem exists_reverse_middle_comparison
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i) :
    ∃ e : M, flagIncident source i 1 e ∧
      secondFlagLayer source i p.delta0 ≤
        (localFlagActor source (!i) e).map (middleTransport p).conjugation.toMonoidHom ∧
      ¬ secondFlagLayer source i p.delta0 ≤
        (localFlagKernel source (!i) e).map (middleTransport p).conjugation.toMonoidHom ∧
      (Z R (alpha R)).relIndex
        ⁅secondFlagLayer source i p.delta0,
          (Y source i e).map (middleTransport p).conjugation.toMonoidHom⁆ ≤
      (Z R p.middle).relIndex
        ⁅secondFlagLayer source i p.delta0,
          (secondFlagLayer source i e).map (middleTransport p).conjugation.toMonoidHom⁆ := by
  exact exists_reverse_middle_comparison_of_contained_bound source geometry common early
    i hkernel p (contained_middle_left_index_le_two source geometry common hb early
      i hkernel natural p)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
