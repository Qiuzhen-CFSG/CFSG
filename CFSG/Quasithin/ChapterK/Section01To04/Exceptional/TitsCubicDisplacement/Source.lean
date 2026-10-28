module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.InternalApplication
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.FiveDisplacement
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.BinaryCoverage
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.SmallDerivedCovers.Source

/-!
# The unconditional Tits cubic source exclusion

Complete involution coverage in the actual binary Ree carrier supplies both
the inner-automorphism reduction and the two marked root classes. The proved
five-local weight estimates and finite centralizer geometry then give strict
displacement greater than twice actor rank for every elementary actor in the
full linear normalizer. Transport retains the original ambient actor and
component representation. The perfect-cover comparison discharges the
original central-quotient model as well.

Source: Aschbacher--Smith K.3, printed p.457; Guralnick--Malle II, Lemma 8.8,
internal p.57. No involution coverage or displacement calculation is a premise.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
open Subgroup Representation Representation.BinaryOffender
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every elementary actor of the literal full normalizer has ratio above two. -/
theorem normalizer_displacement
    (σ : Representation (ZMod 2) Tits.ParrottGroup V)
    (hi : IsIrreducible σ) (hf : Function.Injective σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A :=
  normalizer_displacement_of_local_calculations
    (ElementaryGeometry.localGeometry_of_coverage Tits.InvolutionRootGeometry.binaryInvolutionCoverage)
    Tits.InvolutionRootGeometry.binaryInvolutionCoverage σ hi hf
    (fiveKernel_fixedCodim_ge_twenty σ hf) (fiveInverter_fixedCodim_ge_twelve σ hf) A hA

/-- The original normal Tits component cannot act with cubic ratio at most two. -/
theorem source_exclusion
    {G : Type*} [Group G] [Finite G]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    [IsIrreducible (ρ.comp L.subtype)] (e : L ≃* Tits.ParrottGroup)
    (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2) : False := by
  apply tits_exclusion_of_cubic_displacement_bound ρ L e hf hc
  intro σ hi hσ A hA _
  exact normalizer_displacement σ hi hσ A hA

/-- Source central-quotient application, with the perfect cover identified
internally and the original representation and ambient actors unchanged. -/
theorem source_centralQuotient_exclusion
    {G : Type*} [Group G] [Finite G]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    [Group.IsPerfect L] [IsIrreducible (ρ.comp L.subtype)]
    (e : L ⧸ center L ≃* Tits.ParrottGroup)
    (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2) : False :=
  source_exclusion ρ L
    (ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.titsEquiv e) hf hc

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
