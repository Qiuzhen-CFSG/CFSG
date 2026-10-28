module

public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.GroupTheory.PrimeRankCentralCover
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs

/-!
# The faithful-image reduction for the sporadic branch of B.1.13

The source section need not be faithful on its quasisimple actor. Its actual
image is quasisimple, acts faithfully and irreducibly on the same space, and
has the same simple central quotient. Its full linear normalizer is literally
unchanged. Thus exclusions for faithful actions on the twenty-six concrete
sporadic central quotients suffice for the original section.

`FaithfulExclusion` in the definitions module is an explicit, still-to-be-proved representation
contract for an individual concrete carrier. The theorem in this module only
performs the faithful-image reduction; it does not assert those twenty-six
exclusions or the source theorem. In particular it assumes neither SQTK nor
a generalized-Fitting description of the full normalizer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.1.13, printed pp.73–74 / PDF pp.84–85. The source
cites Guralnick–Malle, *Classification of 2F-modules, II*, Table 2,
DOI 10.1515/9783110198126.117; its predecessor is *Classification of
2F-modules, I*, DOI 10.1016/S0021-8693(02)00526-4. No result from either
paper is assumed as an axiom or encoded as an already-proved classification.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- The literal sporadic source setup supplies an involution whose displacement
is bounded by the two-rank of the automorphism group of the actual named
carrier. Perfect central-quotient descent justifies using that simple model,
even for a central cover acting nonfaithfully on the original section. -/
theorem sporadic_offender_involution
    {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W) (hirr : σ.IsIrreducible)
    (hk : σ.ker ≤ center L) (hspor : KnownSimple.IsSporadicCarrier (L ⧸ center L))
    (hff : IsFFModule (normalizerRepresentation σ)) :
    ∃ name : KnownSimple.SporadicName,
      Nonempty (L ⧸ center L ≃* name.Carrier) ∧
      ∃ t : linearNormalizer σ, t ≠ 1 ∧ t ^ 2 = 1 ∧
        fixedCodim (normalizerRepresentation σ) (zpowers t) ≤
          primeRank 2 (MulAut name.Carrier) := by
  obtain ⟨name, ⟨e⟩⟩ := hspor
  let : Finite name.Carrier := Finite.of_surjective e e.surjective
  let := actionImage_quasisimple_of_central_kernel σ hk
  let e' := (simpleQuotientEquivImage σ hk).symm.trans e
  have hr := automorphism_primeRank_le_quotient_center (E := actionImage σ) 2
  rw [primeRank_equiv 2 (MulAut.congr e')] at hr
  obtain ⟨t, ht, ht2, hd⟩ := exists_small_displacement_involution σ hirr hff
  exact ⟨name, ⟨e⟩, t, ht, ht2, hd.trans hr⟩

/-- An individual faithful-action exclusion applies to a section with central
kernel. The actual quotient equivalence is transported through the image,
and the full-normalizer FF premise is preserved on the same vector space. -/
theorem not_ff_of_faithful_exclusion (name : KnownSimple.SporadicName)
    (hexclude : FaithfulExclusion.{v,v} name)
    {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W) (hirr : σ.IsIrreducible)
    (hk : σ.ker ≤ center L) (he : Nonempty (L ⧸ center L ≃* name.Carrier)) :
    ¬ IsFFModule (normalizerRepresentation σ) := by
  let := actionImage_quasisimple_of_central_kernel σ hk
  have he' : Nonempty (actionImage σ ⧸ center (actionImage σ) ≃* name.Carrier) :=
    ⟨(simpleQuotientEquivImage σ hk).symm.trans he.some⟩
  have hn := hexclude (imageRepresentation σ) (imageRepresentation_injective σ)
    (imageRepresentation_isIrreducible σ hirr) he'
  exact fun hff => hn ((isFFModule_normalizer_imageRepresentation_iff σ).mpr hff)

/-- Final catalogue assembly, conditional on all twenty-six faithful exclusions.
This theorem retains their discharge as an explicit prerequisite. The two-core
hypothesis of B.1.13 is not needed for this particular reduction. -/
theorem not_ff_of_all_faithful_exclusions
    (hexclude : ∀ name, FaithfulExclusion.{v,v} name)
    {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W) (hirr : σ.IsIrreducible)
    (hk : σ.ker ≤ center L) (hspor : KnownSimple.IsSporadicCarrier (L ⧸ center L)) :
    ¬ IsFFModule (normalizerRepresentation σ) := by
  obtain ⟨name, he⟩ := hspor
  exact not_ff_of_faithful_exclusion name (hexclude name) σ hirr hk he

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
