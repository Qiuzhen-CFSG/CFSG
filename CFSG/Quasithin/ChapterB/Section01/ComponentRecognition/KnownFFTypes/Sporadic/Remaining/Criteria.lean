module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Remaining.Defs

/-!
# Criteria for quantitative sporadic normalizer exclusions

The FF condition supplies a nonidentity involution of displacement at most the
automorphism two-rank of the actual simple quotient. A strict displacement
bound contradicts it. Alternatively, a degree lower bound and generation by
conjugates give the strict displacement bound by intersecting fixed spaces.

All model bounds remain explicit here. This module does not yet assert the
eight exclusions for He, Fi₂₂, Fi₂₃, Fi₂₄′, HN, Th, B and M. Their quantitative
producers must account for arbitrary central covers, outer normalizer elements,
and the exact carriers in `CFSG.KnownSimple.SporadicCarriers`.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74 / PDF pp.84–85, and its
reference to Guralnick–Malle, *Classification of 2F-modules, II*, Table 2,
DOI 10.1515/9783110198126.117.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Remaining
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- The fixed-space argument supplies displacement bounds from actual cover degrees and generation. -/
theorem displacementBound_of_degree_and_conjugates
    (name : KnownSimple.SporadicName) (r k d : ℕ)
    (hdegree : DegreeBound.{u,v} name d)
    (hgen : ConjugateGenerationBound.{u,v} name k) (hgap : k * r < d) :
    DisplacementBound.{u,v} name r := by
  intro L W _ _ _ _ _ _ σ hf hi he t ht ht2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  obtain ⟨g, hg⟩ := hgen σ hf hi he t ht ht2
  have hupper := finrank_le_card_mul_fixedCodim_of_conjugates
    (normalizerRepresentation σ) (normalizerActor σ)
    (fixedSpace_normalizerActor_eq_bot σ hf hi) t g hg
  have hupper' : Module.finrank (ZMod 2) W ≤
      k * fixedCodim (normalizerRepresentation σ) (zpowers t) := by
    simpa only [Fintype.card_fin] using hupper
  have hlower := hdegree σ hf hi he
  by_contra! hle
  exact (not_lt_of_ge (hlower.trans (hupper'.trans (Nat.mul_le_mul_left k hle)))) hgap

/-- A quantitative contract can be supplied by the degree route, with every premise explicit. -/
theorem involutionBounds_of_degree_and_conjugates
    (name : KnownSimple.SporadicName) (r k d : ℕ)
    (hrank : RankBound.{u} name r) (hdegree : DegreeBound.{u,v} name d)
    (hgen : ConjugateGenerationBound.{u,v} name k) (hgap : k * r < d) :
    InvolutionBounds.{u,v} name :=
  ⟨r, hrank, displacementBound_of_degree_and_conjugates name r k d hdegree hgen hgap⟩

/-- Apply the quantitative bounds to the literal `FaithfulExclusion` source contract. -/
theorem faithfulExclusion_of_involutionBounds
    (name : KnownSimple.SporadicName) (hb : InvolutionBounds.{u,v} name) :
    FaithfulExclusion.{u,v} name := by
  obtain ⟨r, hr, hd⟩ := hb
  intro L W _ _ _ _ _ _ σ hf hi he
  have hk : σ.ker ≤ center L := by
    rw [(MonoidHom.ker_eq_bot_iff σ).mpr hf]
    exact bot_le
  exact not_ff_of_central_quotient_displacement σ hi hk he.some r
    (hr he) (hd σ hf hi he)

/-- Direct source application of the FF degree bound, retaining the genuine model inputs. -/
theorem faithfulExclusion_of_degree_and_conjugates
    (name : KnownSimple.SporadicName) (r k d : ℕ)
    (hrank : RankBound.{u} name r) (hdegree : DegreeBound.{u,v} name d)
    (hgen : ConjugateGenerationBound.{u,v} name k) (hgap : k * r < d) :
    FaithfulExclusion.{u,v} name := by
  intro L W _ _ _ _ _ _ σ hf hi he hff
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hk : σ.ker ≤ center L := by
    rw [(MonoidHom.ker_eq_bot_iff σ).mpr hf]
    exact bot_le
  have hr := (primeRank_actionImage_le_central_quotient σ hk he.some).trans (hrank he)
  have hu := finrank_le_of_ff_normalizer_conjugates σ hf hi k r hr
    (hgen σ hf hi he) hff
  exact (not_lt_of_ge ((hdegree σ hf hi he).trans hu)) hgap

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Remaining
