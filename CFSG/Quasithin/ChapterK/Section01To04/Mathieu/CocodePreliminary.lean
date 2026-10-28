module

public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.LinearSteps
public import Theory.Representation.BinaryOffender.UniformFixedSpace
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage

/-!
# The cocode cases of Lemma K.4.1

For a small actor of rank at most two, a nonidentity element must be in the
central involution class: the other class displaces five dimensions. Its fixed
space then coincides with the actor's fixed space. The checked pointwise
centralizer of that space is cyclic, contradicting the actor's required rank.
The M23 statement transports this argument through the native point embedding.

These statements apply to the actual cocode representations without any local
geometry hypotheses. The code cases still require their own fixed-space
centralizer calculation from H.16.2(5).
Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma K.4.1,
printed p.458.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Mathieu

open MathieuCode Sporadic.Mathieu MathieuCode.CocodeOctad.Involutions

/-- The M24 cocode part of K.4.1: a small actor has rank greater than two. -/
theorem m24_cocode_small_actor_rank (A : Subgroup M24) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim cocodeRepresentation A ≤ 2 * rank A) : 2 < rank A := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨x, hx, hx1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hx2 : orderOf x = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx) hx1
  have hle := ChapterE.fixedCodim_mono cocodeRepresentation (Subgroup.zpowers_le.mpr hx)
  rcases M24InvolutionCentralizers.involution_classes x hx2 with hz | ht
  · have hx4 := fixedCodim_of_isConj_z x hz
    by_contra! hr
    have heq : fixedCodim cocodeRepresentation A =
        fixedCodim cocodeRepresentation (Subgroup.zpowers x) := by omega
    have hfix := fixedSpace_eq_of_fixedCodim_eq cocodeRepresentation
      (Subgroup.zpowers_le.mpr hx) heq
    have hsub : A ≤ Subgroup.zpowers x := by
      rw [← pointwiseCentralizer_of_isConj_z x hz]
      intro a ha
      refine ⟨Subgroup.mem_top _, ?_⟩
      intro v hv
      rw [← hfix] at hv
      exact hv ⟨a,ha⟩
    have hcard := Subgroup.card_le_of_le hsub
    have hcyc : Nat.card (Subgroup.zpowers x) = 2 := (Nat.card_zpowers x).trans hx2
    have hpow := hA.card_eq_two_pow_rank
    have htwo : rank A = 2 := by omega
    rw [hcyc, hpow, htwo] at hcard
    omega
  · have hx5 := fixedCodim_of_isConj_t x ht
    omega

/-- The same calculation on the literal M23 restriction. -/
theorem m23_cocode_small_actor_rank (A : Subgroup M23) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim m23CocodeRepresentation A ≤ 2 * rank A) : 2 < rank A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hmap : IsElementaryTwo (A.map pointEmbedding) := by
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hb
    apply hA.1
    apply Subgroup.map_injective pointEmbedding_injective
    simpa using hb
  have hdim : fixedCodim cocodeRepresentation (A.map pointEmbedding) =
      fixedCodim m23CocodeRepresentation A := by
    unfold fixedCodim m23CocodeRepresentation
    rw [fixedSpace_comp_map]
  have h := m24_cocode_small_actor_rank (A.map pointEmbedding) hmap (by
    rw [hdim, rank_map_injective pointEmbedding pointEmbedding_injective]
    exact hsmall)
  simpa only [rank_map_injective pointEmbedding pointEmbedding_injective] using h

end CFSG.Quasithin.ChapterK.Mathieu
