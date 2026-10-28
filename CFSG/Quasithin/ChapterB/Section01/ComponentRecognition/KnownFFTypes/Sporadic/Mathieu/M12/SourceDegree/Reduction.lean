module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M12.SourceRecognition
public import Theory.Representation.BinaryOffender.CubicNormalizerDegree
public import Theory.Representation.BinaryOffender.CubicConjugateDimension
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.GroupTheory.PrimeRankAutomorphismOrder

/-!
# Reduction to a finite degree window for the source M₁₂ action

The literal source actor has two-rank at most four: its faithful irreducible
component action bounds this rank by that of Aut(M₁₂). Thus a cubic actor
attaining ratio at most two moves at most eight dimensions. Three-conjugate
generation on Aut(M₁₂), when supplied, bounds the original degree by 24.

The remaining representation input concerns ordinary faithful irreducible
binary representations of the concrete M₁₂ in degrees at most 24. The
centerless-cover equivalence transports the literal component restriction to
that group, retaining the original central-quotient marking. A gap between
degrees ten and 24 then gives the source degree bound and the existing marked
recognition consumer.

The generation and degree-gap assertions are explicit, independent premises
below; this module does not assert either missing assertion. In particular it
does not assert the unconditional Chapter K degree classification. The actual
actor alone has small cubic ratio, and no SQTK property of its full linear
normalizer is assumed.

Source: Aschbacher--Smith, Chapter K introduction, printed p.451, and K.4,
printed p.457 (1 March 2004 manuscript). The source cites Guralnick--Malle,
*Classification of 2F-modules, I*, Theorem 6.6 and Table 6.7. The conditional
route here isolates two finite M₁₂ calculations rather than assuming that
classification theorem.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M12Source
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open _root_.Sporadic.Mathieu
open Representation.MathieuSmall.M12Recognition

private theorem automorphism_rank_le_four : primeRank 2 (MulAut M12) ≤ 4 := by
  have ho : Nat.card (MulAut.Outer M12) ≤ 2 ^ 1 :=
    M12A5Fixer.Automorphisms.outerIndexBound
  exact (automorphism_primeRank_le_add_of_outer_card m12_center_eq_bot ho).trans
    (Nat.add_le_add_right m12_twoRank_le_three 1)

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : Hypotheses ρ)
  (e : (generalizedFitting G ⧸ center (generalizedFitting G)) ≃* M12)

include h e in
/-- The literal source group has two-rank at most four, before module recognition. -/
theorem source_primeRank_le_four : primeRank 2 G ≤ 4 := by
  let := h.quasisimple
  exact (primeRank_le_central_quotient_automorphisms ρ (generalizedFitting G)
    h.faithful h.irreducible e).trans automorphism_rank_le_four

include h e in
/-- The cubic minimum supplies a genuine elementary actor in G, of rank at most
four and fixed codimension at most eight. -/
theorem source_small_cubic_actor :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧ rank A ≤ 4 ∧
      fixedCodim ρ A ≤ 2 * rank A ∧ fixedCodim ρ A ≤ 8 := by
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_ratio
  have hr := hA.rank_le_of_primeRank_le (source_primeRank_le_four ρ h e)
  exact ⟨A, hA, hc, hr, hd, by omega⟩

include h e in
/-- The concrete three-conjugate geometry reduces the source classification to
binary degree at most 24. Its geometry premise is not yet discharged here. -/
theorem source_degree_le_twenty_four_of_threeConjugates
    (hgen : ThreeConjugateAutomorphisms M12) :
    Module.finrank (ZMod 2) V ≤ 24 := by
  let := h.quasisimple
  exact finrank_le_six_mul_of_cubic_central_quotient ρ (generalizedFitting G)
    h.faithful h.irreducible e hgen automorphism_rank_le_four h.cubic_ratio

include h e in
/-- Apply an ordinary M₁₂ degree-gap theorem to the marked component restriction.
Both finite model calculations remain explicit obligations of final assembly. -/
theorem source_degree_le_ten_of_threeConjugates_of_gap
    (hgen : ThreeConjugateAutomorphisms M12)
    (hgap : ∀ σ : Representation (ZMod 2) M12 V,
      Function.Injective σ → σ.IsIrreducible →
      Module.finrank (ZMod 2) V ≤ 24 → Module.finrank (ZMod 2) V ≤ 10) :
    Module.finrank (ZMod 2) V ≤ 10 := by
  let := h.quasisimple
  let σ : Representation (ZMod 2) (generalizedFitting G) V :=
    ρ.comp (generalizedFitting G).subtype
  have hf : Function.Injective σ := h.faithful.comp Subtype.val_injective
  let f := CentralCover.groupEquiv σ hf h.irreducible e
  let τ : Representation (ZMod 2) M12 V := σ.comp f.symm.toMonoidHom
  have ht : τ.IsIrreducible :=
    (Representation.irreducible_comp_surjective_iff f.symm.toMonoidHom
      f.symm.surjective σ).mpr h.irreducible
  exact hgap τ (hf.comp f.symm.injective) ht
    (source_degree_le_twenty_four_of_threeConjugates ρ h e hgen)

include h in
/-- Literal consumer application: the two model calculations give the existing
marked heart and ambient-extension output with the original quotient marking. -/
theorem source_recognition_of_threeConjugates_of_gap
    (hgen : ThreeConjugateAutomorphisms M12)
    (hgap : ∀ σ : Representation (ZMod 2) M12 V,
      Function.Injective σ → σ.IsIrreducible →
      Module.finrank (ZMod 2) V ≤ 24 → Module.finrank (ZMod 2) V ≤ 10) :
    Nonempty (Recognition ρ e) :=
  source_recognition_of_finrank_le_ten ρ h e
    (source_degree_le_ten_of_threeConjugates_of_gap ρ h e hgen hgap)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M12Source
