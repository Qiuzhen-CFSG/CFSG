module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.SourceInputs
public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import Theory.Representation.BinaryIrreducibleRank
public import Theory.SpecificGroups.OddThreeRank.Automorphisms
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# The actual-actor reduction for the PSU₃ branch of K.2

Schur's lemma and faithful central descent bound the ambient two-rank by
three. Inside the component, the central quotient is injective on elementary
two-subgroups, so their rank is at most two. No covering-group classification
or assertion about the full linear normalizer is used.

The degree and conjugate-generation inputs give p(p−1) ≤ 30, leaving p=5
besides the desired p=3. At five, four conjugates give degree at most 24.
The outer-displacement input forces a small actor into L; its rank is then
at most two, giving degree at most 16 against the lower bound 20.

This completes the numerical and transport part of Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, as used on printed p.453
of Aschbacher–Smith. The three explicitly named source inputs remain
obligations: the conditional theorem below is not the unconditional K.2
parameter restriction.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped ENNReal

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]

/-- The actual K.2 group has two-rank at most three, including all outer actors. -/
theorem source_actor_rank_le_three {p : ℕ} (h : SourceHypotheses ρ L p) :
    primeRank 2 G ≤ 3 := by
  let : L.Normal := h.fitting ▸ (inferInstance : (generalizedFitting G).Normal)
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h.quotient
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    e.symm.isSimpleGroup
  have hr := automorphism_primeRank_le_quotient_center (E := L) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  exact (BinaryIrreducibleCentralizer.primeRank_le_automorphisms ρ L h.faithful).trans
    (hr.trans (Theory.SpecificGroups.OddThreeRank.psu3_automorphism_two_rank_le_three
      J h.prime h.odd hcard hconj))

omit [IsQuasisimple L] in
/-- An elementary two-subgroup inside the actual cover has rank at most two.
The binary irreducible action removes the central kernel on this subgroup. -/
theorem source_inner_actor_rank_le_two {p : ℕ} (h : SourceHypotheses ρ L p)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAL : A ≤ L) : rank A ≤ 2 := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h.quotient
  let S := BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite S := Finite.of_surjective e e.surjective
  let f : A →* S := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center L)).comp (inclusion hAL))
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro a ha
    apply Subtype.ext
    apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one ρ L h.faithful
    · exact elemPow_eq_one_of_isElementaryAbelian (a : G) a.property
    · have he : e ((QuotientGroup.mk' (center L)) (inclusion hAL a)) = 1 := ha
      have hc : inclusion hAL a ∈ center L :=
        (QuotientGroup.eq_one_iff _).mp (e.injective (he.trans (map_one e).symm))
      apply mem_centralizer_iff.mpr
      intro l hl
      exact congrArg L.subtype ((mem_center_iff.mp hc) ⟨l, hl⟩)
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le S).mp
    (Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le
      J h.prime h.odd hcard hconj) f.range he
  have hsize : Nat.card A ≤ 2 ^ 2 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).le.trans hc
  have hh := Nat.log_mono_right (b := 2) hsize
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

/-- A source cubic actor contains an actual ambient involution moving at most
six binary dimensions; this does not place that involution inside L. -/
theorem source_small_involution {p : ℕ} (h : SourceHypotheses ρ L p)
    (hq : cubicRatio ρ ≤ 2) :
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧ fixedCodim ρ (zpowers t) ≤ 6 := by
  exact exists_small_involution_of_cubicRatio_le ρ
    (source_actor_rank_le_three ρ L h) hq

/-- Source K.2 assembly from the independent degree, generation and
PSU₃(5) outer-displacement inputs. Final discharge remains with this owner. -/
theorem source_parameter_eq_three_of_inputs
    (hdegree : PrimeDegreeBound.{u, v})
    (hconjugates : SourceConjugateBounds.{u, v})
    (houter : SourceFiveOuterDisplacement.{u, v})
    {p : ℕ} (h : SourceHypotheses ρ L p) (hq : cubicRatio ρ ≤ 2) : p = 3 := by
  by_contra hp3
  have hp2 : p ≠ 2 := by
    have ho := h.odd
    rintro rfl
    norm_num at ho
  have hpge := h.prime.two_le
  have hpgt : 3 < p := by omega
  have hd := hdegree ρ L h hpgt
  obtain ⟨hfive, hfour⟩ := hconjugates ρ L h hpgt
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hr := source_actor_rank_le_three ρ L h
  have hd30 : Module.finrank (ZMod 2) V ≤ 30 :=
    finrank_le_of_cubicRatio_conjugates ρ L h.faithful h.irreducible hr hfive hq
  have hp6 : p ≤ 6 := by
    have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    nlinarith
  have hp5 : p = 5 := by
    have hprime := h.prime
    interval_cases p <;> first | rfl | norm_num at hprime
  subst p
  have hgen := hfour rfl
  have hd24 : Module.finrank (ZMod 2) V ≤ 24 :=
    finrank_le_of_cubicRatio_conjugates ρ L h.faithful h.irreducible hr hgen hq
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp hq
  have hAL : A ≤ L := by
    intro t ht
    by_contra htL
    obtain ⟨ht2, ht6⟩ := involution_fixedCodim_le_of_mem_small_actor ρ hA hr hsmall ht
    have ht7 := houter ρ L h hd hd24 t htL ht2
    omega
  have hrA := source_inner_actor_rank_le_two ρ L h hA hAL
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  obtain ⟨g, hg⟩ := hgen t ht1 ht2
  have ht4 : fixedCodim ρ (zpowers t) ≤ 4 := by
    have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
      intro v hv a
      exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
    have hdim := Submodule.finrank_mono hle
    have hdimA := fixedCodim_add_finrank ρ A
    have hdimt := fixedCodim_add_finrank ρ (zpowers t)
    omega
  have hd16 := finrank_le_mul_fixedCodim_of_conjugate_generation ρ L
    (fixedSpace_eq_bot_of_faithful_irreducible_on ρ L h.faithful h.irreducible) t g hg
  norm_num at hd
  omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
