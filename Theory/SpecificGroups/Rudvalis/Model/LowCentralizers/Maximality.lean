module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.TwoPartBound

/-!
# Maximality of the literal Rudvalis max6 subgroup

The certified order of max6 and the ambient two-part bound give odd index.
Any maximal proper overgroup therefore belongs to the odd-index cover.
It cannot be isomorphic to max4: 245760 does not divide 344064. If it is
isomorphic to max6, inclusion and equal finite order make it equal to max6.

The second theorem supplies this cover from the checked radical-normalizer
classification, retaining triviality of the ambient two-core and nontriviality
of the intrinsic two-cores of odd-index maximal subgroups as explicit inputs.
The Chapter K low-centralizer consumer discharges both inputs from its source
hypotheses and the earlier certified two-normalizer generation theorem.

Source: GLS3 Table 5.3r; Aschbacher, Overgroups of Sylow subgroups in sporadic
groups (1986), as used in Aschbacher--Smith, printed p.511; Guralnick--Malle,
Classification of 2F-modules I, Proposition 5.1, Ru paragraph, manuscript p.17.
-/

public section

open Subgroup
namespace Rudvalis.LowCentralizers
open SylowOvergroups

theorem max6_odd_index : ¬ 2 ∣ max6.index := by
  intro h
  apply RadicalCoverage.SylowCertificate.not_two_pow_fifteen_dvd_card_model
  have hd : 2^15 ∣ Nat.card max6 * max6.index := by
    rw [max6_card]
    obtain ⟨k, hk⟩ := h
    exact ⟨15*k, by rw [hk]; ring⟩
  rwa [max6.card_mul_index] at hd

theorem max6_isCoatom_of_oddIndexMaximalCover (hcover : OddIndexMaximalCover) :
    IsCoatom max6 := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨RadicalCoverage.max6_ne_top, ?_⟩
  intro N hN hle
  obtain ⟨M, hM, hNM⟩ := (eq_top_or_exists_le_coatom N).resolve_left hN
  have h6M := hle.trans hNM
  have hodd : ¬ 2 ∣ M.index := fun h =>
    max6_odd_index (h.trans (index_dvd_of_le h6M))
  have hcard : Nat.card max6 ∣ Nat.card M := card_dvd_of_le h6M
  rcases hcover M hM hodd with h4 | h6
  · obtain ⟨e⟩ := h4
    rw [Nat.card_congr e.toEquiv, max6_card, max4_card] at hcard
    norm_num at hcard
  · obtain ⟨e⟩ := h6
    have he : max6 = M := eq_of_le_of_card_ge h6M
      (Nat.card_congr e.toEquiv).le
    exact hNM.trans he.ge

theorem max6_isCoatom_of_twoCore (hG : pCore 2 Model = ⊥)
    (hcore : OddIndexMaximalTwoCore) : IsCoatom max6 :=
  max6_isCoatom_of_oddIndexMaximalCover
    (oddIndexMaximalCover_of_twoCore_of_radicalCover hG hcore oddIndexMaximalRadicalCover)
end Rudvalis.LowCentralizers
