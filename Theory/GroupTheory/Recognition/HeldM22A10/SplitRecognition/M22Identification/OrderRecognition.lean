module

public import Theory.GroupTheory.Recognition.HeldM22A10.Setup
public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.CentralizerModels
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CaseII
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData

/-!
# The order step in M22 centralizer recognition

The ambient order calculation in Janko's Lemma 14 remains to be proved from
the local data. The elementary step following that lemma is established here:
at order 443520, a Sylow three-normalizer cannot have order 144, because
its index would be 3080, contrary to the Sylow congruence. Thus the two
normalizer orders allowed by Lemma 8 reduce to 72.

Both the ambient order and the Lemma 8 alternative are explicit hypotheses
of this intermediate result. No centralizer-recognition theorem is asserted
until those premises have been discharged.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1–19, Section 7, p.15,
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The order-144 alternative contradicts the number-of-Sylows congruence. -/
public theorem sylowThreeNormalizer_card_ne_144 (hG : Nat.card G = 443520)
    (P : Sylow 3 G) : Nat.card (normalizer (P : Set G)) ≠ 144 := by
  intro hN
  have hc := (normalizer (P : Set G)).card_mul_index
  rw [hN, hG] at hc
  have hi : (normalizer (P : Set G)).index = 3080 := by omega
  have hm := card_sylow_modEq_one 3 G
  rw [P.card_eq_index_normalizer, hi] at hm
  norm_num [Nat.ModEq] at hm

/-- The normalizer conclusion after the ambient order and local alternatives
have actually been established. -/
public theorem sylowThreeNormalizer_card_of_order (hG : Nat.card G = 443520)
    (P : Sylow 3 G)
    (hN : Nat.card (normalizer (P : Set G)) = 72 ∨
      Nat.card (normalizer (P : Set G)) = 144) :
    Nat.card (normalizer (P : Set G)) = 72 :=
  hN.resolve_right (sylowThreeNormalizer_card_ne_144 hG P)

end Theory.GroupTheory.HeldM22A10.M22Identification
