module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Ranks
public import Theory.Representation.BinaryPermutation.SevenParabolic.Residual
public import Theory.ElementaryAbelian.BinaryQuotientRank
public import Theory.Representation.BinaryOffender.Basic
import Mathlib.Tactic
/-!
# The seven-point transvection and rank contradiction

The source fixed-space and transvection identities, together with dimension
at least two, supply a single displacement orthogonal to its center. Hence
the distinguished vector has weight four. The complementary even plane is
invariant and disjoint from the distinguished line. Transvection shape and
the fixed-space identity make its intersection with E zero; the commutator
bound then makes X fix this plane pointwise, so |X| ≤ 4.

The point centralizer has three-rank two. The separately supplied earlier
source implication therefore makes Z nontrivial. Isotropy gives dim(E) ≤ 3,
while dim(E) + dim(X/Z) = 5 forces |X/Z| ≥ 4, contradicting |X| ≤ 4.
The quotient is the actual relative quotient, not a formal rank difference.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
12.8.11(1–5) and the proof of 12.8.13(6), printed pp.854, 856–857.
-/

public section
open Module Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace BinaryPermutation.SevenParabolic

/-- The exact module contradiction, retaining the quotient X/Z and the single
transvection displacement. The force premise is the independent earlier-source
implication about the conjugate center, not the A₇ exclusion. -/
theorem exclude
    {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 7)) (hf : Function.Injective f)
    (hAlt : alternatingGroup (Fin 7) ≤ f.range)
    (T X Z : Subgroup A) [IsElementaryAbelian 2 X]
    (hXT : X ≤ T) (hZX : Z ≤ X)
    (E : Submodule (ZMod 2) Space) (v : Space) (hv : v ≠ 0)
    (hT : ∀ t ∈ T, action (f t) v = v)
    (hiso : ∀ e ∈ E, ∀ w ∈ E, pairing e w = 0)
    (htrans : ∀ x ∈ X, ∀ e ∈ E,
      action (f x) e - e ∈ Submodule.span (ZMod 2) {v})
    (hfixed : E ⊓ fixedSpace (action.comp f) X = Submodule.span (ZMod 2) {v})
    (hcomm : ∀ x ∈ X, ∀ w, pairing v w = 0 → action (f x) w - w ∈ E)
    (hrank : finrank (ZMod 2) E +
      finrank (ZMod 2) (Additive (X ⧸ Z.subgroupOf X)) = 5)
    (hforce : 1 < primeRank 3 ((pointStabilizer v).comap f) → Z ≠ ⊥) : False := by
  have hcardX : Nat.card X ≤ 8 :=
    (primeRank_le_iff_elementary_card_le A).mp (actor_twoRank_le f hf) X inferInstance
  have hcardQ : Nat.card (X ⧸ Z.subgroupOf X) =
      2 ^ finrank (ZMod 2) (Additive (X ⧸ Z.subgroupOf X)) := by
    rw [Nat.card_congr (Additive.ofMul : (X ⧸ Z.subgroupOf X) ≃ _)]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (X ⧸ Z.subgroupOf X)))
  have hqle : finrank (ZMod 2) (Additive (X ⧸ Z.subgroupOf X)) ≤ 3 := by
    have hc : Nat.card (X ⧸ Z.subgroupOf X) ≤ Nat.card X :=
      Nat.le_of_dvd Nat.card_pos (Z.subgroupOf X).index_dvd_card
    rw [hcardQ] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hc.trans hcardX)
  have hdim : 2 ≤ finrank (ZMod 2) E := by omega
  have hvE : v ∈ E := by
    have h : v ∈ E ⊓ fixedSpace (action.comp f) X := by
      rw [hfixed]; exact Submodule.subset_span (by simp)
    exact h.1
  have hnle : ¬ E ≤ Submodule.span (ZMod 2) {v} := by
    intro h
    have hh := Submodule.finrank_mono h
    rw [finrank_span_singleton hv] at hh
    omega
  obtain ⟨e, he, hne⟩ := SetLike.not_le_iff_exists.mp hnle
  have hm : ∃ x : X, action (f x) e ≠ e := by
    by_contra! hm
    apply hne
    rw [← hfixed]
    exact ⟨he, hm⟩
  obtain ⟨x, hx⟩ := hm
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (htrans x x.property e he)
  have hc1 : c = 1 := by
    have hb : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hb c with hz | ho
    · rw [hz, zero_smul] at hc
      exact (hx (sub_eq_zero.mp hc.symm)).elim
    · exact ho
  have hsingle : action (f x) e - e = v := by simpa only [hc1, one_smul] using hc.symm
  have hw : weight v = 4 := weight_four_of_displacement (f x) v e hv (hiso e he v hvE) hsingle
  have hZ : Z ≠ ⊥ := hforce (actor_point_threeRank_gt_one f hf hAlt v hw)
  have hdis : Disjoint (plus v) E := by
    apply Submodule.disjoint_def.mpr
    intro w hwp hwE
    have hwfix : w ∈ fixedSpace (action.comp f) X := by
      intro a
      have hd : action (f a) w - w ∈ plus v :=
        (plus v).sub_mem (plus_invariant v (f a) (hT a (hXT a.property)) w hwp) hwp
      have hz := Submodule.disjoint_def.mp (plus_disjoint_line v) _ hd
        (htrans a a.property w hwE)
      exact sub_eq_zero.mp hz
    have hwl : w ∈ Submodule.span (ZMod 2) {v} := by
      rw [← hfixed]; exact ⟨hwE, hwfix⟩
    exact Submodule.disjoint_def.mp (plus_disjoint_line v) _ hwp hwl
  have hcentral : ∀ x : X, ∀ w ∈ plus v, action (f x) w = w := by
    intro x w hw
    have hd : action (f x) w - w ∈ plus v :=
      (plus v).sub_mem (plus_invariant v (f x) (hT x (hXT x.property)) w hw) hw
    have he := hcomm x x.property w (plus_orthogonal v w hw)
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hdis _ hd he)
  let C := T ⊓ (plusFixer v).comap f
  have hXC : X ≤ C := by
    intro x hx
    exact ⟨hXT hx, hT x (hXT hx), hcentral ⟨x, hx⟩⟩
  let j : X →* C := Subgroup.inclusion hXC
  have hj : Function.Injective j := Subgroup.inclusion_injective hXC
  let : IsElementaryAbelian 2 j.range :=
    IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hsmall : Nat.card X ≤ 4 := by
    have hh := (primeRank_le_iff_elementary_card_le C).mp
      (actor_planeCentralizer_twoRank_le f hf T v hw) j.range inferInstance
    rwa [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv] at hh
  have hEbound := isotropic_finrank_le E hiso
  have hQbound : 2 ≤ finrank (ZMod 2) (Additive (X ⧸ Z.subgroupOf X)) := by omega
  have hqcard : 4 ≤ Nat.card (X ⧸ Z.subgroupOf X) := by
    rw [hcardQ]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hQbound
  have hzcard : 2 ≤ Nat.card (Z.subgroupOf X) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv]
    exact (Subgroup.one_lt_card_iff_ne_bot (H := Z)).mpr hZ
  have hp := (Z.subgroupOf X).card_mul_index
  rw [Subgroup.index_eq_card] at hp
  nlinarith
end BinaryPermutation.SevenParabolic
