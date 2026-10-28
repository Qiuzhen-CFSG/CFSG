module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.LinearBudget
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore
public import Theory.GroupAction.ElementaryTwoOddHyperplane
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration

/-!
# Invariant lines and noncentralized hyperplanes in D.2.14

Coprime hyperplane generation detects a nontrivial core centralizer. The
preceding D.2.13 hypothesis makes it an invariant line of order three.
For any such line, its actor centralizer is the exact order-two hyperplane
and has the supplied two-dimensional fixed-space support. If the whole
actor fixed that hyperplane's fixed space, its full commutator with the
line would fix the space too, contradicting that support dimension.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.14, printed p.186, the paragraphs preceding (+) and (++).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
open Representation.BinaryOffender Subgroup
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The centralizer of an invariant line is the exact hyperplane from D.2.13. -/
theorem Reduced.invariant_line_hyperplane {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z) :
    let B := A ⊓ centralizer (Z : Set G)
    Nat.card B = 2 ∧ rank B = 1 ∧ P ⊓ centralizer (B : Set G) = Z ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ B) Z) = 2 :=
  ElementaryCore.line_fixed_support ρ P A Z h.card_actor hZ.1 hZ.2.1 hZ.2.2
    h.common_centralizer h.hyperplane_support

/-- The core has an invariant order-three line detected by a hyperplane. -/
theorem Reduced.exists_invariant_line {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) : ∃ Z : Subgroup G, IsInvariantLine P A Z := by
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  let : P.Normal := h.normal
  have hn : A ≤ normalizer (P : Set G) := by rw [normalizer_eq_top]; exact le_top
  have hPn : P ≠ ⊥ := by
    intro he
    have hc := h.card_core
    rw [he, card_bot] at hc
    rcases h.rank_cases with hs | hs <;> norm_num [hs] at hc
  obtain ⟨B, _, hBA, hi, hD⟩ := exists_hyperplane_containing_of_odd_centralizer
    A P ⊥ hn (h.card_core ▸ (by decide : Odd 3).pow) hPn bot_le
    (by intro p hp b hb; have hb1 : b = 1 := hb; simp [hb1]) h.common_centralizer
  have hBc : Nat.card B = 2 := by
    have hc := (B.subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv] at hc
    change Nat.card B * B.relIndex A = Nat.card A at hc
    rw [hi, h.card_actor] at hc
    omega
  have hr : rank B = 1 := by simp only [rank, hBc]; decide
  refine ⟨P ⊓ centralizer (B : Set G), inf_le_left,
    (h.hyperplane_support B hBA hr hD).1, ?_⟩
  have hc : A ≤ centralizer (B : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hBA)
  intro a ha
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨(mem_normalizer_iff.mp (hn ha) x).mp hx.1,
      (centralizer (B : Set G)).mul_mem
        ((centralizer (B : Set G)).mul_mem (hc ha) hx.2)
        ((centralizer (B : Set G)).inv_mem (hc ha))⟩
  · intro hx
    have hp := (mem_normalizer_iff.mp (hn (A.inv_mem ha)) (a * x * a⁻¹)).mp hx.1
    have hq := (centralizer (B : Set G)).mul_mem
      ((centralizer (B : Set G)).mul_mem ((centralizer (B : Set G)).inv_mem (hc ha)) hx.2)
      (hc ha)
    exact ⟨by simpa [mul_assoc] using hp, by simpa [mul_assoc] using hq⟩

/-- Trivial common centralizer makes each invariant line its full A-commutator. -/
theorem Reduced.invariant_line_commutator {P A Z : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hZ : IsInvariantLine P A Z) : ⁅Z, A⁆ = Z := by
  have hfix : Z ⊓ centralizer (A : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hZ.1).trans_eq h.common_centralizer)
  exact ElementaryCore.commutator_eq Z A
    (IsPGroup.of_card (n := 1) (by simpa using hZ.2.1))
    h.card_actor hZ.2.2 hfix

/-- A line's hyperplane fixed space cannot be fixed by the whole actor. -/
theorem Reduced.invariant_line_moved_hyperplane [FiniteDimensional (ZMod 2) V]
    {P A Z : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
    (hZ : IsInvariantLine P A Z) :
    subspaceCommutator ρ (fixedSpace ρ (A ⊓ centralizer (Z : Set G))) A ≠ ⊥ := by
  intro he
  have hfix := (subspaceCommutator_eq_bot_iff ρ _ A).mp he
  have hZB : Z ≤ centralizer ((A ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) :=
    le_centralizer_iff.mp inf_le_right
  have hs := fixedSpace_invariant_normalizer ρ (hZB.trans (centralizer_le_normalizer _))
  have hf := le_fixedSpace_commutator_of_invariant ρ hs hfix
  rw [h.invariant_line_commutator ρ hZ] at hf
  have hz := (subspaceCommutator_eq_bot_iff ρ _ Z).mpr hf
  have hd := (h.invariant_line_hyperplane ρ hZ).2.2.2
  rw [hz, finrank_bot] at hd
  omega

/-- The actual reduced action supplies the noncentralized hyperplane witness. -/
theorem Reduced.exists_moved_hyperplane [FiniteDimensional (ZMod 2) V]
    {P A : Subgroup G} {s : ℕ} (h : Reduced ρ P A s) :
    ∃ B : Subgroup G, B ≤ A ∧ rank B = 1 ∧
      subspaceCommutator ρ (fixedSpace ρ B) A ≠ ⊥ := by
  obtain ⟨Z, hZ⟩ := h.exists_invariant_line ρ
  exact ⟨A ⊓ centralizer (Z : Set G), inf_le_left,
    (h.invariant_line_hyperplane ρ hZ).2.1, h.invariant_line_moved_hyperplane ρ hZ⟩

/-- The strict ratio lower bound is derived from the original local action. -/
theorem Reduced.one_lt_cubicRatio [FiniteDimensional (ZMod 2) V]
    {P A : Subgroup G} {s : ℕ} (h : Reduced ρ P A s) : 1 < cubicRatio ρ := by
  obtain ⟨B, hBA, hrB, hm⟩ := h.exists_moved_hyperplane ρ
  exact h.one_lt_ratio_of_moved_hyperplane ρ hBA hrB hm

end CFSG.Quasithin.ChapterD.FittingConfigurations
