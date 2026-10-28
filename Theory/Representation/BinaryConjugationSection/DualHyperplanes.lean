module

public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryOffender.DualDisplacement
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# A common commutator line on dual sections

A faithful actor of binary rank at least two cannot fix subspaces of
codimension at most one in both a module and its dual: the displacement
embedding bounds its rank by the product of those two codimensions.
For literal conjugation sections with a common kernel, a subgroup of
index at most two supplies those hyperplanes. If all commutators lie in
a subgroup of order two, that subgroup must lie in one of the two supports.

Source: the final hyperplane argument of Aschbacher--Smith 14.6.24(3),
printed p.1041. No component classification or numerical certificate is
assumed here. All fixed-space bounds come from the marked sections.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

omit [Finite X] in
/-- A literal subgroup of index at most two gives fixed codimension at
most one on the specified quotient action. -/
theorem fixedCodim_le_one_of_fixed_index
    (H W Z A B : Subgroup G) (σ : Representation (ZMod 2) X V) (π : H →* X)
    (c : BinaryConjugationSection H W Z (σ.comp π))
    (hBW : B ≤ W) (hZB : Z ≤ B) (hcomm : ⁅A,B⁆ ≤ Z)
    (hindex : B.relIndex W ≤ 2) : fixedCodim σ ((A.subgroupOf H).map π) ≤ 1 := by
  let : Finite V := Finite.of_surjective (fun w : W => (c.coordinates w).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hfix : c.imageSpace B ≤ fixedSpace σ ((A.subgroupOf H).map π) := by
    intro v hv a
    obtain ⟨aH,ha,he⟩ := a.property
    change σ (a : X) v = v
    rw [← he]
    exact c.fixed_on_imageSpace_of_commutator_le A B hcomm aH ha v hv
  have hdim := Submodule.finrank_mono hfix
  have hsum := fixedCodim_add_finrank σ ((A.subgroupOf H).map π)
  have hpos : B.relIndex W ≠ 0 := (B.subgroupOf W).index_ne_zero_of_finite
  have hi : B.relIndex W = 1 ∨ B.relIndex W = 2 := by omega
  rcases hi with hi | hi
  · have hc := c.imageSpace_codimension_of_index B hBW hZB 0 (by simpa using hi)
    omega
  · have hc := c.imageSpace_codimension_of_index B hBW hZB 1 (by simpa using hi)
    omega

omit [Finite G] [Finite X] in
private theorem line_inf_eq_bot (C W : Subgroup G) (hc : Nat.card C = 2)
    (hn : ¬ C ≤ W) : C ⊓ W = ⊥ := by
  let : Fact (Nat.card C).Prime := ⟨hc ▸ Nat.prime_two⟩
  rcases (W.subgroupOf C).eq_bot_or_eq_top_of_prime_card with hh | hh
  · apply le_bot_iff.mp
    intro x hx
    have hm : (⟨x,hx.1⟩ : C) ∈ W.subgroupOf C := hx.2
    rw [hh] at hm
    exact congrArg Subtype.val (mem_bot.mp hm)
  · exact (hn (fun x hx =>
      (show (⟨x,hx⟩ : C) ∈ W.subgroupOf C from hh ▸ mem_top _))).elim

/-- A common commutator line must lie in one of two genuinely dual
supports when a rank-two actor acts across a subgroup of index two. -/
theorem line_le_one_of_dual_supports
    (H U Z A D C W Wdual : Subgroup G)
    (σ : Representation (ZMod 2) X V) (hσ : Function.Injective σ) (π : H →* X)
    (c : BinaryConjugationSection H W Z (σ.comp π))
    (cdual : BinaryConjugationSection H Wdual Z (σ.dual.comp π))
    (hAH : A ≤ H) (hWU : W ≤ U) (hWdualU : Wdual ≤ U) (hZD : Z ≤ D)
    (hindex : D.relIndex U ≤ 2) (hrank : 2 ≤ rank ((A.subgroupOf H).map π))
    (hC : Nat.card C = 2) (hcomm : ⁅A,D⁆ ≤ C) :
    C ≤ W ∨ C ≤ Wdual := by
  let : Finite V := Finite.of_surjective (fun w : W => (c.coordinates w).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  by_contra hn
  push Not at hn
  have hzero (S : Subgroup G) (hS : H ≤ normalizer (S : Set G))
      (hnot : ¬ C ≤ S) : ⁅A,D ⊓ S⁆ ≤ Z := by
    have hCS : C ⊓ S = ⊥ := line_inf_eq_bot C S hC hnot
    have hs : ⁅A,D ⊓ S⁆ ≤ S :=
      (commutator_mono le_rfl inf_le_right).trans
        (le_normalizer_iff_commutator_le_right.mp (hAH.trans hS))
    have hc : ⁅A,D ⊓ S⁆ ≤ C :=
      (commutator_mono le_rfl inf_le_left).trans hcomm
    exact (le_inf hc hs).trans (hCS.le.trans bot_le)
  have hidx (S : Subgroup G) (hS : S ≤ U) : (D ⊓ S).relIndex S ≤ 2 := by
    rw [inf_relIndex_right]
    exact (relIndex_le_of_le_right hS
      (show D.relIndex U ≠ 0 from (D.subgroupOf U).index_ne_zero_of_finite)).trans hindex
  have hn₁ := fixedCodim_le_one_of_fixed_index H W Z A (D ⊓ W) σ π c
    inf_le_right (le_inf hZD c.kernel_le) (hzero W c.normalized hn.1) (hidx W hWU)
  have hn₂ := fixedCodim_le_one_of_fixed_index H Wdual Z A (D ⊓ Wdual) σ.dual π cdual
    inf_le_right (le_inf hZD cdual.kernel_le)
    (hzero Wdual cdual.normalized hn.2) (hidx Wdual hWdualU)
  have hb := rank_le_fixedCodim_mul_dual σ hσ ((A.subgroupOf H).map π)
  have hm := Nat.mul_le_mul hn₁ hn₂
  omega

end Representation.BinaryConjugationSection
