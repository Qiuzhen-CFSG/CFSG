module
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# Centralization on a normalized quotient of order at most two

If P normalizes subgroups U and Z and the supplied quotient U/(Z∩U)
has at most two elements, then [U,P] lies in Z. The quotient normality
witness is kept as an explicit parameter, and no containment U≤P is
required.

The literal quotient-conjugation homomorphism is trivial because every
automorphism of a group with at most two elements fixes every element.
Applying its representative formula and the quotient kernel criterion
places every commutator in Z.

This source-neutral fact supplies the small quotient step in the final
central auxiliary argument of Stellmacher (9.4), printed p.52.
-/

namespace Subgroup
open scoped commutatorElement
universe u

private theorem mulAut_eq_one_of_card_le_two {W : Type*} [Group W] [Finite W]
    (hcard : Nat.card W ≤ 2) (a : MulAut W) : a = 1 := by
  by_cases hone : Nat.card W ≤ 1
  · let _ := Finite.card_le_one_iff_subsingleton.mp hone
    apply MulEquiv.ext
    intro w
    exact Subsingleton.elim _ _
  · have htwo : Nat.card W = 2 := by omega
    obtain ⟨z,_hzne,huniq⟩ := (Nat.card_eq_two_iff' (1:W)).mp htwo
    apply MulEquiv.ext
    intro w
    change a w = w
    by_cases hw : w = 1
    · simpa only [hw] using a.map_one
    · have ha : a w ≠ 1 := fun heq => hw (a.injective (heq.trans a.map_one.symm))
      exact (huniq _ ha).trans (huniq _ hw).symm

public theorem commutator_le_of_normalized_quotient_card_le_two
    {G : Type u} [Group G] [Finite G]
    (P U Z : Subgroup G)
    (hPU : P ≤ normalizer (U:Set G)) (hPZ : P ≤ normalizer (Z:Set G))
    (hN : (Z.subgroupOf U).Normal) :
    let _ := hN
    Nat.card (U ⧸ Z.subgroupOf U) ≤ 2 → ⁅U,P⁆ ≤ Z := by
  let _ := hN
  dsimp only
  intro hcard
  obtain ⟨action,hact⟩ := exists_quotient_conjugation_action P U Z hPU hPZ hN
  rw [commutator_comm]
  apply commutator_le.mpr
  intro p hp u hu
  have htrivial := mulAut_eq_one_of_card_le_two hcard (action ⟨p,hp⟩)
  have hfix := hact ⟨p,hp⟩ ⟨u,hu⟩
  rw [htrivial] at hfix
  have hmember := QuotientGroup.eq_iff_div_mem.mp hfix.symm
  change p*u*p⁻¹/u ∈ Z at hmember
  simpa only [div_eq_mul_inv,commutatorElement_def] using hmember

end Subgroup
