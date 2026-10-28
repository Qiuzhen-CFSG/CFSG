module

public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Centralizers of five-subgroups acting faithfully on sixteen elements

Let a finite group H act faithfully by automorphisms on a group V of order
sixteen, and let A be a subgroup of H of order five. The centralizer of A
in H has order dividing fifteen. The original action and faithfulness
instances are retained; V need not be abelian or elementary abelian.

Faithfulness makes the A action nontrivial. Orbit counting makes its fixed
subgroup trivial, and every A-invariant subgroup is trivial or full. For an
actor centralizing A, its fixed subgroup is A-invariant. If it contains a
nonidentity point, it is therefore all of V, so faithfulness makes the actor
the identity. The centralizer consequently acts freely on the fifteen
nonidentity elements, and the orbit decomposition proves the divisibility.

This source-neutral finite-action argument supplies the centralizer bound
for the normal five-subgroup of a terminal full-centralizer quotient. It
uses the proved five-action orbit arguments in FiveActionMinimalOrder and
FiveOnSixteenIrreducible, and the ordinary free-action orbit decomposition.
-/

open MulAction

namespace Subgroup

/-- The centralizer of a five-subgroup in a faithful action on sixteen elements
has order dividing fifteen. -/
public theorem card_centralizer_five_dvd_fifteen
    {H V : Type*} [Group H] [Finite H] [Group V] [Finite V]
    [MulDistribMulAction H V] [FaithfulSMul H V]
    (A : Subgroup H) (hA : Nat.card A = 5) (hV : Nat.card V = 16) :
    Nat.card (centralizer (A : Set H)) ∣ 15 := by
  classical
  have hnot : FixedPoints.subgroup A V ≠ ⊤ := by
    intro htop
    have hbot : A = ⊥ := by
      apply eq_bot_iff.mpr
      intro a ha
      apply mem_bot.mpr
      apply eq_of_smul_eq_smul (α := V)
      intro v
      have hv : v ∈ FixedPoints.subgroup A V := htop ▸ mem_top v
      simpa only [Subgroup.smul_def, one_smul] using hv ⟨a, ha⟩
    rw [hbot, card_bot] at hA
    omega
  have hfixed := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen hA hV hnot
  let C := centralizer (A : Set H)
  have hfree (c : C) (v : V) (hv : v ≠ 1) (hcv : (c : H) • v = v) : c = 1 := by
    let D : Subgroup V := FixedPoints.subgroup (zpowers (c : H)) V
    have hD (x : V) : x ∈ D ↔ (c : H) • x = x := by
      constructor
      · intro hx
        exact hx ⟨c, mem_zpowers (c : H)⟩
      · intro hx k
        exact smul_eq_self_of_mem_zpowers k.property hx
    have hcomm (a : A) (x : V) :
        (c : H) • ((a : H) • x) = (a : H) • ((c : H) • x) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      exact ((mem_centralizer_iff.mp c.property) a a.property).symm
    let _ : IsInvariant A V D := ⟨by
      intro a x
      rw [hD, hD]
      change (c : H) • x = x ↔ (c : H) • ((a : H) • x) = (a : H) • x
      rw [hcomm]
      exact (smul_left_cancel_iff (a : H)).symm⟩
    rcases invariant_eq_bot_or_top_of_five_actor hA hV hfixed D with hbot | htop
    · exact (hv (mem_bot.mp (hbot ▸ (hD v).mpr hcv))).elim
    · apply Subtype.ext
      apply eq_of_smul_eq_smul (α := V)
      intro x
      simpa only [Subgroup.coe_one, one_smul] using (hD x).mp (htop ▸ mem_top x)
  let X := {v : V // v ≠ 1}
  let _ : MulAction C X := {
    smul c v := ⟨(c : H) • (v : V), by
      intro heq
      apply v.property
      apply (MulDistribMulAction.toMulAut H V (c : H)).injective
      simpa using heq⟩
    one_smul v := by apply Subtype.ext; exact one_smul H (v : V)
    mul_smul c d v := by apply Subtype.ext; exact mul_smul (c : H) (d : H) (v : V) }
  have hstab (v : X) : stabilizer C v = ⊥ := by
    apply eq_bot_iff.mpr
    intro c hc
    exact mem_bot.mpr (hfree c v v.property (congrArg Subtype.val hc))
  have hcount := Nat.card_congr (selfEquivOrbitsQuotientProd (G := C) (X := X) hstab)
  rw [Nat.card_prod] at hcount
  have hX : Nat.card X = 15 := by
    let _ : Fintype V := Fintype.ofFinite V
    change Nat.card {v : V // ¬v = 1} = 15
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, hV]
    simp
  rw [hX] at hcount
  exact ⟨Nat.card (Quotient (orbitRel C X)), by simpa only [Nat.mul_comm] using hcount⟩

end Subgroup
