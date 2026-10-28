module

public import Theory.GroupAction.FiveSixteenCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Point stabilizers for a normal five on sixteen elements

A faithful automorphism group of a group of order sixteen, containing a
normal five-group, has point stabilizers of order dividing four away from
the identity. Conjugation embeds each such stabilizer in Aut(C5): an element
in its kernel centralizes the five, so its fixed subgroup is five-invariant,
and irreducibility makes that element trivial.
-/

public section
open Subgroup MulAction
namespace Theory.GroupAction
variable {H V : Type*} [Group H] [Finite H] [Group V] [Finite V]
  [MulDistribMulAction H V] [FaithfulSMul H V]

/-- The literal point stabilizer embeds in the automorphism group of the
normal five and consequently has order dividing four. -/
theorem card_point_stabilizer_dvd_four_of_normal_five
    (P : Subgroup H) [P.Normal] (hP : Nat.card P = 5) (hV : Nat.card V = 16)
    (v : V) (hv : v ≠ 1) : Nat.card (stabilizer H v) ∣ 4 := by
  have hnot : FixedPoints.subgroup P V ≠ ⊤ := by
    intro htop
    have hbot : P = ⊥ := by
      apply bot_unique
      intro p hp
      apply mem_bot.mpr
      apply eq_of_smul_eq_smul (α := V)
      intro w
      have hw : w ∈ FixedPoints.subgroup P V := htop ▸ mem_top w
      simpa only [Subgroup.smul_def, one_smul] using hw ⟨p, hp⟩
    rw [hbot, card_bot] at hP
    omega
  have hfixed := fixed_eq_bot_of_five_action_card_sixteen hP hV hnot
  have hfree (c : H) (hc : c ∈ centralizer (P : Set H)) (hcv : c • v = v) : c = 1 := by
    let D := FixedPoints.subgroup (zpowers c) V
    have hD (w : V) : w ∈ D ↔ c • w = w := by
      constructor
      · intro hw
        exact hw ⟨c, mem_zpowers c⟩
      · intro hw k
        exact smul_eq_self_of_mem_zpowers k.property hw
    have hcomm (p : P) (w : V) : c • ((p : H) • w) = (p : H) • (c • w) := by
      rw [← mul_smul, ← mul_smul]
      exact congrArg (fun a : H => a • w) ((mem_centralizer_iff.mp hc) p p.property).symm
    let : IsInvariant P V D := ⟨by
      intro p w
      rw [hD, hD]
      change c • w = w ↔ c • ((p : H) • w) = (p : H) • w
      rw [hcomm]
      exact (smul_left_cancel_iff (p : H)).symm⟩
    rcases invariant_eq_bot_or_top_of_five_actor hP hV hfixed D with hz | ht
    · exact (hv (mem_bot.mp (hz ▸ (hD v).mpr hcv))).elim
    · apply eq_of_smul_eq_smul (α := V)
      intro w
      simpa only [one_smul] using (hD w).mp (ht ▸ mem_top w)
  let A := stabilizer H v
  let f : A →* MulAut P := MulAut.conjNormal.comp A.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    apply Subtype.ext
    apply hfree a ?_ a.property
    intro p hp
    have he := congrArg (fun α : MulAut P => (α ⟨p, hp⟩ : H)) (MonoidHom.mem_ker.mp ha)
    change (a : H)*p*(a : H)⁻¹ = p at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hc : Nat.card (MulAut P) = 4 := by
    rw [IsCyclic.card_mulAut, hP]
    decide
  exact hc ▸ card_dvd_of_injective f hf

end Theory.GroupAction
