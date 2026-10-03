module

public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# Sylow five-subgroups from a small Frattini action

For a finite group of characteristic two, a two-core Frattini quotient of
order at most 32 forces every nontrivial Sylow five-subgroup to have order
five. The canonical Frattini action has two-group kernel, and the orders
of GL(n,2), for n ≤ 5, have five-part at most five.

This is the standard Burnside Frattini-action argument; no solvability or
ambient Sylow hypothesis is required.
-/

namespace Subgroup

/-- Five occurs only once in the automorphism order of binary space of
order at most 32. -/
public theorem not_twentyfive_dvd_card_mulAut_of_elementary_two_card_le
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V ≤ 32) : ¬ 25 ∣ Nat.card (MulAut V) := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hnle : n ≤ 5 := by
    by_contra h
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ n)
    rw [← hn] at hp
    norm_num at hp
    omega
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow V n hn]
  interval_cases n <;> decide

/-- A nontrivial Sylow five-subgroup has order five when the self-centralizing
two-core has at most five Frattini generators. -/
public theorem five_sylow_card_of_characteristic_two_frattini_card_le
    {G : Type*} [Group G] [Finite G]
    (hcentral : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hV : Nat.card (pCore 2 G ⧸ frattini (pCore 2 G)) ≤ 32)
    (hdiv : 5 ∣ Nat.card G) (P : Sylow 5 G) : Nat.card P = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Q := pCore 2 G
  let V := Q ⧸ frattini Q
  let _ : Fact (IsPGroup 2 Q) := ⟨pCore_isPGroup⟩
  let _ : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini (p := 2)
  let action := (quotientAut (frattini Q)).comp (MulAut.conjNormal : G →* MulAut Q)
  have hk : action.ker = Q := pCore_frattini_action_kernel 2 hcentral
  have hdis : Disjoint (P : Subgroup G) Q :=
    IsPGroup.disjoint_of_ne 5 2 (by decide) _ _ P.isPGroup' pCore_isPGroup
  let restriction := action.comp (P : Subgroup G).subtype
  have hinj : Function.Injective restriction := by
    apply (MonoidHom.ker_eq_bot_iff restriction).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdis a.property (hk ▸ ha)
  have hPdiv : Nat.card P ∣ Nat.card (MulAut V) := card_dvd_of_injective restriction hinj
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra hnot
    exact not_twentyfive_dvd_card_mulAut_of_elementary_two_card_le hV
      (dvd_trans (Nat.pow_dvd_pow 5 (by omega : 2 ≤ n)) (hn ▸ hPdiv))
  have hne : Nat.card P ≠ 1 := by
    intro h
    exact (Sylow.ne_bot_of_dvd_card P hdiv) (Subgroup.card_eq_one.mp h)
  interval_cases n
  · exact (hne (by simpa using hn)).elim
  · simpa using hn

end Subgroup
