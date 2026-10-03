module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic
/-!
# Odd actions and central involutions in a self-centralizing two-core

When the two-core is self-centralizing, every odd subgroup acts faithfully
on it by conjugation: the kernel lies in both the odd subgroup and the two-core.
A central involution belongs to the core and is fixed by the full conjugation
action. These elementary facts supply actual automorphisms and a common fixed
involution for coprime-action arguments, including Thompson VI, printed p.630.
-/

namespace Subgroup

/-- Odd subgroups act faithfully on a self-centralizing two-core. -/
public theorem odd_subgroup_conj_twoCore_injective
    {G : Type*} [Group G] [Finite G]
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (H : Subgroup G) (hodd : Nat.Coprime 2 (Nat.card H)) :
    Function.Injective ((MulAut.conjNormal : G →* MulAut (pCore 2 G)).comp H.subtype) := by
  let K := pCore 2 G
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  have hd : Disjoint H K := disjoint_of_coprime_natCard (by
    rw [hn]
    exact hodd.symm.pow_right n)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply Subtype.ext
  apply hd.le_bot
  refine ⟨x.property, hchar ?_⟩
  intro k hk
  have he := congrArg (fun f : MulAut K => (f ⟨k, hk⟩ : G))
    (show MulAut.conjNormal (x : G) = (1 : MulAut K) from hx)
  change (x : G) * k * (x : G)⁻¹ = k at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- A central involution supplies the literal common fixed involution in the core. -/
public theorem exists_twoCore_central_involution
    {G : Type*} [Group G] [Finite G]
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (y : G) (hy : y ∈ center G) (hy2 : orderOf y = 2) :
    ∃ k : pCore 2 G, (k : G) = y ∧ orderOf k = 2 ∧
      ∀ g : G, (MulAut.conjNormal : G →* MulAut (pCore 2 G)) g k = k := by
  have hyK : y ∈ pCore 2 G := hchar (fun g _ => mem_center_iff.mp hy g)
  refine ⟨⟨y, hyK⟩, rfl, ?_, ?_⟩
  · simpa only [← orderOf_coe] using hy2
  · intro g
    apply Subtype.ext
    change g * y * g⁻¹ = y
    rw [mem_center_iff.mp hy g, mul_inv_cancel_right]

end Subgroup
