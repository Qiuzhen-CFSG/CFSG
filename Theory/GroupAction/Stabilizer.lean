module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MulAction

/-! Generic stabilizer facts used by the finite simple-group arguments. -/

theorem stabilizer_eq_bot_of_comap_eq_bot
    {G α : Type*} [Group G] [MulAction G α]
    (N : Subgroup G) (a : α)
    (hK : N.comap (MulAction.stabilizer G a).subtype = ⊥) :
    MulAction.stabilizer N a = ⊥ := by
  apply (MulAction.stabilizer N a).eq_bot_iff_forall.mpr
  intro n hn
  let h : MulAction.stabilizer G a := ⟨(n : G), hn⟩
  have hh : h ∈ N.comap (MulAction.stabilizer G a).subtype := n.property
  rw [hK] at hh
  have hh1 : h = 1 := Subgroup.mem_bot.mp hh
  apply Subtype.ext
  exact congrArg (fun z : MulAction.stabilizer G a => (z : G)) hh1

theorem card_eq_card_of_comap_stabilizer_eq_bot
    {G α : Type*} [Group G] [MulAction G α] [Finite α]
    (N : Subgroup G) [IsPretransitive N α]
    (a : α)
    (hK : N.comap (MulAction.stabilizer G a).subtype = ⊥) :
    Nat.card N = Nat.card α := by
  have hStab : MulAction.stabilizer N a = ⊥ :=
    stabilizer_eq_bot_of_comap_eq_bot N a hK
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer N a)
  rw [MulAction.index_stabilizer_of_transitive N a, hStab] at hmul
  simpa using hmul.symm

theorem eq_top_of_stabilizer_le
    {G α : Type*} [Group G] [MulAction G α]
    (N : Subgroup G) [IsPretransitive N α]
    (a : α)
    (hH : MulAction.stabilizer G a ≤ N) :
    N = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N a (g • a)
  let k : G := (n : G)⁻¹ * g
  have hkH : k ∈ MulAction.stabilizer G a := by
    change k • a = a
    dsimp [k]
    rw [mul_smul, inv_smul_eq_iff]
    exact hn.symm
  have hnN : (n : G) ∈ N := n.property
  have hkN : k ∈ N := hH hkH
  have hmul := N.mul_mem hnN hkN
  simpa [k] using hmul

end MulAction
