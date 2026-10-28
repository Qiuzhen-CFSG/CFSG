module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Small normal subgroups under a perfect action

A perfect subgroup acts trivially on a normal subgroup of order at most four:
its permutation image is both perfect and solvable. Consequently a nontrivial
commutator with a normal two-subgroup has order at least eight. If that
commutator were smaller, the three-subgroups lemma and perfectness would
make it trivial.

Source: the standard three-subgroups lemma and the solvability of S₄. This
is used for the intrinsic omega-center in Aschbacher–Smith C.1.31–34;
no pushing-up classification is used here.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- A perfect subgroup centralizes every normal subgroup of order at most four. -/
theorem le_centralizer_of_isPerfect_of_card_le_four (L M : Subgroup G)
    [Group.IsPerfect L] [M.Normal]
    (hM : Nat.card M ≤ 4) : L ≤ centralizer (M : Set G) := by
  classical
  let : Fintype M := Fintype.ofFinite M
  have hc : Fintype.card M ≤ Fintype.card (Fin 4) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hM
  let e : M ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm M) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let f : L →* Equiv.Perm M :=
    (MulAction.toPermHom (MulAut M) M).comp
      ((MulAut.conjNormal : G →* MulAut M).comp L.subtype)
  let := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  intro l hl m hm
  have hf : f ⟨l, hl⟩ = 1 := congrArg Subtype.val
    (Subsingleton.elim (f.rangeRestrict ⟨l, hl⟩) 1)
  have he := congrArg (fun a : Equiv.Perm M => (a ⟨m, hm⟩ : G)) hf
  change l * m * l⁻¹ = m at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- A nontrivial commutator of a normal two-subgroup with a normal perfect
subgroup has at least eight elements. No faithfulness assumption is needed. -/
theorem commutator_card_ge_eight_of_isPerfect (L V : Subgroup G)
    [Group.IsPerfect L] [L.Normal] [V.Normal]
    (hV : IsPGroup 2 V) (hne : ⁅V, L⁆ ≠ ⊥) :
    8 ≤ Nat.card (⁅V, L⁆ : Subgroup G) := by
  by_contra hnot
  have htwo : IsPGroup 2 (⁅V, L⁆ : Subgroup G) :=
    hV.to_le (commutator_le_left V L)
  obtain ⟨n, hn⟩ := htwo.exists_card_eq
  have hnlt : n < 3 := by
    by_contra hnge
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hnge)
    rw [← hn] at hh
    exact hnot hh
  have hsmall : Nat.card (⁅V, L⁆ : Subgroup G) ≤ 4 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) (by omega : n ≤ 2)
  have hcent : ⁅L, ⁅V, L⁆⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_of_isPerfect_of_card_le_four L ⁅V, L⁆ hsmall)
  have hsecond : ⁅⁅V, L⁆, L⁆ = ⊥ := by rwa [commutator_comm] at hcent
  have hthird : ⁅⁅L, V⁆, L⁆ = ⊥ := by rwa [commutator_comm L V]
  have hzero : ⁅⁅L, L⁆, V⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hthird hsecond
  apply hne
  simpa only [commutator_eq_self, commutator_comm L V] using hzero

end Subgroup
