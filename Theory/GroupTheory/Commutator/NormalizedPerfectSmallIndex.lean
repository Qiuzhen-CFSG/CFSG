module
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.IsPerfect

/-!
# A perfect group centralizes normalized sections of order at most four

Conjugation on the literal section U/(C.subgroupOf U) gives a permutation
representation of L. Its image is perfect and embeds into the solvable
symmetric group on four letters, so it is trivial. The conclusion retains
the original ambient commutator and needs normality only inside U.

This is the elementary small-section argument used in the terminal
Aschbacher--Smith 13.1.7 configuration (printed p.876).
-/

public noncomputable section
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A perfect actor fixes a normalized section of order at most four. -/
theorem commutator_le_of_perfect_normalized_small_index
    (L U C : Subgroup G) [Group.IsPerfect L] [(C.subgroupOf U).Normal]
    (hLU : L ≤ normalizer (U : Set G)) (hLC : L ≤ normalizer (C : Set G))
    (hi : C.relIndex U ≤ 4) : ⁅U,L⁆ ≤ C := by
  classical
  let W := U ⧸ C.subgroupOf U
  let : Fintype W := Fintype.ofFinite W
  have hc : Fintype.card W ≤ Fintype.card (Fin 4) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using (show Nat.card W ≤ 4 by simpa only [relIndex, index_eq_card] using hi)
  let e : W ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm W) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action L U C hLU hLC inferInstance
  let f : L →* Equiv.Perm W := (MulAction.toPermHom (MulAut W) W).comp ρ
  let := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl u hu
  have hf : f ⟨l,hl⟩ = 1 := congrArg Subtype.val
    (Subsingleton.elim (f.rangeRestrict ⟨l,hl⟩) 1)
  have he := congrArg (fun a : Equiv.Perm W => a (QuotientGroup.mk' _ ⟨u,hu⟩)) hf
  change ρ ⟨l,hl⟩ (QuotientGroup.mk' _ ⟨u,hu⟩) = QuotientGroup.mk' _ ⟨u,hu⟩ at he
  rw [hρ] at he
  have hm := QuotientGroup.eq_iff_div_mem.mp he
  change l*u*l⁻¹/u ∈ C at hm
  simpa only [div_eq_mul_inv,commutatorElement_def] using hm

end Subgroup
