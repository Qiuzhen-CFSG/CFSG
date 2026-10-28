module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry

/-!
# Irreducibility of the even point core under the literal A₄ residual

The three nonidentity double transpositions are permuted transitively by
the cubic (012). Hence every nontrivial subgroup of the actual even point
core normalized by A₄ is the full four-group. The four-word certificate
avoids enumeration of the ambient symmetric group.

Source: Aschbacher–Smith,13.5.14(2), printed p.919.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.EvenPointCoreNormal
private def a : S := swap01 * swap23
private def b : S := Equiv.swap 0 2 * Equiv.swap 1 3
private def word (i : Fin 4) : S := ![1,a,b,a*b] i
private theorem a_mem : a ∈ pointCoreEven := by
  refine ⟨?_,by change Equiv.Perm.sign a = 1; decide +kernel⟩
  rw [pointCore_eq_closure]
  exact subset_closure (by simp [a])
private theorem b_mem : b ∈ pointCoreEven := by
  refine ⟨?_,by change Equiv.Perm.sign b = 1; decide +kernel⟩
  rw [pointCore_eq_closure]
  exact subset_closure (by simp [b])
private theorem word_mem (i : Fin 4) : word i ∈ pointCoreEven := by
  fin_cases i
  · exact one_mem _
  · exact a_mem
  · exact b_mem
  · exact mul_mem a_mem b_mem
private theorem word_surjective : ∀h∈pointCoreEven, ∃i,word i=h := by
  let f : Fin 4 → pointCoreEven := fun i => ⟨word i,word_mem i⟩
  have hi : Function.Injective f := by
    intro i j he
    have hh : word i 0 = word j 0 := congrArg (fun h:pointCoreEven=>h.val 0) he
    exact (by decide +kernel : ∀i j:Fin 4,word i 0=word j 0 → i=j) i j hh
  have hb := hi.bijective_of_nat_card_le (by rw [pointCoreEven_card,Nat.card_fin])
  intro h hh
  obtain ⟨i,he⟩ := hb.2 ⟨h,hh⟩
  exact ⟨i,congrArg Subtype.val he⟩

/-- The literal even four-group has no proper nontrivial A₄-invariant subgroup. -/
theorem eq_pointCore_of_normalized (A : Subgroup S) (hA : A ≤ pointCoreEven)
    (hne : A ≠ ⊥) (hn : K ≤ normalizer (A : Set S)) : A = pointCoreEven := by
  apply le_antisymm hA
  obtain ⟨x,hx,hx1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  obtain ⟨i,hi⟩ := word_surjective x (hA hx)
  have hi0 : i ≠ 0 := by
    intro he
    subst i
    exact hx1 (show x ∈ (⊥:Subgroup S) from hi.symm)
  intro y hy
  by_cases hy1 : y=1
  · exact hy1 ▸ A.one_mem
  obtain ⟨j,hj⟩ := word_surjective y hy
  have hj0 : j ≠ 0 := by intro he; subst j; exact hy1 hj.symm
  have cert : ∀i j:Fin 4,i≠0 → j≠0 → ∃k:Fin 3,
      cycle012^k.val*word i*(cycle012^k.val)⁻¹=word j := by decide +kernel
  obtain ⟨k,hk⟩ := cert i j hi0 hj0
  have hc : cycle012^k.val ∈ K := K.pow_mem (by decide +kernel) _
  have hh := (mem_normalizer_iff.mp (hn hc) x).mp hx
  rw [←hi,hk,hj] at hh
  exact hh

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.EvenPointCoreNormal
end
