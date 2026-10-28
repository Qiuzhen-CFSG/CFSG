module
public import Theory.GroupAction.HomomorphismFixedKernel
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.GroupTheory.CComponent.Basic

/-!
# Perfect actions on small equivariant kernels

A perfect group acts trivially on a set of at most four elements, since
its permutation image is solvable. For an equivariant homomorphism with a
two-group kernel of that size, the kernel of the quotient action fixes both
the kernel and the quotient. The subgroup-and-quotient automorphism theorem
then makes that action kernel a two-group whenever the original action has
a two-group kernel.

Source: the perfect-action step in Aschbacher--Smith 12.8.13 and 14.3.15,
printed pp.855--856 and 994.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupAction.PerfectSmallKernel
theorem fixes_small_equivariant_kernel
    {A P D : Type*} [Group A] [Group P] [Finite P] [Group D]
    [Group.IsPerfect A] (q : P →* D)
    (f : A →* MulAut P) (j : A →* MulAut D)
    (he : ∀ a x, q (f a x) = j a (q x))
    (hc : Nat.card q.ker ≤ 4) :
    ∀ (a : A) (x : q.ker), f a x = x := by
  classical
  let s : A →* Equiv.Perm q.ker := {
    toFun a := {
      toFun x := ⟨f a x, by rw [MonoidHom.mem_ker,he,x.property,map_one]⟩
      invFun x := ⟨f a⁻¹ x, by rw [MonoidHom.mem_ker,he,x.property,map_one]⟩
      left_inv x := by
        apply Subtype.ext
        change f a⁻¹ (f a x) = x
        rw [map_inv]
        exact (f a).symm_apply_apply x
      right_inv x := by
        apply Subtype.ext
        change f a (f a⁻¹ x) = x
        rw [map_inv]
        exact (f a).apply_symm_apply x }
    map_one' := by ext x; simp
    map_mul' a b := by ext x; simp }
  let : Fintype q.ker := Fintype.ofFinite _
  have hc' : Fintype.card q.ker ≤ Fintype.card (Fin 4) := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_fin] using hc
  let emb : q.ker ↪ Fin 4 := Classical.choice
    (Function.Embedding.nonempty_of_card_le hc')
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm q.ker) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective emb)
  let := Group.IsPerfect.range s
  have hs : Subsingleton s.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable s.range inferInstance
  intro a x
  have ha : s a = 1 := congrArg Subtype.val (Subsingleton.elim (s.rangeRestrict a) 1)
  exact congrArg Subtype.val (Equiv.congr_fun ha x)

theorem quotient_action_kernel_isPGroup
    {A P D : Type*} [Group A] [Group P] [Finite P] [Group D]
    [Group.IsPerfect A] (q : P →* D)
    (f : A →* MulAut P) (j : A →* MulAut D)
    (he : ∀ a x, q (f a x) = j a (q x))
    (hc : Nat.card q.ker ≤ 4) (hq : IsPGroup 2 q.ker)
    (hf : IsPGroup 2 f.ker) : IsPGroup 2 j.ker := by
  apply q.isPGroup_of_fixes_kernel_and_quotient hq (f.comp j.ker.subtype)
  · change IsPGroup 2 (f.ker.subgroupOf j.ker)
    exact hf.comap_subtype
  · intro a x
    change q (f a x) = q x
    rw [he,show j a = 1 from a.property]
    rfl
  · intro a x
    exact fixes_small_equivariant_kernel q f j he hc a x

end Theory.GroupAction.PerfectSmallKernel
