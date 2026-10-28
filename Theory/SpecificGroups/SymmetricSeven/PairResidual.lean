module
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Two-perfect groups normalizing a transposition

The normalizer of the transposition preserves its two-letter support. Its
action on that pair has two-group image and is therefore trivial on every
two-perfect subgroup. This gives the local residual calculation used in
Aschbacher–Smith 4.3.7, printed p.616.
-/

public section
open Subgroup Equiv
namespace Equiv.Perm

/-- A two-perfect permutation group normalizing a transposition fixes its
 two letters individually. -/
theorem twoPerfect_normalizes_swap_fixes
    {α : Type*} [Fintype α] [DecidableEq α] (i j : α) (hij : i ≠ j)
    (X : Subgroup (Perm α)) (hp : IsPPerfect 2 X)
    (hn : X ≤ normalizer (zpowers (swap i j) : Set (Perm α))) :
    ∀ x ∈ X, ∀ a ∈ ({i,j} : Set α), x a = a := by
  classical
  have hc : X ≤ centralizer (zpowers (swap i j) : Set (Perm α)) :=
    hn.trans (normalizer_le_centralizer_of_card_two _ (by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by simp [pow_two]) (by simpa using hij)))
  let P : SubMulAction X α := {
    carrier := {i,j}
    smul_mem' := by
      intro x a ha
      have hne : swap i j a ≠ a := swap_apply_ne_self_iff.mpr ⟨hij,by simpa using ha⟩
      have he := congrArg (fun f : Perm α => f a)
        (hc x.property (swap i j) (mem_zpowers _))
      change swap i j (x.val a) = x.val (swap i j a) at he
      have hm : swap i j (x.val a) ≠ x.val a := by
        rw [he]
        exact fun hh => hne (x.val.injective hh)
      change x.val a ∈ ({i,j} : Set α)
      simpa using eq_or_eq_of_swap_apply_ne_self hm }
  have hcard : Nat.card P = 2 := by
    change Nat.card ({i,j} : Set α) = 2
    simp [hij]
  have hpperm : IsPGroup 2 (Perm P) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,←Nat.card_eq_fintype_card,hcard]
    decide)
  let f := MulAction.toPermHom X P
  have hf := hp.hom_eq_one_of_isPGroup hpperm f
  intro x hx a ha
  have he := DFunLike.congr_fun (DFunLike.congr_fun hf ⟨x,hx⟩) (⟨a,ha⟩ : P)
  exact congrArg Subtype.val he
end Equiv.Perm
