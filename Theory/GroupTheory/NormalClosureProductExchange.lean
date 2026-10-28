module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Exchange in a two-factor normal closure

If the ambient group permutes two disjoint factors whose join is the normal
closure of an element in the first factor, it must exchange them when the
second factor is nontrivial. Otherwise the first factor is normal and already
contains the normal closure, contradicting disjointness.

Source application: Aschbacher–Smith, G.6.4(1), printed pp.345–346.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem exists_exchange_of_normalClosure_product
    (A B : Subgroup G) (a : G) (ha : a ∈ A)
    (hjoin : A ⊔ B = normalClosure ({a} : Set G))
    (hdis : Disjoint A B) (hB : B ≠ ⊥)
    (hperm : ∀ g : G,
      (A.map (MulAut.conj g).toMonoidHom = A ∧
        B.map (MulAut.conj g).toMonoidHom = B) ∨
      (A.map (MulAut.conj g).toMonoidHom = B ∧
        B.map (MulAut.conj g).toMonoidHom = A)) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B ∧
      B.map (MulAut.conj g).toMonoidHom = A := by
  by_contra hn
  have hf (g : G) : A.map (MulAut.conj g).toMonoidHom = A :=
    ((hperm g).resolve_right (fun hg => hn ⟨g, hg⟩)).1
  let : A.Normal := normalizer_eq_top_iff.mp (top_unique (by
    intro g _
    exact mem_normalizer_iff_map_conj_eq.mpr (hf g)))
  have hK : normalClosure ({a} : Set G) ≤ A :=
    normalClosure_le_normal (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using ha)
  have hBA : B ≤ A := le_sup_right.trans (hjoin ▸ hK)
  apply hB
  apply bot_unique
  intro b hb
  exact hdis.eq_bot.le ⟨hBA hb, hb⟩

end Theory.GroupTheory
