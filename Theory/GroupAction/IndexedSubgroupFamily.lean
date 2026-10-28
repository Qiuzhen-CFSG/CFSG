module
public import Theory.GroupTheory.SubgroupConjugation
/-!
# Conjugation on an injectively indexed subgroup family

A subgroup preserving an injectively indexed family acts on its index set.
The permutation fixes an index exactly when the actor normalizes the
corresponding original subgroup.
-/

public section
open Subgroup
namespace Theory.GroupTheory.IndexedSubgroupFamily
variable {G I : Type*} [Group G]
variable (N : Subgroup G) (f : I → Subgroup G) (hinj : Function.Injective f)
  (hinv : ∀ g : N, ∀ i : I, ∃ j : I, f j = (f i).conjBy (g : G))

private noncomputable def move (g : N) (i : I) : I := (hinv g i).choose
private theorem move_spec (g : N) (i : I) :
    f (move N f hinv g i) = (f i).conjBy (g : G) := (hinv g i).choose_spec

private noncomputable def permutation (g : N) : Equiv.Perm I where
  toFun := move N f hinv g
  invFun := move N f hinv g⁻¹
  left_inv i := by
    apply hinj
    rw [move_spec N f hinv,move_spec N f hinv]
    exact Subgroup.conjBy_inv _ _
  right_inv i := by
    apply hinj
    rw [move_spec N f hinv,move_spec N f hinv]
    exact Subgroup.conjBy_inv' _ _

noncomputable def action : N →* Equiv.Perm I where
  toFun := permutation N f hinj hinv
  map_one' := by
    apply Equiv.ext
    intro i
    apply hinj
    change f (move N f hinv 1 i) = f i
    rw [move_spec N f hinv]
    exact Subgroup.conjBy_one _
  map_mul' g k := by
    apply Equiv.ext
    intro i
    apply hinj
    change f (move N f hinv (g*k) i) = f (move N f hinv g (move N f hinv k i))
    rw [move_spec N f hinv,move_spec N f hinv,move_spec N f hinv]
    exact Subgroup.conjBy_mul _ _ _

theorem action_apply (g : N) (i : I) :
    f (action N f hinj hinv g i) = (f i).conjBy (g : G) := move_spec N f hinv g i

theorem action_fixed_iff (g : N) (i : I) :
    action N f hinj hinv g i = i ↔ (g : G) ∈ normalizer (f i : Set G) := by
  constructor
  · intro he
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (action_apply N f hinj hinv g i).symm.trans (congrArg f he)
  · intro hn
    apply hinj
    exact (action_apply N f hinj hinv g i).trans (mem_normalizer_iff_map_conj_eq.mp hn)

end Theory.GroupTheory.IndexedSubgroupFamily
