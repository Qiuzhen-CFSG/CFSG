module
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Mathlib.GroupTheory.IndexNormal
/-!
# An index-two stabilizer fixes the prescribed opposite conjugate

The stabilizer inside T is normal because it has index two. Conjugating
its containment in N(U) therefore places the same stabilizer in N(U^t).
This retains the specified element t and is the paired-component geometry
used in Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]
/-- The index-two stabilizer normalizes every specified T-conjugate. -/
theorem index_two_stabilizer_normalizes_conjugate
    (U T : Subgroup G) (hi : (normalizer (U : Set G)).relIndex T=2)
    {t : G} (ht : t ∈ T) :
    T ⊓ normalizer (U : Set G) ≤ normalizer (U.map (MulAut.conj t).toMonoidHom : Set G) := by
  let N := normalizer (U : Set G)
  let P := N.subgroupOf T
  let : P.Normal := normal_of_index_eq_two hi
  have hN : T ≤ normalizer ((T ⊓ N : Subgroup G) : Set G) := by
    have hh := P.le_normalizer_map T.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
      show P=N.subgroupOf T from rfl,subgroupOf_map_subtype,inf_comm] at hh
    exact hh
  have hm : (T ⊓ N).map (MulAut.conj t).toMonoidHom=T ⊓ N :=
    mem_normalizer_iff_map_conj_eq.mp (hN ht)
  have hle := map_mono (f := (MulAut.conj t).toMonoidHom)
    (show T ⊓ N ≤ normalizer (U : Set G) from inf_le_right)
  rwa [hm,map_equiv_normalizer_eq] at hle
end Theory.GroupTheory
