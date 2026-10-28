module

public import Theory.GroupTheory.ReducedNormal.Equiv
public import Theory.GroupTheory.ReducedNormal.Inheritance

/-!
# Reduced subgroups through literal ambient inclusions

For Sylow overgroups H ≤ M, the inclusion Rₚ(H) ≤ Rₚ(M) is expressed
inside the original group. Transport to H as a subgroup of M allows
direct application of A.1.11, without replacing either conjugation group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma A.1.11 and its application in Lemma 3.2.2.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem reducedPSubgroup_ambient_le (T : Sylow p G) (H M : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hHM : H ≤ M)
    (hM : centralizer (pCore p M : Set M) ≤ pCore p M) :
    (reducedPSubgroup p H).map H.subtype ≤ (reducedPSubgroup p M).map M.subtype := by
  let e := (subgroupOfEquivOfLe hHM).symm
  have he : (reducedPSubgroup p H).map e.toMonoidHom ≤
      reducedPSubgroup p (H.subgroupOf M) :=
    (isPReduced_reducedPSubgroup.map_equiv e).le_reducedPSubgroup
  have hT : (T.subtype (hTH.trans hHM) : Subgroup M) ≤ H.subgroupOf M :=
    fun _ ht => hTH ht
  have hle := (map_mono (f := (H.subgroupOf M).subtype) he).trans
    (reducedPSubgroup_map_le_of_sylow_le (T.subtype (hTH.trans hHM))
      (H.subgroupOf M) hT hM)
  have hh := map_mono (f := M.subtype) hle
  have heq : M.subtype.comp ((H.subgroupOf M).subtype.comp e.toMonoidHom) = H.subtype := by
    ext x
    rfl
  simpa only [map_map, heq] using hh

end Theory.GroupTheory
