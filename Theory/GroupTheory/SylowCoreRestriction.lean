module

public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Prime cores along overgroups of a fixed Sylow subgroup

If T is an ambient Sylow p-subgroup and T ≤ H ≤ M, then O_p(M) lies
in T and hence in H. Restriction of the core therefore gives O_p(M) ≤ O_p(H).
In particular a core-free H containing T cannot lie in an overgroup with
nontrivial p-core. This detects distinct maximal local overgroups from an
actual core-free generated pair.

Source: the standing two-local condition after Aschbacher--Smith 2.1.1,
p.518, applied to the actual F.9.1 pair, p.317.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- Reverse core containment along subgroups containing a fixed Sylow subgroup. -/
theorem pCoreIn_le_of_sylow_le {p : ℕ} (T : Sylow p G)
    {H M : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hHM : H ≤ M) :
    M.pCoreIn p ≤ H.pCoreIn p := by
  have hMT : M.pCoreIn p ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow M (T.subtype (hTH.trans hHM))).trans_eq
      (map_subgroupOf_eq_of_le (hTH.trans hHM))
  exact (le_inf (hMT.trans hTH) le_rfl).trans (inf_pCoreIn_le_of_le p hHM)

/-- A Sylow-containing core-free subgroup escapes every overgroup with
nontrivial core, using the original intrinsic cores. -/
theorem not_le_of_sylow_le_of_core_eq_bot {p : ℕ} (T : Sylow p G)
    {H M : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hH : pCore p H = ⊥) (hM : pCore p M ≠ ⊥) : ¬ H ≤ M := by
  intro hHM
  have hb : M.pCoreIn p = ⊥ := bot_unique (by
    have hle := pCoreIn_le_of_sylow_le T hTH hHM
    simpa only [pCoreIn, hH, Subgroup.map_bot] using hle)
  exact hM (((pCore p M).map_eq_bot_iff_of_injective M.subtype_injective).mp hb)

end Theory.GroupTheory
