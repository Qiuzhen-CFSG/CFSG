module

public import Theory.SpecificGroups.BinaryLinear.LineRadical

/-!
# Fixed vectors of a full binary linear Sylow subgroup

Every nonzero invariant subspace contains the entire fixed space of a
Sylow two-subgroup of the full linear group. Its full unipotent radical
lies in that Sylow subgroup and detects membership of the subspace.
Consequently, a subgroup with no fixed vector on that subspace, together
with the Sylow subgroup, has no fixed vector on the natural module.

Source application: Aschbacher--Smith12.7.18, printed p.845.
-/

public section
open Subgroup
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Every nonzero Sylow-invariant subspace contains every Sylow-fixed vector. -/
theorem sylow_fixedSpace_le_of_invariant
    (S : Sylow 2 (GL V)) (E : Submodule (ZMod 2) V) (hE : E ≠ ⊥)
    (hS : (S : Subgroup (GL V)) ≤ parabolic E) :
    fixedSpace (S : Subgroup (GL V)) ≤ E := by
  have hR : radical E ≤ S := by
    have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' (radical_two E)
      (hS.trans (parabolic_le_normalizer E))) le_sup_left
    exact he ▸ le_sup_right
  intro v hv
  exact (mem_iff_fixed_radical hE v).mpr (fun g hg => hv g (hR hg))

/-- A full Sylow and an actor moving its invariant subspace have no common
fixed vector when that subspace has no fixed vector for the actor. -/
theorem fixedSpace_sup_sylow_eq_bot_of_invariant
    (S : Sylow 2 (GL V)) (J : Subgroup (GL V))
    (E : Submodule (ZMod 2) V) (hE : E ≠ ⊥)
    (hS : (S : Subgroup (GL V)) ≤ parabolic E)
    (hJ : Disjoint E (fixedSpace J)) :
    fixedSpace (J ⊔ (S : Subgroup (GL V))) = ⊥ := by
  apply bot_unique
  intro v hv
  have hs : v ∈ fixedSpace (S : Subgroup (GL V)) :=
    fun g hg => hv g ((show (S : Subgroup (GL V)) ≤ J ⊔ (S : Subgroup (GL V)) from le_sup_right) hg)
  exact Submodule.disjoint_def.mp hJ v
    (sylow_fixedSpace_le_of_invariant S E hE hS hs)
    (fun g hg => hv g ((show J ≤ J ⊔ (S : Subgroup (GL V)) from le_sup_left) hg))

end BinaryLinear
