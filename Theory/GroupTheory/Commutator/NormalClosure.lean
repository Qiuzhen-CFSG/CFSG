module
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Commutator bounds and normal closure

If H and V are normal subgroups and [H,J] is contained in V, then the
same bound holds with J replaced by its normal closure. No finiteness or
solvability assumptions are required. This is the normal-closure transfer
used in the noncentralizing case of Stellmacher (2.3), Journal of Algebra
190 (1997).

Pass to the quotient by V. The image of J centralizes the image of H;
since the latter is normal, its centralizer is normal as well. Pulling
that centralizer back contains the normal closure of J. Mapping the final
commutator to the quotient therefore kills it, giving the desired bound.
-/

namespace Subgroup

public theorem commutator_normalClosure_le_of_normal
    {G : Type*} [Group G] (H J V : Subgroup G) [H.Normal] [V.Normal]
    (hcomm : ⁅H, J⁆ ≤ V) : ⁅H, normalClosure (J : Set G)⁆ ≤ V := by
  let q := QuotientGroup.mk' V
  let : (H.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective V)
  have hqcomm : ⁅H.map q, J.map q⁆ = ⊥ := by
    rw [← map_commutator, map_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hcomm
  have hJC : J.map q ≤ centralizer (H.map q) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  have hclosure : normalClosure (J : Set G) ≤ (centralizer (H.map q)).comap q :=
    normalClosure_le_normal (fun _ hj => (map_le_iff_le_comap.mp hJC) hj)
  have hqclosure : (normalClosure (J : Set G)).map q ≤ centralizer (H.map q) :=
    map_le_iff_le_comap.mpr hclosure
  have hzero : (⁅H, normalClosure (J : Set G)⁆).map q = ⊥ := by
    rw [map_commutator, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hqclosure
  have hh := (map_eq_bot_iff _).mp hzero
  simpa only [q, QuotientGroup.ker_mk'] using hh

end Subgroup

