module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Normalizers of a moved subgroup modulo an action kernel

If [U,Q] lies in a normal subgroup Z, adjoining Q to an actor V does
not change Z[U,V]. Thus a normalizer of the image of V in G/Q preserves
this moved subgroup whenever U and Z are normal. The proof uses the
commutator identity for vq and the literal quotient preimage VQ.

This is the group-theoretic step in Aschbacher–Smith F.9.5(3), printed
p.319. It needs no choice of module coordinates or dimension assumptions.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem point_sup_commutator_sup_kernel (U V Q Z : Subgroup G) [Q.Normal] [Z.Normal]
    (hc : ⁅U,Q⁆ ≤ Z) : Z ⊔ ⁅U,V ⊔ Q⁆ = Z ⊔ ⁅U,V⁆ := by
  apply le_antisymm _ (sup_le_sup_left (commutator_mono le_rfl le_sup_left) Z)
  refine sup_le le_sup_left (commutator_le.mpr ?_)
  intro u hu x hx
  obtain ⟨v,hv,q,hq,rfl⟩ := mem_sup_of_normal_right.mp hx
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hz : v * ⁅u,q⁆ * v⁻¹ ∈ Z :=
    (inferInstance : Z.Normal).conj_mem _ (hc (commutator_mem_commutator hu hq)) v
  have hm := (Z ⊔ ⁅U,V⁆).mul_mem (mem_sup_right (commutator_mem_commutator hu hv))
    (mem_sup_left hz)
  simpa only [mul_assoc] using hm

theorem normalizer_quotient_preserves_moved_seed (U V Q Z : Subgroup G)
    [U.Normal] [Q.Normal] [Z.Normal] (hc : ⁅U,Q⁆ ≤ Z) :
    (normalizer (V.map (QuotientGroup.mk' Q) : Set (G ⧸ Q))).comap
      (QuotientGroup.mk' Q) ≤ normalizer ((Z ⊔ ⁅U,V⁆ : Subgroup G) : Set G) := by
  intro x hx
  have hN : x ∈ normalizer ((V ⊔ Q : Subgroup G) : Set G) := by
    have hh := (V.map (QuotientGroup.mk' Q)).le_normalizer_comap (QuotientGroup.mk' Q) hx
    simpa only [comap_map_eq,QuotientGroup.ker_mk'] using hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← point_sup_commutator_sup_kernel U V Q Z hc,Subgroup.map_sup,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (show x∈normalizer (Z:Set G) from by
      rw [normalizer_eq_top]; trivial),
    mem_normalizer_iff_map_conj_eq.mp (show x∈normalizer (U:Set G) from by
      rw [normalizer_eq_top]; trivial),
    mem_normalizer_iff_map_conj_eq.mp hN]
end Subgroup
