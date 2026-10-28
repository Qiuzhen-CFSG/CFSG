module
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.Commutator.ConjugateGeneration

/-!
# Trivial quotient action on a seed and its conjugate orbit

Let T normalize X. If X acts trivially on K modulo a normal subgroup Q,
then it acts trivially on the whole T-orbit of K modulo Q. When Q lies
in T and X normalizes this orbit, it also normalizes its intersection
with T. This uses the original seed and actor, with no component quotient
or factor projection chosen along the way.

Source application: Aschbacher--Smith 6.1.4, printed p.665.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A trivial seed action modulo a normal subgroup in T forces
normalization of the actual orbit intersection with T. -/
theorem normalizes_orbit_intersection_of_commutator_le
    (X K T Q : Subgroup G) [Q.Normal]
    (hQT : Q ≤ T) (hTX : T ≤ normalizer (X : Set G))
    (hXN : X ≤ normalizer (componentOrbit K T : Set G))
    (hcomm : ⁅X,K⁆ ≤ Q) :
    X ≤ normalizer ((T ⊓ componentOrbit K T : Subgroup G) : Set G) := by
  let q := QuotientGroup.mk' Q
  have hTXq : T.map q ≤ normalizer (X.map q : Set (G ⧸ Q)) :=
    (map_mono hTX).trans (X.le_normalizer_map q)
  have hzero : ⁅K.map q,X.map q⁆ = ⊥ := by
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk',commutator_comm]
    exact hcomm
  have hcent : (componentOrbit K T).map q ≤ centralizer (X.map q : Set (G ⧸ Q)) := by
    rw [map_componentOrbit]
    exact iSup_conjugates_le_centralizer _ _ _ hTXq hzero
  have horb : ⁅X,componentOrbit K T⁆ ≤ Q := by
    have hz := commutator_eq_bot_iff_le_centralizer.mpr hcent
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk',commutator_comm] at hz
    exact hz
  apply le_normalizer_iff.mpr
  intro x hx t ht
  refine ⟨?_,(mem_normalizer_iff.mp (hXN hx) t).mp ht.2⟩
  have hc : ⁅x,t⁆ ∈ Q := horb (commutator_mem_commutator hx ht.2)
  have hh := T.mul_mem (hQT hc) ht.1
  change x * t * x⁻¹ ∈ T
  simpa only [commutatorElement_def,inv_mul_cancel_right] using hh

end Theory.GroupTheory
