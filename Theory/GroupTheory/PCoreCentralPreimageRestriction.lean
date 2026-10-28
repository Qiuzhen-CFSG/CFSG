module
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.PGroupCore

/-!
# Restricting the center above a prime core

An injective homomorphism pulls the ambient prime core into the intrinsic
prime core. Hence an element central modulo the ambient core remains
central modulo the intrinsic core. A surjection to a centerless group
with trivial prime core then identifies its kernel with this central
preimage whenever the reverse containment is known.

The actual weight-six point residual uses these two comparisons to retain
the possible triple cover in Aschbacher--Smith 12.3.6, printed p.809.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {A B D : Type*} [Group A] [Group B] [Group D]

/-- Centrality modulo an ambient prime core restricts to an embedded subgroup. -/
theorem centralPreimage_pCore_comap_le (p : ℕ) (i : A →* B)
    (hi : Function.Injective i) :
    (centralPreimage (pCore p B)).comap i ≤ centralPreimage (pCore p A) := by
  have hp : (pCore p B).comap i ≤ pCore p A :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective i hi⟩
  intro x hx
  apply mem_center_iff.mpr
  intro y
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore p A) y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply hp
  change i ⁅y,x⁆ ∈ pCore p B
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (pCore p B)) (i ⁅y,x⁆) = 1
  rw [map_commutatorElement,map_commutatorElement]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  exact mem_center_iff.mp hx _

/-- A centerless, core-free image detects exactly the central preimage of the core. -/
theorem centralPreimage_pCore_eq_ker_of_centerless [Finite A] [Finite D]
    (p : ℕ) (f : A →* D) (hf : Function.Surjective f)
    (hcore : pCore p D = ⊥) (hcenter : center D = ⊥)
    (hk : f.ker ≤ centralPreimage (pCore p A)) :
    centralPreimage (pCore p A) = f.ker := by
  have hp : pCore p A ≤ f.ker := by
    have hn : ((pCore p A).map f).Normal := Normal.map inferInstance f hf
    have hm : (pCore p A).map f ≤ pCore p D :=
      le_sSup ⟨hn,pCore_isPGroup.map f⟩
    rw [hcore] at hm
    exact (map_le_iff_le_comap).mp hm
  let q : A ⧸ pCore p A →* D := QuotientGroup.lift _ f hp
  apply le_antisymm ?_ hk
  intro x hx
  have hc : f x ∈ center D := by
    apply mem_center_iff.mpr
    intro d
    obtain ⟨a,rfl⟩ := hf d
    simpa only [map_mul, q, QuotientGroup.mk'_apply, QuotientGroup.lift_mk'] using
      congrArg q (mem_center_iff.mp hx (QuotientGroup.mk' _ a))
  rwa [hcenter,mem_bot] at hc

end Subgroup
