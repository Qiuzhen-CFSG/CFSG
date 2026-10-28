module
public import Theory.GroupTheory.PCoreNormalizerAction.Kernel
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Sylow placement of a core-quotient action kernel

If S is an ambient Sylow p-subgroup contained in J, every actor trivial
on J/O_p(J) normalizes S: its displacement of each element of S belongs
to O_p(J), which lies in S. If the quotient is centerless, the action
kernel meets J in exactly O_p(J). These are literal ambient intersections,
not centralizers substituted for quotient-action kernels.

The original triality centralizer in Aschbacher--Smith 14.2.18, p.987,
uses these statements in `EightLargeParabolic/FieldAction.lean`.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- Trivial quotient action preserves the original Sylow containing J's core. -/
theorem pCoreActionKernelIn_le_sylow_normalizer (J N : Subgroup G)
    (S : Sylow p G) (hSJ : (S : Subgroup G) ≤ J) :
    pCoreActionKernelIn p J N ≤ normalizer (S : Set G) := by
  have hQS : J.pCoreIn p ≤ (S : Subgroup G) := by
    rintro x ⟨y,hy,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (S.subtype hSJ) hy
  intro x hx
  obtain ⟨a,ha,he⟩ := hx.2
  have hax : (a : G) = x := he
  apply mem_normalizer_fintype
  intro t ht
  have hm := (pCoreNormalizerAction_eq_one_iff p J a).mp ha ⟨t,hSJ ht⟩
  have hc : x * t * x⁻¹ / t ∈ J.pCoreIn p := by
    refine ⟨J.normalizerMonoidHom a ⟨t,hSJ ht⟩ / ⟨t,hSJ ht⟩,hm,?_⟩
    change (a : G) * t * (a : G)⁻¹ / t = x * t * x⁻¹ / t
    rw [hax]
  change x * t * x⁻¹ ∈ (S : Subgroup G)
  convert S.mul_mem (hQS hc) ht using 1
  simp only [div_mul_cancel]

omit [Finite G] in
/-- The intersection with the acted-on subgroup is exactly its core. -/
theorem pCoreActionKernelIn_inf_eq_core (J N : Subgroup G) (hJN : J ≤ N)
    (hz : center (J ⧸ pCore p J) = ⊥) :
    pCoreActionKernelIn p J N ⊓ J = J.pCoreIn p := by
  have hi := conj_injective_of_center_eq_bot hz
  ext x
  constructor
  · rintro ⟨hx,hxJ⟩
    obtain ⟨a,ha,he⟩ := hx.2
    let j : J := ⟨x,hxJ⟩
    have he' : a = ⟨j,J.le_normalizer j.property⟩ := Subtype.ext he
    have hc : MulAut.conj (QuotientGroup.mk' (pCore p J) j) = 1 := by
      change pCoreNormalizerAction p J a = 1 at ha
      rw [he',pCoreNormalizerAction_on_component] at ha
      exact ha
    have hj : j ∈ pCore p J := (QuotientGroup.eq_one_iff j).mp
      (hi (hc.trans (map_one MulAut.conj).symm))
    exact ⟨j,hj,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    refine ⟨⟨hJN j.property,⟨j,J.le_normalizer j.property⟩,?_,rfl⟩,j.property⟩
    change pCoreNormalizerAction p J ⟨j,J.le_normalizer j.property⟩ = 1
    have hq : QuotientGroup.mk' (pCore p J) j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
    rw [pCoreNormalizerAction_on_component, hq, map_one]

end Subgroup
