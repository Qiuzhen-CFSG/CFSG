module
public import Theory.GroupTheory.TwoPerfectCubicImages
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SectionSylow

/-!
# Restricted kernels and Sylow action cores

A nontrivial action of a finite p-perfect group with simple quotient by
its p-core has p-group kernel: a nontrivial residual of the kernel would
fill the whole group. A normal subgroup with such a restricted kernel
normalizes the preimage in a Sylow subgroup of the target p-core.
Commutators with that preimage lie in the subgroup's own p-core.

These statements apply to the normal cubic residuals in the original
five-dimensional action in Aschbacher--Smith 13.4.8, pp.904--905,
without asserting that the entire action kernel is a two-group.
-/

public section
open Subgroup

namespace IsPPerfect
variable {G D : Type*} [Group G] [Group D] [Finite G]
/-- Every nontrivial action has p-group kernel over a simple p-core quotient. -/
theorem kernel_isPGroup_of_simple_core_quotient {p : ℕ} [Fact p.Prime] (hG : IsPPerfect p G)
    [IsSimpleGroup (G ⧸ pCore p G)] (f : G →* D) (hne : f ≠ 1) :
    IsPGroup p f.ker := by
  let N := (pResidual p f.ker).map f.ker.subtype
  have hn : N = ⊥ := by
    by_contra hn
    have ht : N = ⊤ := eq_top_of_normal_isPPerfect_of_simple_quotient
      (pCore p G) pCore_isPGroup hG N (isPPerfect_embedded_pResidual p f.ker) hn
    have hk : f.ker = ⊤ := top_unique (ht ▸ map_subtype_le (pResidual p f.ker))
    apply hne
    ext x
    exact MonoidHom.mem_ker.mp (hk ▸ mem_top x)
  have hr : pResidual p f.ker = ⊥ :=
    (map_eq_bot_iff_of_injective _ f.ker.subtype_injective).mp hn
  exact (isPGroup_quotient_pResidual p).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hr).trans QuotientGroup.quotientBot)
end IsPPerfect

open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G D : Type*} [Group G] [Group D]

/-- Commutators with the Sylow action core lie in the normal actor's own core. -/
theorem commutator_sylow_action_core_le {p : ℕ} [Fact p.Prime]
    (f : G →* D) (Y : Subgroup G) [Y.Normal] (T : Sylow p G)
    (hk : IsPGroup p (f.comp Y.subtype).ker) :
    ⁅Y,((T : Subgroup G) ⊓ (pCore p D).comap f : Subgroup G)⁆ ≤ Y.pCoreIn p := by
  let R := (T : Subgroup G) ⊓ (pCore p D).comap f
  have hpre : (pCore p D).comap (f.comp Y.subtype) ≤ pCore p Y :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_ker_isPGroup _ hk⟩
  apply commutator_le.mpr
  intro y hy r hr
  have hmem : ⁅y,r⁆ ∈ Y := le_normalizer_iff_commutator_le_left.mp
    (show R ≤ normalizer (Y : Set G) from le_normalizer_of_normal)
    (commutator_mem_commutator hy hr)
  have hmap : f ⁅y,r⁆ ∈ pCore p D := by
    rw [map_commutatorElement]
    exact (pCore p D).mul_mem
      ((inferInstance : (pCore p D).Normal).conj_mem (f r) hr.2 (f y))
      ((pCore p D).inv_mem hr.2)
  exact
    mem_map_of_mem Y.subtype (hpre (show (⟨⁅y,r⁆,hmem⟩ : Y) ∈
      (pCore p D).comap (f.comp Y.subtype) from hmap))

/-- A normal subgroup with a prime-group restricted action kernel normalizes
the preimage in a Sylow subgroup of the image prime core. -/
theorem normalizes_sylow_action_core {p : ℕ} [Fact p.Prime]
    (f : G →* D) (Y : Subgroup G) [Y.Normal] (T : Sylow p G)
    (hk : IsPGroup p (f.comp Y.subtype).ker) :
    Y ≤ normalizer ((T : Subgroup G) ⊓ (pCore p D).comap f : Set G) := by
  let R := (T : Subgroup G) ⊓ (pCore p D).comap f
  have hQT : Y.pCoreIn p ≤ T := by
    have hn : (Y.pCoreIn p).Normal := inferInstanceAs ((pCore p Y).map Y.subtype).Normal
    exact (isPGroup_pCoreIn p Y).le_sylow_of_normal T
  change Y ≤ normalizer (R : Set G)
  apply le_normalizer_iff.mpr
  intro y hy r hr
  have hq : ⁅y,r⁆ ∈ Y.pCoreIn p :=
    commutator_sylow_action_core_le f Y T hk (commutator_mem_commutator hy hr)
  refine ⟨?_,?_⟩
  · change y*r*y⁻¹ ∈ (T : Subgroup G)
    have hh := (T : Subgroup G).mul_mem (hQT hq) hr.1
    simpa only [commutatorElement_def,inv_mul_cancel_right] using hh
  · change f (y*r*y⁻¹) ∈ pCore p D
    rw [map_mul,map_mul,map_inv]
    exact (inferInstance : (pCore p D).Normal).conj_mem (f r) hr.2 (f y)
end Subgroup
