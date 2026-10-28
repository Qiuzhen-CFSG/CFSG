module
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.Frattini.Intersection
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# Detecting prime-core membership from Frattini displacement

For a self-centralizing prime core, an element whose commutators with the
core lie in its Frattini subgroup belongs to the core. This is the pointwise
form of Burnside's exact Frattini action kernel. The ambient version retains
the original subgroup inclusion and transports the Frattini subgroup through
that inclusion.

The nonblock rank-one consumer applies this to its original second center
and the component core, whose Frattini subgroup is the source root.
Source: Burnside's basis theorem; Aschbacher--Smith, original 4.3.2,
printed pp.618--619, with the radical second-center calculation.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
/-- Pointwise Frattini displacement detects membership in a self-centralizing prime core. -/
theorem mem_pCore_of_frattini_displacement
    (hcentral : centralizer (pCore p G : Set G) ≤ pCore p G) (g : G)
    (hg : ∀ x : pCore p G, ⁅g,(x : G)⁆ ∈
      (frattini (pCore p G)).map (pCore p G).subtype) : g ∈ pCore p G := by
  rw [←pCore_frattini_action_kernel p hcentral]
  apply MulEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini (pCore p G)) v
  change quotientAut (frattini (pCore p G)) (MulAut.conjNormal g)
    (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
  rw [quotientAut_apply_mk]
  have hx : MulAut.conjNormal g x * x⁻¹ ∈ frattini (pCore p G) := by
    apply (mem_map_iff_mem (pCore p G).subtype_injective).mp
    exact hg x
  have he : QuotientGroup.mk' (frattini (pCore p G))
      (MulAut.conjNormal g x * x⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hx
  rw [map_mul,map_inv] at he
  exact mul_inv_eq_one.mp he

/-- The same detection through the original ambient subgroup inclusion. -/
theorem le_pCoreIn_of_frattini_displacement (M A : Subgroup G) (hAM : A ≤ M)
    (hcentral : centralizer (pCore p M : Set M) ≤ pCore p M)
    (hc : ⁅A,M.pCoreIn p⁆ ≤ (frattini (M.pCoreIn p)).map (M.pCoreIn p).subtype) :
    A ≤ M.pCoreIn p := by
  have hF : (frattini (M.pCoreIn p)).map (M.pCoreIn p).subtype =
      ((frattini (pCore p M)).map (pCore p M).subtype).map M.subtype :=
    frattini_image_map (pCore p M) M.subtype M.subtype_injective
  intro a ha
  have hb : (⟨a,hAM ha⟩ : M) ∈ pCore p M := by
    apply mem_pCore_of_frattini_displacement hcentral
    intro x
    apply (mem_map_iff_mem M.subtype_injective).mp
    rw [←hF]
    exact hc (commutator_mem_commutator ha (mem_map_of_mem M.subtype x.property))
  exact mem_map_of_mem M.subtype hb
end Subgroup
