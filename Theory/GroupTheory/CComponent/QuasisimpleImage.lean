module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Quasisimple images of C-components

When a homomorphism kills the two-core of a C-component whose two-core
quotient is quasisimple, every nontrivial image is an ordinary component.
The image inherits subnormality, and its quasisimplicity comes from the
surjective map out of the literal intrinsic two-core quotient.

This is the component-image step in Aschbacher–Smith, combined manuscript
of 1 March 2004, Lemma D.3.3(1), printed p.193.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

theorem IsCComponent.isComponent_map_of_twoCore_killed
    {L : Subgroup G} (hL : L.IsCComponent)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (f : G →* H) (hf : Function.Surjective f)
    (hcore : L.pCoreIn 2 ≤ f.ker) (hne : L.map f ≠ ⊥) :
    IsComponent H (L.map f) := by
  let := hq
  let : Nontrivial (L.map f) := (nontrivial_iff_ne_bot _).mpr hne
  have hk : pCore 2 L ≤ (f.subgroupMap L).ker := by
    intro l hl
    apply Subtype.ext
    exact hcore (mem_map_of_mem L.subtype hl)
  let q := QuotientGroup.lift (pCore 2 L) (f.subgroupMap L) hk
  exact ⟨hL.subnormal.map hf, IsQuasisimple.of_surjective q
    (QuotientGroup.lift_surjective_of_surjective _ _ (f.subgroupMap_surjective L) _)⟩

/-- A nontrivial image of a component orbit has nontrivial seed image. -/
theorem componentOrbit_map_seed_ne_bot (L A : Subgroup G) (f : G →* H)
    (hne : (componentOrbit L A).map f ≠ ⊥) : L.map f ≠ ⊥ := by
  intro he
  apply hne
  rw [map_componentOrbit, he]
  simp only [componentOrbit, map_bot, iSup_const]

end Subgroup
