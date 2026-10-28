module
public import Theory.GroupTheory.PCoreImage

/-!
# Normal two-by-three layers

A normal subgroup whose quotient by its own two-core is a three-group
lies in the preimage of the three-core modulo the ambient two-core.
The property also passes to surjective images. These are the normal-core
steps in Aschbacher–Smith13.5.21(ii), printed p.923.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A surjective image of a two-by-three group is again two-by-three. -/
theorem quotient_twoCore_isThreeGroup_of_surjective
    {E F : Type*} [Group E] [Group F] (f : E →* F) (hf : Function.Surjective f)
    (h : IsPGroup 3 (E ⧸ pCore 2 E)) : IsPGroup 3 (F ⧸ pCore 2 F) := by
  let q := (QuotientGroup.mk' (pCore 2 F)).comp f
  have hc : (pCore 2 E).map f ≤ pCore 2 F :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  have hk : pCore 2 E ≤ q.ker := fun x hx =>
    (QuotientGroup.eq_one_iff _).mpr (hc (mem_map_of_mem f hx))
  let g := QuotientGroup.lift (pCore 2 E) q hk
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  exact h.of_surjective g (QuotientGroup.lift_surjective_of_surjective (pCore 2 E) q hq hk)

/-- Normal two-by-three subgroups lie in the actual two-three core. -/
theorem le_twoThreeCore_of_normal (L : Subgroup G) [L.Normal]
    (h : IsPGroup 3 (L ⧸ pCore 2 L)) :
    L ≤ (pCore 3 (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let M := L.map q
  let f : L →* M := q.subgroupMap L
  have hc : (pCore 2 L).map L.subtype ≤ pCore 2 G :=
    le_sSup ⟨inferInstance,(pCore_isPGroup (p := 2) (G := L)).map L.subtype⟩
  have hk : pCore 2 L ≤ f.ker := by
    intro l hl
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr (hc (mem_map_of_mem L.subtype hl))
  let g := QuotientGroup.lift (pCore 2 L) f hk
  have hg : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective _ _ (q.subgroupMap_surjective L) _
  have hM : IsPGroup 3 M := h.of_surjective g hg
  have hN : M.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  exact Subgroup.map_le_iff_le_comap.mp (le_sSup ⟨hN,hM⟩)
end Subgroup
