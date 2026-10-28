module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalAction
public import Theory.GroupTheory.CComponent.NormalFromImage

/-!
# Sylow normalization of the original marked A₅ component

The actual LT action kills its solvable radical and maps the original
C-component L onto the normal A₅ subgroup of S₅. Distinct C-components
commute modulo the solvable radical, so the nonabelian action image
forces L to be normal in LT. Thus T-normality in the A₅ F.9 application
follows from the original Context, without the general model list of
13.3.2 or a new normality assumption.

Source: Aschbacher–Smith 13.3.2(2) in the marked A₅ case; application
13.5.7, printed pp.885 and917.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem localActor_component_image :
    (L.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor = alternatingGroup (Fin 5) := by
  apply le_antisymm
  · rintro a ⟨l,hl,rfl⟩
    have he : d.localActor l = (d.flag.module.action ⟨l.val,hl⟩).val :=
      d.flag.action_agrees ⟨l.val,hl⟩ (d.flag.module.normalizes hl)
    rw [he]
    exact (d.flag.module.action ⟨l.val,hl⟩).property
  · intro a ha
    obtain ⟨l,hl⟩ := d.flag.module.onto ⟨a,ha⟩
    refine ⟨inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l,l.property,?_⟩
    exact (d.flag.action_agrees l (d.flag.module.normalizes l.property)).trans
      (congrArg Subtype.val hl)

/-- The actual A₅ module detects normality of its original local component. -/
theorem normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G) := by
  have hR : solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G) ≤ d.localActor.ker :=
    Theory.SpecificGroups.FivePointSylowParabolic.solvable_normal_le_ker
      d.localActor d.alternating_le_localActor _
  have hn : ((L.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor).Normal :=
    d.localActor_component_image.symm ▸ inferInstance
  have hna : ¬ IsMulCommutative ((L.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor) := by
    rw [d.localActor_component_image]
    intro h
    have hh := alternatingGroup.isMulCommutative_iff_card_le_three.mp h
    norm_num at hh
  have hL := d.hypothesis.local_component.1.1.normal_of_normal_nonabelian_image
    d.localActor hR hn hna
  exact (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)).trans
    ((normal_subgroupOf_iff_le_normalizer (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).mp hL)

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
