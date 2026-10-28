module

public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.ComponentStructure
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.SourceCatalogue
public import Theory.Representation.NormalPSubgroupKernel

/-!
# The literal actor on the B.5.5 chief section

For an A-invariant faithful irreducible L-chief section of the original
module, its literal quotient (LA)/ker contains an isomorphic marked copy of L.
Irreducibility makes its two-core trivial, and its two-group quotient by L
identifies its generalized Fitting subgroup. Odd-prime rank bounds pass
through this marked copy, while the full K-group condition comes from the
original SQTK cover through D, LA and the literal quotient. The group and
module universes remain independent.

`classify` applies the complete corrected B.4.2 implication on precisely this
actor and section. The section and contained-offender premises are discharged
by the sibling Selection module in the ChiefSections assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.5(1iii–iv), printed pp.104–105; B.4.2, printed p.86.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.PreparationSource.ChiefSections
open SourceInduction ComponentReduction ComponentReduction.PreliminaryActions Preparation
open QuasisimpleSource.IrreducibleBranch
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {A L : Subgroup D}

theorem projection_surjective (s : ChiefSection ρ A L) :
    Function.Surjective s.projection := QuotientGroup.mk'_surjective _

theorem action_faithful (s : ChiefSection ρ A L) : Function.Injective s.action :=
  (QuotientGroup.injective_lift_iff _ _ le_rfl).mpr rfl

theorem component_map_injective (s : ChiefSection ρ A L) :
    Function.Injective (s.projection.subgroupMap (L.subgroupOf (L ⊔ A))) := by
  intro x y h
  apply (subgroupOfEquivOfLe (show L ≤ L ⊔ A from le_sup_left)).injective
  apply s.faithful
  exact congrArg (fun q => s.action q) (congrArg Subtype.val h)

noncomputable def componentEquiv (s : ChiefSection ρ A L) : L ≃* s.component :=
  (subgroupOfEquivOfLe (show L ≤ L ⊔ A from le_sup_left)).symm.trans
    (MulEquiv.ofBijective (s.projection.subgroupMap (L.subgroupOf (L ⊔ A)))
      ⟨component_map_injective s, s.projection.subgroupMap_surjective _⟩)

theorem componentEquiv_action (s : ChiefSection ρ A L) (l : L) :
    s.action (componentEquiv s l) =
      s.lower.quotientRepresentation (inclusion (show L ≤ L ⊔ A from le_sup_left) l) := by rfl

theorem component_irreducible (s : ChiefSection ρ A L) :
    IsIrreducible (s.action.comp s.component.subtype) :=
  RepEquiv.irreducible_of_group_iso (componentEquiv s) (fun _ _ => rfl) s.irreducible

private theorem irreducible_of_pullback {E : Type*} [Group E]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (f : E →* D)
    (hi : IsIrreducible (σ.comp f)) : IsIrreducible σ := by
  let : IsIrreducible (σ.comp f) := hi
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial (σ.comp f)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (σ.comp f) :=
    ⟨S.toSubmodule, fun d _ hv => S.apply_mem_toSubmodule (f d) hv⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (σ.comp f) => U.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (σ.comp f) => U.toSubmodule) h

theorem action_irreducible (s : ChiefSection ρ A L) : IsIrreducible s.action :=
  irreducible_of_pullback s.action s.component.subtype (component_irreducible s)

theorem component_normal (s : ChiefSection ρ A L) [L.Normal] : s.component.Normal :=
  Subgroup.Normal.map inferInstance s.projection (projection_surjective s)

theorem component_quotient_isTwoGroup (s : ChiefSection ρ A L) [L.Normal]
    (hA : IsPGroup 2 A) :
    let := component_normal s
    IsPGroup 2 (s.Actor ⧸ s.component) := by
  let := component_normal s
  have hm : L.subgroupOf (L ⊔ A) ≤ s.component.comap s.projection :=
    fun _ hl => mem_map_of_mem s.projection hl
  exact (local_quotient_isTwoGroup L A hA).of_surjective
    (QuotientGroup.map _ _ s.projection hm)
    (QuotientGroup.map_surjective_of_surjective _ _ s.projection
      ((QuotientGroup.mk'_surjective s.component).comp (projection_surjective s)) hm)

theorem twoCore_eq_bot [Finite D] [Module.Finite (ZMod 2) V]
    (s : ChiefSection ρ A L) : pCore 2 s.Actor = ⊥ := by
  let := action_irreducible s
  exact bot_unique ((normal_p_subgroup_le_ker s.action (pCore 2 s.Actor)
    (pCore_isPGroup (p := 2))).trans
      ((MonoidHom.ker_eq_bot_iff _).mpr (action_faithful s)).le)

theorem fitting_eq_component [Finite D] [Module.Finite (ZMod 2) V]
    (s : ChiefSection ρ A L) [L.Normal] [IsQuasisimple L]
    (hA : IsPGroup 2 A) : generalizedFitting s.Actor = s.component := by
  let := component_normal s
  let : IsQuasisimple s.component := IsQuasisimple.of_mulEquiv (componentEquiv s)
  exact generalizedFitting_eq_of_quasisimple_two_quotient s.component
    (component_quotient_isTwoGroup s hA) (twoCore_eq_bot s)

theorem actor_isKGroup [Finite D] {K : GroupClass.{u}}
    (hyp : FFHypothesis K ρ) (s : ChiefSection ρ A L) : IsKGroup K s.Actor := by
  obtain ⟨c⟩ := hyp.quotient
  have hD : IsKGroup K D := (IsKGroup.equiv c.equiv).mp (c.sqtk.isKGroup.quotient c.kernel)
  exact (hD.subgroup (L ⊔ A)).quotient s.lower.quotientRepresentation.ker

theorem actor_sqtk [Finite D] {K : GroupClass.{u}}
    (hyp : FFHypothesis K ρ) (s : ChiefSection ρ A L) [L.Normal]
    (hA : IsPGroup 2 A) (hL : IsSQTK K L) : IsSQTK K s.Actor := by
  let := component_normal s
  exact ⟨stronglyQuasithin_of_twoGroup_quotient s.component
    (component_quotient_isTwoGroup s hA)
    ((IsStronglyQuasithin.equiv (componentEquiv s)).mp hL.stronglyQuasithin),
    actor_isKGroup hyp s⟩

theorem classify [Finite D] {K : GroupClass.{u}}
    (earlier : ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (s : ChiefSection ρ A L) [L.Normal] [IsQuasisimple L]
    (hA : IsPGroup 2 A) (hL : IsSQTK K L)
    (hb : ∃ B ≤ s.offender, IsBestOffender s.action B) :
    ProjectiveLine.IrreducibleActionCase s.action s.component (offenderSubgroup s.action) := by
  let := hyp.finite_module
  have hf := fitting_eq_component s hA
  have hq : IsQuasisimple (generalizedFitting s.Actor) := by
    rw [hf]
    exact IsQuasisimple.of_mulEquiv (componentEquiv s)
  have hi : IsIrreducible (s.action.comp (generalizedFitting s.Actor).subtype) := by
    rw [hf]
    exact component_irreducible s
  obtain ⟨B, _, hB⟩ := hb
  simpa only [hf] using earlier s.Actor _ s.action (actor_sqtk hyp s hA hL)
    hq (action_faithful s) hi ⟨B, hB⟩

end CFSG.Quasithin.ChapterB.PreparationSource.ChiefSections
