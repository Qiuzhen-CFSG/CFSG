module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Reduction

/-!
# The marked symplectic source on its characteristic replacement

Restricting the native source to the minimum characteristic edge product
preserves its literal natural module, fixed vector, component image A6 and
map into S6. Normality identifies the new two-core with the restriction of
the old one. Thus both the unreduced and reduced pairs have the proved
holomorph graph geometry. The reduced pair has characteristic minimality,
and pulling back its actual amalgam commutator recovers precisely the
original intrinsic component core.

Source: MS93 Section 7, pp.932--933. This realizes the setup only; the
critical-distance cases and whole-core reconstruction are subsequent proofs.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal]
namespace Source
variable (s : Source L R W)
include s

noncomputable def reduction : CharacteristicReduction L R :=
  Classical.choice (exists_reduction s.sup_eq_top s.core_le)

/-- The characteristic replacement retains the original natural coordinates. -/
noncomputable def reduce (c : CharacteristicReduction L R) :
    Source (L.subgroupOf c.overgroup) c.radical (W.subgroupOf c.overgroup) := by
  have hLH : L ≤ c.overgroup := le_sup_left
  have hRH : c.ambient ≤ c.overgroup := le_sup_right
  have hWH : W ≤ c.overgroup := s.module_le_component.trans hLH
  have hp : IsPGroup 2 c.radical :=
    ((s.two_group.to_subgroup c.subgroup).map R.subtype).comap_subtype
  have hperfect : IsPPerfect 2 (L.subgroupOf c.overgroup) := s.component_twoPerfect.of_surjective
    (subgroupOfEquivOfLe hLH).symm.toMonoidHom (subgroupOfEquivOfLe hLH).symm.surjective
  exact {
    two_group := hp
    core_le := Reduction.core_le_radical c inferInstance s.sup_eq_top
    characteristic := Reduction.msCharacteristic c s.sup_eq_top s.characteristic
    product := by
      intro m
      obtain ⟨l,hl,r,hr,he⟩ := mem_sup_of_normal_left.mp m.property
      exact ⟨⟨l,hLH hl⟩,hl,⟨r,hRH hr⟩,hr,Subtype.ext he⟩
    residual := pResidual_eq_of_isPPerfect_sup _ _ hperfect hp
      (codisjoint_subgroupOf_sup L c.ambient).eq_top
    projection := s.projection.comp c.overgroup.subtype
    projection_kernel := by
      change s.projection.ker.comap c.overgroup.subtype = pCore 2 c.overgroup
      rw [s.projection_kernel,Reduction.core_eq c inferInstance s.sup_eq_top]
    component_image := by
      rw [← map_map,map_subgroupOf_eq_of_le hLH,s.component_image]
    module_le_core := by
      intro w hw
      rw [Reduction.core_eq c inferInstance s.sup_eq_top]
      exact s.module_le_core hw
    module_le_component := fun _ hw => s.module_le_component hw
    coordinates := (subgroupOfEquivOfLe hWH).trans s.coordinates
    action := fun g w => s.action (g : M) ((subgroupOfEquivOfLe hWH) w)
    w := ⟨⟨s.w,hWH s.w.property⟩,s.w.property⟩
    w_ne := by
      intro he
      apply s.w_ne
      apply Subtype.ext
      exact congrArg (fun a : W.subgroupOf c.overgroup => ((a : c.overgroup) : M)) he
    radical_fixes := by
      intro r hr
      apply Subtype.ext
      exact s.radical_fixes (r : M) (map_subtype_le c.subgroup hr) }

theorem reduce_projection (c : CharacteristicReduction L R) :
    (s.reduce c).projection = s.projection.comp c.overgroup.subtype := rfl

theorem reduce_minimal (c : CharacteristicReduction L R) :
    CharacteristicMinimal (L.subgroupOf c.overgroup) c.radical :=
  Reduction.reduced_minimal c inferInstance s.sup_eq_top

/-- Pullback of the actual amalgam core is the original ambient commutator. -/
theorem reduced_core_pullback (c : CharacteristicReduction L R) :
    ((core c.radical (alpha c.radical)).comap (embedM c.radical)).map
      c.overgroup.subtype = ⁅pCore 2 M,L⁆ := by
  rw [core_alpha _ (s.reduce c).two_group (s.reduce c).core_le (s.reduce c).residual,
    comap_map_eq_self_of_injective (embedM_injective _)]
  exact Reduction.commutatorCore_eq c inferInstance s.sup_eq_top s.commutatorCore_eq_internal

/-- The intrinsic component core is unchanged through both source inclusions. -/
theorem reduced_core_pullback_internal (c : CharacteristicReduction L R) :
    ((core c.radical (alpha c.radical)).comap (embedM c.radical)).map
      c.overgroup.subtype = (⁅pCore 2 L,(⊤ : Subgroup L)⁆).map L.subtype :=
  (s.reduced_core_pullback c).trans s.commutatorCore_eq_internal

/-- At the unreduced source vertex, the same pullback is the intrinsic component core. -/
theorem original_core_pullback :
    (core R (alpha R)).comap (embedM R) = (blockU L).map L.subtype := by
  rw [core_alpha _ s.two_group s.core_le s.residual,
    comap_map_eq_self_of_injective (embedM_injective _)]
  exact s.commutatorCore_eq_internal

/-- The reduced marked vector is the original marked vector through inclusion. -/
theorem reduce_w_coe (c : CharacteristicReduction L R) :
    (((s.reduce c).w : c.overgroup) : M) = (s.w : M) := rfl

/-- The reduced natural coordinates are exactly the original coordinates. -/
theorem reduce_coordinates (c : CharacteristicReduction L R)
    (v : W.subgroupOf c.overgroup) :
    (s.reduce c).coordinates v =
      s.coordinates ((subgroupOfEquivOfLe
        (s.module_le_component.trans (show L ≤ c.overgroup from le_sup_left))) v) := rfl

end Source
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
