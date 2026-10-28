module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.BinaryCover
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.NaturalDualCover

/-!
# Faithful containing sections in the quiet full-module branch

Original Thompson fixedness forces the original moved fixed kernel to vanish:
a positive full fixed layer would force movement on the local module by
3.1.8. Thus the original moved subgroup embeds in the containing central
section. If its dimension fills that section, the original Thompson subgroup
fixes the section pointwise. Its image lies in the offender subgroup, so
faithfulness of the section contradicts the proved Thompson movement on VI.

The central kernel of the containing section is retained. Only its
intersection with the original moved subgroup is proved zero. The actual
natural--dual application is in Models.NaturalDualRows.
Source: Aschbacher--Smith 10.1.2 and10.2.9, printed pp.742 and751--752.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open scoped IsMulCommutative

private theorem end_eq_one_of_surjective {X Y : Type*}
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    (f : X →ₗ[ZMod 2] Y) (hf : Function.Surjective f)
    (g : Y →ₗ[ZMod 2] Y) (hg : ∀ x, g (f x) = f x) : g = 1 := by
  apply LinearMap.ext
  intro y
  obtain ⟨x,rfl⟩ := hf y
  exact hg x

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Full-module Thompson fixedness excludes every original moved fixed vector. -/
theorem Context.moved_fixed_eq_bot_of_fullModule_centralized
    (c : Context D t v I)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    sourceMovedFixed D = ⊥ := by
  have hf : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
    by_contra hn
    exact Selection.ModuleChoice.local_thompson_moves_of_full_fixed_ne_bot D c.many hn
      (hJ.trans (centralizer_le (le_componentOrbit _ _)))
  rw [c.moved_fixed_eq_orbit_fixed]
  apply bot_unique
  apply (inf_le_inf_right _ ?_).trans_eq hf
  exact le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)

/-- A faithful containing central section must have larger dimension than
the original moved subgroup fixed by the Thompson subgroup. -/
theorem Context.no_small_faithful_section_of_fullModule_centralized
    (c : Context D t v I) (a : ActionFacts c)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    letI := source_original_full_moved_elementary D
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∀ (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N)),
      Function.Injective s.action →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) ≤
        Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) → False := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let W := ⁅D.fullModule,L⁆
  let := c.reduced.normal
  let := c.reduced.elementary
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  let A := (I.subgroupOf H).map (actionMk U)
  let N := offenderSubgroup (action U)
  dsimp only
  intro s hfaith hdim
  have hAN : A ≤ N := a.classification.2.1
  have hm : moved ((action U).comp N.subtype) (A.subgroupOf N) = ⊤ := by
    rw [moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.fully_moved_of_moved_le hspan
  let p := s.fullProjection hm
  let j : W →* U := (subgroupOfEquivOfLe c.orbit_le_join).symm.toMonoidHom.comp
    (inclusion hspan)
  let jlin : Additive W →ₗ[ZMod 2] Additive U := j.toAdditive.toZModLinearMap 2
  let f := p.comp jlin
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro w hw
    have hfix := (s.fullProjection_eq_zero_iff hm (jlin w)).mp hw
    have hc : (w.toMul : G) ∈ centralizer (L : Set G) := by
      intro l hl
      let lH : H := ⟨l,(c.escaping.strict.le.trans le_sup_left) hl⟩
      let lA : A := ⟨actionMk U lH,mem_map_of_mem _ (c.escaping.strict.le hl)⟩
      have hh := hfix ⟨⟨lA,hAN lA.property⟩,lA.property⟩
      have hh' := congrArg (fun z : Additive U => ((z.toMul : H) : G)) hh
      have ha := congrArg H.subtype (action_apply U lH (jlin w))
      have he : l * (w.toMul : G) * l⁻¹ = (w.toMul : G) := ha.symm.trans hh'
      exact mul_inv_eq_iff_eq_mul.mp he
    have hz : (w.toMul : G) ∈ sourceMovedFixed D := ⟨w.toMul.property,hc⟩
    rw [c.moved_fixed_eq_bot_of_fullModule_centralized hJ] at hz
    exact Additive.toMul.injective (Subtype.ext (mem_bot.mp hz))
  have hsur : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    have he : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) =
        Module.finrank (ZMod 2) f.range := (LinearEquiv.ofInjective f hfi).finrank_eq
    exact le_antisymm (Submodule.finrank_le _) (hdim.trans he.le)
  obtain ⟨P,hP⟩ := c.join_sylow
  have hPN : (elementaryAbelianMaxJ (pointSylow T v)).subgroupOf H ≤
      N.comap (actionMk U) := by
    have hmap : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (pointSylow T v) := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
    have he : (elementaryAbelianMaxJ (pointSylow T v)).subgroupOf H =
        elementaryAbelianMaxJ (P : Subgroup H) := by
      rw [←hmap]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [he]
    exact map_le_iff_le_comap.mp (thompson_image_le P U)
  apply a.prepared.thompson_moves
  intro z hz w hw
  have hJS : elementaryAbelianMaxJ (pointSylow T v) ≤ pointSylow T v :=
    sSup_le fun _ hA => hA.1
  have hzH : z ∈ H := (show pointSylow T v ≤ H from le_sup_right)
    (hJS hz)
  let zH : H := ⟨z,hzH⟩
  let zN : N := ⟨actionMk U zH,hPN hz⟩
  have hact' (u : Additive W) : s.central.quotientRepresentation zN (f u) = f u := by
    change s.central.quotientRepresentation zN (p (jlin u)) = p (jlin u)
    rw [←s.fullProjection_intertwines hm zN]
    apply congrArg p
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    have ha := congrArg H.subtype (action_apply U zH (jlin u))
    change _ = z * (u.toMul : G) * z⁻¹ at ha
    rw [a.prepared.thompson_eq] at hz
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact ha.trans (by
      rw [←hJ hz u.toMul (hWV u.toMul.property),mul_inv_cancel_right]
      rfl)
  have hact : s.central.quotientRepresentation zN = 1 :=
    end_eq_one_of_surjective f hsur _ hact'
  have hzq : actionMk U zH = 1 := congrArg Subtype.val
    (hfaith (hact.trans (map_one s.action).symm))
  have hzk : zH ∈ centralizer (U : Set H) := (QuotientGroup.eq_one_iff zH).mp hzq
  exact congrArg H.subtype (hzk ⟨w,c.orbit_le_join hw⟩ hw)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
