module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.LocalRows
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.Separation
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.PairComponentAlignment
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairModule
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import CFSG.Quasithin.Chapter10.SourceA5NumericalSelection
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement

/-!
# Separated support from the actual moving local module

The native B.5 two-factor row places the two original components in
opposite factors. Its quotient summands are fixed by the opposite factor;
perfectness lifts that fixation through the global fixed kernel. The
literal conjugation action then separates the original local commutator.
Its nonzero second commutator gives nonzero fixed support in the original
full module, and source reselection minimality gives crossed centralization.

When the full fixed layer is positive, the original 3.1.8 omega-center
alternative forces the needed local Thompson movement. No natural model,
full/local equality, or chosen-support assertion is assumed in this branch.
The remaining coordinate classification and quiet-module tensor exclusions
stay with qt-d-10-nona5-point-selection.

Source: Aschbacher--Smith B.5.6, 3.1.8(3), 3.2.2(6), 3.2.6 and10.1.1,
printed pp.105,576,579,581,741.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02

private theorem source_first_fixed {Q V : Type*} [Group Q] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) Q V}
    (d : ChapterB.SourceInduction.SourceTwoFactorCase ρ)
    (B : Subgroup Q) [Group.IsPerfect B] (hB : B ≤ d.second) :
    d.firstSpace.toSubmodule ≤ fixedSpace ρ B := by
  apply le_fixedSpace_of_commutator_le_fixedSpace ρ B d.firstSpace.toSubmodule
    (le_subspaceStabilizer _ _ (fun b _ v hv => d.firstSpace.apply_mem_toSubmodule b hv))
  apply Submodule.span_le.mpr
  rintro _ ⟨b,hb,v,hv,rfl⟩
  have hh := congrArg Subtype.val (d.second_fixes_first ⟨b,hB hb⟩
    ⟨ρ.invariants.mkQ v, ⟨v,hv,rfl⟩⟩)
  have hz : ρ.invariants.mkQ (ρ b v - v) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hh
  exact fun b' => (Submodule.Quotient.mk_eq_zero _).mp hz b'

private theorem source_two_factor_crossed {Q V : Type*} [Group Q] [Finite Q]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) Q V}
    (d : ChapterB.SourceInduction.SourceTwoFactorCase ρ)
    {A B : Subgroup Q} (hA : IsComponent Q A) (hB : IsComponent Q B) (hne : A ≠ B) :
    subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B := by
  let := hB.2
  rcases d.component_alignment hA hB hne with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact (Submodule.span_mono (by
      rintro _ ⟨a,ha',v,hv,rfl⟩
      exact ⟨a,ha ha',v,hv,rfl⟩)).trans
      (d.firstCase.moved_le_space.trans (source_first_fixed d B hb))
  · let d' : ChapterB.SourceInduction.SourceTwoFactorCase ρ := {
      first := d.second
      second := d.first
      product := d.product.swap
      firstSpace := d.secondSpace
      secondSpace := d.firstSpace
      decomposition := d.decomposition.symm
      firstCase := d.secondCase
      secondCase := d.firstCase }
    exact (Submodule.span_mono (by
      rintro _ ⟨a,ha',v,hv,rfl⟩
      exact ⟨a,ha ha',v,hv,rfl⟩)).trans
      (d.secondCase.moved_le_space.trans (source_first_fixed d' B hb))

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Thompson movement separates the original local module on the original pair. -/
theorem local_moved_centralizes_partner
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅D.moduleSubgroup,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let := (D.module_reduced (source_module_nonsolvable_uniqueness D)).normal
  let := (D.module_reduced (source_module_nonsolvable_uniqueness D)).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let Y := offenderSubgroup ρ
  let σ := ρ.comp Y.subtype
  let X := (localOrbit T L).subgroupOf H
  let A := L.subgroupOf H
  let tH : H := ⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hUH : D.moduleSubgroup ≤ H :=
    D.module_le_sylow.trans (show (T : Subgroup G) ≤ H from le_sup_right)
  have hXY : X.map q ≤ Y := local_orbit_image_le_offender D hJ
  have hAX : A ≤ X := comap_mono (le_componentOrbit L T)
  have hBX : B ≤ X := by
    rintro b ⟨a,ha,rfl⟩
    have hXn : H ≤ normalizer (localOrbit T L : Set G) :=
      sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    exact (mem_normalizer_iff.mp (hXn tH.property) a).mp (hAX ha)
  have hAY : A.map q ≤ Y := (map_mono hAX).trans hXY
  have hBY : B.map q ≤ Y := (map_mono hBX).trans hXY
  obtain ⟨hAq,hBq,hne⟩ := local_action_component_pair D ht htn
  have hneY : (A.map q).subgroupOf Y ≠ (B.map q).subgroupOf Y := by
    intro he
    apply hne
    have hh := congrArg (map Y.subtype) he
    simpa only [map_subgroupOf_eq_of_le hAY,map_subgroupOf_eq_of_le hBY] using hh
  obtain ⟨d⟩ := local_module_two_factor_case D (fun hn => htn (hn ht)) hJ
  have hc := source_two_factor_crossed d (hAq.subgroupOf hAY) (hBq.subgroupOf hBY) hneY
  have hcross : ⁅U,A⁆ ≤ centralizer (B : Set H) := by
    intro v hv b hb
    let w : Additive U := Additive.ofMul ⟨v,(commutator_le_left U A) hv⟩
    have hw : w ∈ subspaceCommutator ρ ⊤ (A.map q) := by
      change w ∈ subspaceCommutator
        (NormalElementaryQuotient.representation U q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (A.map q)
      rw [← NormalElementaryQuotient.commutatorSpace_eq U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)]
      exact hv
    have hw' : w ∈ subspaceCommutator σ ⊤ ((A.map q).subgroupOf Y) := by
      rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAY]
      exact hw
    have hbq : q b ∈ B.map q := mem_map_of_mem q hb
    have he := hc hw' (⟨⟨q b,hBY hbq⟩,hbq⟩ : (B.map q).subgroupOf Y)
    have he' := congrArg (fun z : Additive U => (z.toMul : H)) he
    change ((ρ (q b) w).toMul : H) = v at he'
    rw [ChapterB.InternalThompsonAction.action_apply] at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le hLH
  have hmapB : B.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [map_map,show H.subtype.comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype from rfl,←map_map,hmapA]
  have hmapU : U.map H.subtype = D.moduleSubgroup := map_subgroupOf_eq_of_le hUH
  intro v hv b hb
  rw [←hmapU,←hmapA,←map_commutator] at hv
  rw [←hmapB] at hb
  obtain ⟨v,hv,rfl⟩ := hv
  obtain ⟨b,hb,rfl⟩ := hb
  exact congrArg H.subtype (hcross hv b hb)

/-- The original local module is moved by each original component. -/
theorem local_moved_ne_bot : ⁅D.moduleSubgroup,L⁆ ≠ ⊥ := by
  intro he
  have hLC : L ≤ centralizer (D.moduleSubgroup : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  have hOC : localOrbit T L ≤ centralizer (D.moduleSubgroup : Set G) :=
    iSup_conjugates_le_of_le_normalizer L T _ hLC
      (D.sylow_normalizes_module.trans (normalizer_le_normalizer_centralizer _))
  apply D.module_ne_bot
  exact (local_module_eq_commutator D).trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hOC))

/-- A moving local Thompson subgroup gives the support required by the
minimal full-module selection, without replacing its seed. -/
theorem fixed_support_moved_of_local_thompson
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅D.fullModule ⊓ centralizer
      (L.map (MulAut.conj t).toMonoidHom : Set G), L⁆ ≠ ⊥ := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  have hW : ⁅D.moduleSubgroup,L⁆ ≤ D.fullModule :=
    (le_normalizer_iff_commutator_le_left.mp
      ((le_componentOrbit L T).trans D.orbit_normalizes_module)).trans
      (le_componentOrbit D.moduleSubgroup D.maximalLocal)
  intro he
  apply local_moved_ne_bot D
  apply commutator_eq_bot_of_iterated_eq_bot
  exact bot_unique ((commutator_mono
    (le_inf hW (local_moved_centralizes_partner D hJ ht htn)) le_rfl).trans_eq he)

/-- The selected original full module has the literal crossed centralization
in every moving local Thompson case. -/
theorem crossed_of_minimal_local_thompson
    (hmin : D.IsMinimalFullModule)
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  crossed_of_minimal_fixed_support D hmin ht htn
    (fixed_support_moved_of_local_thompson D hJ ht htn)

/-- Nonzero fixed vectors on the full orbit force Thompson movement on the
original local module by the source 3.1.8 alternative. -/
theorem local_thompson_moves_of_full_fixed_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G) := by
  have hu := source_module_nonsolvable_uniqueness D
  have hc : D.fullCentralizer ≠ ⊥ := by
    intro he
    apply hfixed
    apply bot_unique
    intro x hx
    have hx' : (⟨x,hx.1⟩ : D.fullModule) ∈ D.fullCentralizer := hx.2
    have hx1 := Subgroup.mem_bot.mp (he ▸ hx')
    exact Subgroup.mem_bot.mpr (congrArg D.fullModule.subtype hx1)
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (source_maximalOutside_of_many D hmany)
  have hz := D.omega_center_not_le_center_of_fullCentralizer_ne_bot hu hc hH
  have huniq := D.lemma_3_2_3_uniqueness hu
  exact (D.qrcHypotheses hu hH).thompson_moves_of_noncentral_omega
    D.simpleQTKE huniq.1 huniq.2.2 D.module_ne_bot hz

/-- Positive full fixed layers already have the required separated support. -/
theorem fixed_support_moved_of_full_fixed_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅D.fullModule ⊓ centralizer
      (L.map (MulAut.conj t).toMonoidHom : Set G), L⁆ ≠ ⊥ :=
  fixed_support_moved_of_local_thompson D
    (local_thompson_moves_of_full_fixed_ne_bot D hmany hfixed) ht htn

/-- The source positive-fixed-layer branch supplies crossed centralization
for the same selected setup and exchanger. -/
theorem crossed_of_minimal_full_fixed_ne_bot
    (hmin : D.IsMinimalFullModule)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  crossed_of_minimal_local_thompson D hmin
    (local_thompson_moves_of_full_fixed_ne_bot D hmany hfixed) ht htn

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
