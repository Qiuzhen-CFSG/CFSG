module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Quiet.SuzukiTwoFactors
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SuzukiProductCentralizer
public import Theory.Representation.BinaryOffender.NormalRestriction

/-!
# Exclusion of the actual quiet Suzuki configuration

The offender subgroup inside the orbit centralizer has normal image in the
full faithful actor. Original quiet minimality makes that full action
irreducible, so the nontrivial offender subgroup has zero fixed space.
Apply the two-factor exclusion on its literal fixed-space quotient, using
the existing orbit-submodule degree bound. This closes the final Suzuki
branch under the original small-offender configuration.

Source: Aschbacher–Smith 10.1.1–2 and 10.2.12, pp.741–742 and754–755;
B.5.6(3), p.105. The remaining independent half-Sylow input is retained in
SmallOffender.Complete for final source assembly.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 BenderSuzuki.MatrixGroups PointControl.Selection
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem no_quiet_suzuki_smallOffender
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) : False := by
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let Q := M ⧸ centralizer (U : Set M)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let C := centralizer (X : Set Q)
  let N := offenderSubgroup (ρ.comp C.subtype)
  let f := C.subtype.comp N.subtype
  let A := L.subgroupOf M
  let S := A.map q
  have hLM : L ≤ M := (le_componentOrbit L T).trans R.le_normalizer
  obtain ⟨a⟩ := ModuleChoice.full_action_original_component_equiv D c.nonnormal
  let eS : S ≃* SuzukiMatrixGroup m := a.trans e
  have hfull := quiet_suzuki_moved_eq_full D c hJ hNL hm e
  have hz := quiet_moved_fixed_eq_bot D c.many c.minimal c.nonnormal hJ
  rw [hfull] at hz
  have hfixS : fixedSpace ρ S = ⊥ := by
    apply bot_unique
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    apply hz.le
    refine ⟨v.toMul.property,?_⟩
    intro l hl
    let lM : M := ⟨l,hLM hl⟩
    have hh := hv ⟨q lM,mem_map_of_mem q hl⟩
    have hact := ChapterB.InternalThompsonAction.action_apply U lM v
    have he : l * (v.toMul : G) * l⁻¹ = (v.toMul : G) := by
      exact (congrArg (fun x : M => (x : G)) hact).symm.trans
        (congrArg (fun x : Additive U => ((x.toMul : M) : G)) hh)
    exact mul_inv_eq_iff_eq_mul.mp he
  have hSX : S ≤ X := map_mono (comap_mono (le_componentOrbit L T))
  have hc : f.range ≤ centralizer (S : Set Q) := by
    rintro _ ⟨n,rfl⟩ s hs
    exact n.val.property s (hSX hs)
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLM).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLM).symm.surjective
  let : Group.IsPerfect S := Group.IsPerfect.map q
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : C.Normal := inferInstance
  have hf := ChapterB.InternalThompsonAction.action_faithful U
  have hi := ModuleChoice.quiet_full_action_irreducible D c.many c.minimal hJ
  have hff := (quiet_suzuki_orbit_centralizer_nonsolvable_ff D c hJ hNL hm e).2
  have hzN : Representation.invariants (ρ.comp f) = ⊥ :=
    normal_restriction_offender_fixed_eq_bot ρ hf hi C
      (offenderSubgroup_ne_bot_of_ff _ hff)
  obtain ⟨d⟩ := quiet_suzuki_centralizer_two_factors D c hJ hNL hm e
  apply not_twoFactors_of_commuting_suzuki ρ S (by omega) eS hfixS f hc hzN ?_ d
  intro B hB
  change 24 ≤ Module.finrank (ZMod 2) (subspaceCommutator (ρ.comp f) ⊤ B)
  rw [subspaceCommutator_comp_map]
  apply degree_le_moved_finrank_of_commuting ρ X (B.map f)
  · intro W hW
    have hd := quiet_suzuki_orbit_submodule_degree D c hJ hNL hm e W hW
    exact (by omega : 24 ≤ 8*(2*m+1)).trans hd
  · intro h
    apply hB
    apply bot_unique
    intro b hb
    apply (C.subtype_injective.comp N.subtype_injective)
    apply hf
    exact (h (mem_map_of_mem f hb)).trans (by simp)
  · rintro _ ⟨b,hb,rfl⟩
    exact b.val.property

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
