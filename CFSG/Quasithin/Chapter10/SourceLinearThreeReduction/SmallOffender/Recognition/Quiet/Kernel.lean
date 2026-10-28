module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Semisimple.Action
public import Theory.Representation.BinaryConjugationSection.Coinvariants
public import Theory.Representation.SemisimpleCoinvariants

/-!
# Vanishing of the original quiet moved kernel

Clifford restriction along L normal in L₀ normal in M makes the actual
moved subgroup W = [V,L] semisimple. Since W = [W,L], its coinvariants
vanish. A semisimple module is the sum of its fixed and moved parts, so
W has no nonidentity L-fixed element. This removes the central kernel
before recognizing a model, and feeds the quiet TI reduction.

Source: Aschbacher–Smith D.3.6–7 and 10.1.1, printed pp.196–197,741.
-/

public noncomputable section
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Complete reducibility of the literal moved group, before quotienting. -/
theorem quiet_moved_action_semisimple
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    let := source_full_moved_elementary D
    let ω : Representation (ZMod 2) L (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
      elementaryRepresentation ((⁅D.fullModule,L⁆ : Subgroup G).normalizerMonoidHom.comp
        (inclusion (normalizer_commutator_ge_right D.fullModule L)))
    IsSemisimpleModule (ZMod 2)[L] ω.asModule := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let := (source_full_module_reduced D).elementary
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let τ : Representation (ZMod 2) M (Additive U) := ρ.comp q
  have hi : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff q (QuotientGroup.mk'_surjective _) ρ).mpr
      (ModuleChoice.quiet_full_action_irreducible D hmany hmin hJ)
  let K := L.subgroupOf M
  let N := (localOrbit T L).subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hKN : K ≤ N := comap_mono (le_componentOrbit L T)
  let : N.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hNK : N ≤ normalizer (K : Set M) := by
    intro n hn'
    rw [Subgroup.mem_normalizer_iff]
    intro k
    exact Subgroup.mem_normalizer_iff.mp
      (source_nonnormal_orbit_le_normalizer D hn hn') k
  let : IsSemisimpleModule (ZMod 2)[K] (Representation.asModule (τ.comp K.subtype)) :=
    irreducible_restriction_semisimple_of_normal_chain τ hi K N hKN hNK
  let a : L ≃* K := (subgroupOfEquivOfLe hLM).symm
  let τL : Representation (ZMod 2) L (Additive U) := τ.comp (inclusion hLM)
  let : IsSemisimpleModule (ZMod 2)[L] τL.asModule :=
    comp_semisimple_of_surjective (τ.comp K.subtype) a.toMonoidHom a.surjective
  let W := ⁅D.fullModule,L⁆
  let : IsElementaryAbelian 2 W := source_full_moved_elementary D
  have hLW : L ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
  let ω : Representation (ZMod 2) L (Additive W) := elementaryRepresentation (W.normalizerMonoidHom.comp (inclusion hLW))
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (hLM.trans D.maximalLocal_normalizes_fullModule)
  let fW : W →* U := {
    toFun w := ⟨⟨w,hLM (source_full_moved_le_component D w.property)⟩,hWV w.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let f : ω.IntertwiningMap τL := {
    toLinearMap := fW.toAdditive.toZModLinearMap 2
    isIntertwining' l := by
      apply LinearMap.ext
      intro w
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      exact (congrArg M.subtype (ChapterB.InternalThompsonAction.action_apply U
        (inclusion hLM l) (Additive.ofMul ⟨⟨w.toMul,hLM (source_full_moved_le_component D w.toMul.property)⟩,hWV w.toMul.property⟩))).symm }
  let fm := IntertwiningMap.equivLinearMapAsModule ω τL f
  exact
    IsSemisimpleModule.of_injective fm (by
      intro x y h
      apply Additive.toMul.injective
      apply Subtype.ext
      exact congrArg (fun z : Additive U => ((z.toMul : M) : G)) h)

/-- Quiet minimality kills the full component-fixed kernel in the moved group. -/
theorem quiet_moved_fixed_eq_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
  let W := ⁅D.fullModule,L⁆
  let := source_full_moved_elementary D
  let hLW := normalizer_commutator_ge_right D.fullModule L
  let ω : Representation (ZMod 2) L (Additive W) := elementaryRepresentation (W.normalizerMonoidHom.comp (inclusion hLW))
  let : IsSemisimpleModule (ZMod 2)[L] ω.asModule :=
    quiet_moved_action_semisimple D hmany hmin hn hJ
  let s : BinaryConjugationSection L W ⊥ ω := {
    section_le := source_full_moved_le_component D
    kernel_le := bot_le
    normalized := hLW
    coordinates := {
      toFun w := Multiplicative.ofAdd (Additive.ofMul w)
      map_one' := rfl
      map_mul' _ _ := rfl }
    onto := fun w => ⟨w.toAdd.toMul,rfl⟩
    kernel_eq := by
      ext w
      change w = 1 ↔ (w : G) = 1
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    equivariant := fun _ _ => rfl }
  have hgen : Coinvariants.ker ω = ⊤ :=
    s.coinvariants_eq_top_of_group_generation L le_rfl ω (MonoidHom.id L)
      (fun _ _ => rfl) (by rw [sup_bot_eq,commutator_comm,source_full_moved_eq_commutator D])
  have hfix := invariants_eq_bot_of_semisimple_of_coinvariants_eq_top ω hgen
  apply _root_.eq_bot_iff.mpr
  intro w hw
  have hv : Additive.ofMul (⟨w,hw.1⟩ : W) ∈ ω.invariants := by
    intro l
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * w * (l : G)⁻¹ = w
    rw [hw.2 l l.property,mul_inv_cancel_right]
  have hz := hfix.le hv
  exact congrArg (fun x : Additive W => (x.toMul : G)) hz

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
