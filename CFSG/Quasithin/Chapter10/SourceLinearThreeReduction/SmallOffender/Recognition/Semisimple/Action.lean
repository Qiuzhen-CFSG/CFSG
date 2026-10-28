module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Irreducible.Action
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietAction
public import Theory.Representation.CliffordRestriction
public import Theory.Representation.NormalSemisimpleSpan

/-!
# Complete reducibility of the original quiet moved quotient

Quiet minimality makes the full M-action irreducible. Clifford restriction
along L normal in L₀ normal in M gives complete reducibility on L. The
inclusion of W = [V,L] and the literal coordinate map W → W/C_W(L) transfer
this to every marking of the original component quotient. No irreducibility
of an arbitrary fixed setup or component module is assumed.

Source: Aschbacher–Smith D.3.6–7 and 10.1.1, printed pp.196–197,741.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal moved central quotient is semisimple in the original quiet minimal setup. -/
theorem quiet_moved_section_semisimple
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) J V)
    (e : (L ⧸ pCore 2 L) ≃* J)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    IsSemisimpleModule (ZMod 2)[J] σ.asModule := by
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
  let : IsSemisimpleModule (ZMod 2)[L] ω.asModule :=
    IsSemisimpleModule.of_injective fm (by
      intro x y h
      apply Additive.toMul.injective
      apply Subtype.ext
      exact congrArg (fun z : Additive U => ((z.toMul : M) : G)) h)
  let qL := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let b : ω.IntertwiningMap (σ.comp qL) := {
    toLinearMap := ({
      toFun := fun w => (s.coordinates w.toMul).toAdd
      map_zero' := s.coordinates.map_one
      map_add' x y := s.coordinates.map_mul x.toMul y.toMul } : Additive W →+ V).toZModLinearMap 2
    isIntertwining' l := by
      apply LinearMap.ext
      intro w
      exact s.equivariant l w.toMul }
  let : IsSemisimpleModule (ZMod 2)[L] (Representation.asModule (σ.comp qL)) :=
    IsSemisimpleModule.of_surjective (IntertwiningMap.equivLinearMapAsModule _ _ b)
      (by
        intro v
        obtain ⟨w,hw⟩ := s.onto (Multiplicative.ofAdd v)
        exact ⟨Additive.ofMul w,congrArg Multiplicative.toAdd hw⟩)
  exact (semisimple_comp_iff_of_surjective σ qL
    (e.surjective.comp (QuotientGroup.mk'_surjective _))).mp inferInstance

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
