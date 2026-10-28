module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceMarking
public import Theory.Representation.NormalPSubgroupKernel

/-!
# The original point core fixes the seed quotient

The natural L-action makes V/V₁ irreducible already under L₁. It is
therefore irreducible under L₁T, and the normal two-core R₁ acts trivially.
The literal quotient action converts this into [R₁,V] ≤ V₁ and hence
fixedness in the original U/V₁ coordinates. The compatible target
remarking then supplies both fields of LocalActors without a seed-fixing
premise.

Source: Aschbacher–Smith, 12.8.1–2 and 14.7.65, printed pp.849,1070.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion
open Subgroup Representation Chapter12.Section08 LocalGeometry.Preparation
open scoped IsMulCommutative MonoidAlgebra
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

include d in
/-- The natural point quotient kills the intrinsic core of L₁T. -/
theorem point_core_commutator_seed : ⁅F.Ri L 1, V⁆ ≤ F.Vi 1 := by
  let := d.natural.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hBV : group F L ≤ normalizer (V : Set G) :=
    sup_le ((F.Li_le L 1).trans (inf_le_left.trans d.natural.chosen.normalizes))
      (by simpa only [F.last] using F.invariant 3)
  let f := F.tildeAction (group F L) V group_le_H hBV
  let ρ := Representation.elementaryRepresentation (p := 2) f
  let τ := F.localSeedRepresentation L d.natural.chosen.normalizes
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide : 3 ≤ 3)
    L d.natural.chosen.normalizes d.natural.naturalMarking
  let : τ.IsIrreducible := (irreducible_iff_isSimpleModule_asModule τ).mpr (D.seed_simple (by decide))
  let : Nontrivial (Additive (F.tilde V)) := Subrepresentation.irreducible_module_nontrivial τ
  let : ρ.IsIrreducible := by
    rw [Representation.IsIrreducible, isSimpleOrder_iff]
    refine ⟨inferInstance, fun S => ?_⟩
    let S₀ : Subrepresentation τ := {
      toSubmodule := S.toSubmodule
      apply_mem_toSubmodule l v hv := by
        exact S.apply_mem_toSubmodule
          (⟨l, (show F.Li L 1 ≤ group F L from le_sup_left) l.property⟩ : group F L) hv }
    rcases eq_bot_or_eq_top S₀ with he | he
    · left
      apply le_antisymm _ bot_le
      intro v hv
      exact (show v ∈ (⊥ : Subrepresentation τ) from he ▸ hv)
    · right
      apply top_unique
      intro v _
      exact (show v ∈ S₀ from he ▸ (show v ∈ (⊤ : Subrepresentation τ) from trivial))
  have hk : pCore 2 (group F L) ≤ ρ.ker :=
    normal_p_subgroup_le_ker ρ (pCore 2 (group F L)) pCore_isPGroup
  apply commutator_le.mpr
  intro r hr v hv
  obtain ⟨r, hr, rfl⟩ := hr
  have hrf : r ∈ f.ker := by
    apply MulEquiv.ext
    intro w
    have he := LinearMap.congr_fun (hk hr) (Additive.ofMul w)
    exact Additive.ofMul.injective he
  exact (F.mem_tildeAction_ker_iff (group F L) V group_le_H
    ((Data.V_le_U F).trans d.conjugationSection.section_le)
    hBV r).mp hrf v hv

/-- The actual R₁ action fixes the original seed image inside U/V₁. -/
theorem seed_fixed : ∀ r : F.H, (r : G) ∈ F.Ri L 1 → ∀ v : F.U, (v : G) ∈ V →
    d.action r (d.conjugationSection.coordinates v).toAdd =
      (d.conjugationSection.coordinates v).toAdd := by
  intro r hr v hv
  apply d.conjugationSection.fixed_on_imageSpace_of_commutator_le
    (F.Ri L 1) V (point_core_commutator_seed d) r hr
  exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr ⟨v, hv, rfl⟩

/-- Compatible local actors, with both the seed fixedness and cubic proved. -/
theorem localActors_of_source
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    MarkedSpans.LocalActors (Goldschmidt.LeftChiefFactors.BorelRefinements.upperRemark d structural) :=
  Goldschmidt.LeftChiefFactors.BorelRefinements.upperRemark_localActors d structural (seed_fixed d)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion
