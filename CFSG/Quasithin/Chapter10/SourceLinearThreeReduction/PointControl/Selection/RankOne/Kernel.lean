module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.BinaryConjugationSection.Cover

/-!
# Original kernels in the rank-one natural row

Faithfulness of the natural matrix action identifies the coordinate kernel
with O₂(L). That two-core centralizes the original full module. Full commutator
generation therefore removes every hidden normalizer action on the fixed
kernel, and the original conjugation action descends faithfully to SL₂.
The field, quotient map, moved factor and its entire fixed kernel are retained.
Source: Aschbacher--Smith, 10.1.1(1), 10.2.9, printed pp.741,750--751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
  (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
    (SL2.BinarySmall.natural.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

include e c

omit [Finite F] in
/-- The literal natural quotient has precisely the original component two-core as kernel. -/
theorem moved_quotient_kernel :
    commutatorPreimage L ⁅D.fullModule,L⁆ (sourceMovedFixed D) = L.pCoreIn 2 := by
  have hf : Function.Injective (SL2.BinarySmall.natural (K := F)) := by
    intro x y h
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    exact fun v => LinearMap.congr_fun h v
  have hn : L ≤ normalizer (sourceMovedFixed D : Set G) :=
    (le_inf L.le_normalizer (normalizer_commutator_ge_right _ _)).trans
      (source_original_moved_fixed_normalizer D)
  have he := c.action_kernel_map hn
  rw [MonoidHom.ker_comp_of_injective _ _ hf,
    MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,
    QuotientGroup.ker_mk'] at he
  exact he.symm

omit [Finite F] in
/-- No common normalizer action is hidden in the component-fixed quotient kernel. -/
theorem moved_normalizer_quotient_kernel :
    commutatorPreimage
      (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
      ⁅D.fullModule,L⁆ (sourceMovedFixed D) =
    (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ⊓
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let H := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  have hAH : L ≤ H := le_inf L.le_normalizer (normalizer_commutator_ge_right _ _)
  have hker : commutatorPreimage L W (sourceMovedFixed D) ≤ centralizer (W : Set G) := by
    rw [moved_quotient_kernel D e c]
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact (source_component_core_centralizes_fullModule D).trans (centralizer_le hWV)
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _)
      (commutatorPreimage_le_centralizer_of_fully_moved H L W (sourceMovedFixed D)
        hAH inf_le_left inf_le_right (source_original_moved_fixed_normalizer D)
        inf_le_right (source_full_moved_eq_commutator D) hker)
  · apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

omit [Finite F] in
/-- Faithful SL₂ action on the full moved factor, with literal original conjugation. -/
theorem moved_action :
    ∃ σ : Representation (ZMod 2) SL(2,F) (Additive (⁅D.fullModule,L⁆ : Subgroup G)),
      Function.Injective σ ∧
      ∀ (l : L) (w : Additive (⁅D.fullModule,L⁆ : Subgroup G)),
        ((σ (e (QuotientGroup.mk' (pCore 2 L) l)) w).toMul : G) =
          l * w.toMul * (l : G)⁻¹ := by
  let W := ⁅D.fullModule,L⁆
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨σ,hσ⟩ := BinaryConjugationSection.exists_action_of_central_kernel
    L W (normalizer_commutator_ge_right _ _) π hπ (by
      intro l hl
      have hp : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
        (e.injective (hl.trans e.map_one.symm))
      exact centralizer_le hWV (source_component_core_centralizes_fullModule D
        (mem_map_of_mem L.subtype hp)))
  obtain ⟨q,hq,_⟩ := c.exists_cover_of_fully_moved SL2.BinarySmall.natural π hπ σ hσ
    inf_le_right (source_full_moved_eq_commutator D)
  refine ⟨σ,?_,hσ⟩
  intro x y h
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  obtain ⟨w,rfl⟩ := hq.1 v
  exact (LinearMap.congr_fun (q.isIntertwining' x) w).symm.trans
    ((congrArg (fun f => q (f w)) h).trans (LinearMap.congr_fun (q.isIntertwining' y) w))


end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
