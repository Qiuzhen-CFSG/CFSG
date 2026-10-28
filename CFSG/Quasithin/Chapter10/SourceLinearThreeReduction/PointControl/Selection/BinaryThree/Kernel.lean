module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Contracts
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import Theory.Representation.BinaryConjugationSection.Cover
public import Theory.Representation.SLThreeCentralExtension

/-!
# The fixed kernel of the original binary-three moved factor

The literal natural quotient descends the action on W=[V,L] through L/O₂(L).
Full commutator generation makes its coordinate projection a central cover.
The checked dual H¹ calculation bounds the covering kernel by one binary
dimension, so C_W(L) has at most two elements. Splitting and irreducibility
of an arbitrary chosen setup are not assumed.
Source: Aschbacher--Smith, B.4.8(1), applied in 10.2.8, printed p.749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The fixed kernel of the literal moved natural quotient has at most two elements. -/
theorem moved_fixed_card_le_two (hmodel : BinaryThreeNatural D) :
    Nat.card (sourceMovedFixed D) ≤ 2 := by
  obtain ⟨e,⟨c⟩⟩ := hmodel
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
  obtain ⟨p,hp,hpcoord⟩ := c.exists_cover_of_fully_moved (specialLinearNatural 3) π hπ σ hσ
    inf_le_right (source_full_moved_eq_commutator D)
  let : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) p.toLinearMap.ker ≤ 1 := by
    have hh := OneCohomology.finrank_ker_le_H1_of_cover p hp
    rwa [OneCohomology.SLThreeCentralExtension.finrank_H1_dual] at hh
  have hcard : Nat.card p.toLinearMap.ker ≤ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim).trans_eq (by norm_num)
  have hker (w : Additive W) : p w = 0 ↔ (w.toMul : G) ∈ sourceMovedFixed D := by
    rw [hpcoord w]
    exact c.coordinates_eq_one_iff w.toMul
  let f : sourceMovedFixed D → p.toLinearMap.ker := fun z =>
    ⟨Additive.ofMul ⟨z,(show (z : G) ∈ W ⊓ centralizer (L : Set G) from z.property).1⟩,
      (hker _).mpr z.property⟩
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun x : p.toLinearMap.ker => (x.val.toMul : G)) h)
  exact (Nat.card_le_card_of_injective f hf).trans hcard

end CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
