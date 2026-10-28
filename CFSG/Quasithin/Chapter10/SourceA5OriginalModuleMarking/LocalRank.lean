module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.LocalParameters

/-!
# Two-rank of the full original moved-factor automizer

The full local automizer embeds faithfully in the normalizer of the literal
irreducible A₅ quotient action. That normalizer has two-rank at most two.
This retains all local actors and the central-cover kernel needed by the
weak-closure argument in Aschbacher–Smith, 10.2.12, printed pp.754–755.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

theorem source_a5_original_local_primeRank_le_two
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hNL : D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    primeRank 2 (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal) ≤ 2 := by
  let W := ⁅D.fullModule,L⁆
  let V := Additive (W ⧸ (sourceMovedFixed D).subgroupOf W)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have hLM : L ≤ D.maximalLocal := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hNZ := (le_inf hNL (show D.maximalLocal ⊓ normalizer (W : Set G) ≤
    normalizer (W : Set G) from inf_le_right)).trans (source_original_moved_fixed_normalizer D)
  have hk : commutatorPreimage (D.maximalLocal ⊓ normalizer (W : Set G)) W
      (sourceMovedFixed D) ≤ centralizer (W : Set G) := by
    rw [source_a5_original_local_quotient_kernel D e hNL]
    exact inf_le_right
  obtain ⟨τ,f,hf,_,_⟩ := exists_local_section_normalizer L W (sourceMovedFixed D) D.maximalLocal
    (originalMovedQuotientAction D e)
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (originalMovedQuotientSection D e) hLM hNL hNZ hk
  exact (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans
    (primeRank_alternatingFive_linearNormalizer_le_two
      (originalMovedQuotientAction D e) (originalMovedQuotientAction_faithful D e) hi)

end CFSG.Quasithin.Chapter10
