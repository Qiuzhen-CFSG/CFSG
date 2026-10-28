module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.Alternatives
public import CFSG.Quasithin.ChapterE.Section04.AlternatingFive.Local

/-!
# Full local automizer parameters of the original A₅ moved factor

The entire M-normalizer of W=[V,L] acts faithfully on W/C_W(L): the source
kernel theorem removes the possible central-cover kernel. Its image normalizes
the actual irreducible A₅ action, whose full normalizer has two-rank at most
two. This bounds the original W-module parameter, including every outer actor.
In the deleted-permutation branch W itself is the marked module; its full
normalizer has parameter at most one. The source separate-factor condition
discharges component normalization. The chosen-setup irreducibility and
separate-factor input stay explicit for the original 3.2.6/10.1.1 producers.
Source: Aschbacher–Smith, 10.2.12, printed pp.754–755.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The full original local action has parameter at most two after the source choice. -/
theorem source_a5_original_local_moduleA_le_two
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hNL : D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    moduleA ((automizerRepresentation ⁅D.fullModule,L⁆).comp
      (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal).subtype) ≤ 2 := by
  let W := ⁅D.fullModule,L⁆
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
  exact moduleA_le_two_of_alternatingFive_normalizer
    ((automizerRepresentation W).comp (inducedAutomizer W D.maximalLocal).subtype)
    ((automizerRepresentation_injective W).comp Subtype.val_injective)
    (originalMovedQuotientAction D e) (originalMovedQuotientAction_faithful D e) hi f hf

/-- The deleted branch gives parameter at most one on the same full local automizer. -/
theorem source_a5_original_local_moduleA_le_one_of_deleted
    (f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hNL : D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    moduleA ((automizerRepresentation ⁅D.fullModule,L⁆).comp
      (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal).subtype) ≤ 1 := by
  exact moduleA_local_deleted_section_le_one L ⁅D.fullModule,L⁆ D.maximalLocal
    (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (f.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))) c
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) hNL

/-- The source's separate factors discharge component normalization in the full local bound. -/
theorem source_a5_original_local_moduleA_le_two_of_separate_factors
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    moduleA ((automizerRepresentation ⁅D.fullModule,L⁆).comp
      (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal).subtype) ≤ 2 :=
  source_a5_original_local_moduleA_le_two D e hi
    (source_original_moved_stabilizer_le_component_normalizer D ht htn hcross)

local instance originalParameterFieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- The source markings carry their upper parameters on the literal full local automizer. -/
theorem source_a5_original_local_module_alternatives
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    (∃ f : alternatingGroup (Fin 5) ≃*
        SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
        (sourceMovedFixed D)
        (Representation.SL2.BinarySmall.natural.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) ∧
      moduleA ((automizerRepresentation ⁅D.fullModule,L⁆).comp
        (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal).subtype) ≤ 2) ∨
    (sourceMovedFixed D = ⊥ ∧
      ∃ f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5),
      Nonempty (Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
          (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) ∧
      moduleA ((automizerRepresentation ⁅D.fullModule,L⁆).comp
        (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal).subtype) ≤ 1) := by
  have hn := source_original_moved_stabilizer_le_component_normalizer D ht htn hcross
  rcases source_a5_original_module_alternatives_of_irreducible D e hi with
    ⟨f,c⟩ | ⟨hz,f,⟨c⟩⟩
  · exact Or.inl ⟨f,c,source_a5_original_local_moduleA_le_two D e hi hn⟩
  · exact Or.inr ⟨hz,f,⟨c⟩,source_a5_original_local_moduleA_le_one_of_deleted D e f c hn⟩

end CFSG.Quasithin.Chapter10
