module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementOffender
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ClosureSylowGeneration
public import Theory.Representation.BinaryConjugationSection.ResidualSimpleSection
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator

/-!
# A genuine residual-moving section of the replacement module

For either neighboring-center branch of 6.4, start with the actual
elementary V=<Z_delta^X> and its constructed conjugation action. The proved
residual supplement forces O²(X) to move V. A maximal quotient retaining
that movement supplies a simple section with literal original numerator
and denominator. Its faithful action image has trivial two-core, vanishing
O²-fixed space, and generation by the image of an actual Sylow of X.

The original escaping Thompson actor remains quadratic on this section,
and its fixed-space index still satisfies the original numerical bound.
The kernel is recorded exactly as a commutator preimage. Identifying the
image with the rank-one catalogue and proving that this actor survives
in the section remain necessary before corrected 5.12 can be applied.
In particular no fixed-generation claim for all of V, nor equality of its
centralizer kernel with O₂(X), is inferred from the selected section.

Source: DGS, Groups and Graphs (1985), 6.4, pp.120--121, and corrected
5.12, pp.113--115. The original completion may be infinite.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory.AmalgamGraph Representation
open Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Trivial-denominator coordinates preserve the proved residual movement of the actual replacement span. -/
theorem source_replacement_section_residual_moves
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (ρ : Representation (ZMod 2) (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))) W)
    (d : BinaryConjugationSection (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))
      (conjugateSpanBy (sylowCenterSpan (P i))
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)))) ⊥ ρ) :
    ¬ pResidual 2 (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))) ≤ ρ.ker := by
  intro hk
  apply source_replacement_residual_not_central h hB i hn
  intro v hv r hr
  obtain ⟨x,hx,rfl⟩ := hr
  exact (commutatorElement_eq_one_iff_mul_comm.mp
    (mem_bot.mp ((d.action_mem_ker_iff x).mp (hk hx) v hv)))

/-- Construct the literal simple section, its faithful image and actual Sylow, retaining the original escaping quadratic actor and index. -/
theorem source_replacement_simple_quadratic_section_of_inter_normal (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    ∃ U C : Subgroup G, U ≤ V ∧ ∃ (W : Type u) (_ : AddCommGroup W)
      (_ : Module (ZMod 2) W) (_ : Finite W) (ρ : Representation (ZMod 2) X W),
      Nonempty (BinaryConjugationSection X U C ρ) ∧ IsIrreducible ρ ∧
      ρ.ker.map X.subtype = commutatorPreimage X U C ∧ pCore 2 X ≤ ρ.ker ∧
      Function.Injective (imageRepresentation ρ) ∧ pCore 2 (actionImage ρ) = ⊥ ∧
      fixedSpace (imageRepresentation ρ) (pResidual 2 (actionImage ρ)) = ⊥ ∧
      (∃ T : Sylow 2 X, (T : Subgroup X).map X.subtype = B.pCoreIn 2 ⊓ X ∧
        ∃ R : Sylow 2 (actionImage ρ), (R : Subgroup (actionImage ρ)) =
          (T : Subgroup X).map (actionHom ρ) ∧ GeneratedByFixedSpace (imageRepresentation ρ) R) ∧
      ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
        ¬ A ≤ (P (other i)).pCoreIn 2 ∧ ¬ A ≤ X.pCoreIn 2 ∧
        IsQuadratic (imageRepresentation ρ) ((A.subgroupOf X).map (actionHom ρ)) ∧
        Nat.card (W ⧸ fixedSpace (imageRepresentation ρ)
          ((A.subgroupOf X).map (actionHom ρ))) ≤ ((P (other i)).pCoreIn 2).relIndex A := by
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let V := conjugateSpanBy (sylowCenterSpan (P i)) X
  let := (Classical.choice (h.local_data (other i))).finite_P
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans (Classical.choice (h.local_data (other i))).supplement.le))
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  have hVX : V ≤ X := ((source_replacement_span_le_inter_omega_of_inter_normal h i hn).trans
    ((map_subtype_le _).trans inf_le_left)).trans (le_conjugateSpanBy _ _)
  let : Finite V := Finite.of_injective (inclusion hVX) (inclusion_injective _)
  obtain ⟨hE,hh⟩ := source_replacement_faithful_action_of_inter_normal h i hn
  let := hE
  obtain ⟨K,hK,hh⟩ := hh
  let := hK
  obtain ⟨σ,_,_,⟨d⟩⟩ := hh
  let : Finite (Additive (V.subgroupOf X)) := inferInstance
  let : FiniteDimensional (ZMod 2) (Additive (V.subgroupOf X)) := Module.Finite.of_finite
  let ρ₀ := σ.comp (QuotientGroup.mk' K)
  obtain ⟨U,C,hUV,W,hW,hWM,hWf,ρ,⟨s⟩,hi,hker,hcore,hfaith,hzero,hres,hgen⟩ :=
    d.exists_faithful_residual_simple_section
      (source_replacement_section_residual_moves h hB i hn ρ₀ d)
  let := hW
  let := hWM
  let := hWf
  let : Finite U := Finite.of_injective (inclusion hUV) (inclusion_injective _)
  have he : (imageRepresentation ρ).comp (actionHom ρ) = ρ :=
    MonoidHom.ext (imageRepresentation_actionHom ρ)
  have simg : BinaryConjugationSection X U C ((imageRepresentation ρ).comp (actionHom ρ)) :=
    he.symm ▸ s
  refine ⟨U,C,hUV,W,hW,hWM,hWf,ρ,⟨s⟩,hi,hker,hcore,hfaith,hzero,hres,?_,?_⟩
  · obtain ⟨T,hT⟩ := source_closure_sylow_intersection h hB hS i
    exact ⟨T,hT,hgen T⟩
  · obtain ⟨A,hA,hout,houtX,hquad,hbound⟩ := source_replacement_quadratic_offender_of_inter_normal h i hn
    refine ⟨A,hA,hout,houtX,?_,?_⟩
    · apply isQuadratic_of_triple_commutator_le X U C A (imageRepresentation ρ) (actionHom ρ) simg
      have hh : ⁅A,⁅A,U⁆⁆ ≤ ⁅⁅V,A⁆,A⁆ := by
        rw [commutator_comm A ⁅A,U⁆,commutator_comm A U]
        exact commutator_mono (commutator_mono hUV le_rfl) le_rfl
      exact hh.trans (hquad.le.trans bot_le)
    · have hb := fixed_quotient_card_le_centralizer_index (imageRepresentation ρ) (actionHom ρ) simg A
      have hm : (centralizer (A : Set G)).relIndex U ≤ (centralizer (A : Set G)).relIndex V :=
        relIndex_le_of_le_right hUV index_ne_zero_of_finite
      rw [inf_relIndex_left] at hbound
      exact (hb.trans hm).trans hbound

/-- The original noncentral interface, retained as a specialization of the general construction. -/
theorem source_replacement_simple_quadratic_section (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    ∃ U C : Subgroup G, U ≤ V ∧ ∃ (W : Type u) (_ : AddCommGroup W)
      (_ : Module (ZMod 2) W) (_ : Finite W) (ρ : Representation (ZMod 2) X W),
      Nonempty (BinaryConjugationSection X U C ρ) ∧ IsIrreducible ρ ∧
      ρ.ker.map X.subtype = commutatorPreimage X U C ∧ pCore 2 X ≤ ρ.ker ∧
      Function.Injective (imageRepresentation ρ) ∧ pCore 2 (actionImage ρ) = ⊥ ∧
      fixedSpace (imageRepresentation ρ) (pResidual 2 (actionImage ρ)) = ⊥ ∧
      (∃ T : Sylow 2 X, (T : Subgroup X).map X.subtype = B.pCoreIn 2 ⊓ X ∧
        ∃ R : Sylow 2 (actionImage ρ), (R : Subgroup (actionImage ρ)) =
          (T : Subgroup X).map (actionHom ρ) ∧ GeneratedByFixedSpace (imageRepresentation ρ) R) ∧
      ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
        ¬ A ≤ (P (other i)).pCoreIn 2 ∧ ¬ A ≤ X.pCoreIn 2 ∧
        IsQuadratic (imageRepresentation ρ) ((A.subgroupOf X).map (actionHom ρ)) ∧
        Nat.card (W ⧸ fixedSpace (imageRepresentation ρ)
          ((A.subgroupOf X).map (actionHom ρ))) ≤ ((P (other i)).pCoreIn 2).relIndex A := by
  have _ := hnc
  exact source_replacement_simple_quadratic_section_of_inter_normal h hB hS i hn

end CFSG.Quasithin.ChapterF.Source.DGS85
