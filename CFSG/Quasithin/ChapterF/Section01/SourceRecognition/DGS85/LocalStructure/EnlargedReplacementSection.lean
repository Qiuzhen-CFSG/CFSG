module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementSection
public import Theory.Representation.BinaryConjugationSection.NormalElementary
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# A replacement section for the full enlarged endpoint

Under contrary adjacent-core normality, the literal replacement span
V = <Z_delta^X> is also the span under the full neighboring endpoint.
It is elementary and normal in M = L_lambda. Its conjugation action and
the inclusion O²(X) ≤ O²(M) give a residual-moving simple section for M.
The section has vanishing residual fixed space and generation by every
actual Sylow fixed space. The escaping Thompson actor stays quadratic
with its original index bound.

The reduced F.1.1 application constructs the same section on the actual
reduced enlargement. No model marking or faithfulness on the original
core quotient is inferred. EnlargedReplacementQuotient descends this
section through that quotient without a perfectness assumption.
Source: DGS, Groups and Graphs (1985), 6.4, pp.120--121, using corrected
5.12, pp.113--115.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory.AmalgamGraph Representation
open Representation.BinaryOffender Representation.BinaryConjugationSection
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The full enlarged endpoint acts on a residual-moving section of the original replacement span. -/
theorem source_enlarged_replacement_simple_section (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    let M := localEnlargement d
    ∃ U C : Subgroup G, U ≤ V ∧ ∃ (W : Type u) (_ : AddCommGroup W)
      (_ : Module (ZMod 2) W) (_ : Finite W) (ρ : Representation (ZMod 2) M W),
      Nonempty (BinaryConjugationSection M U C ρ) ∧ IsIrreducible ρ ∧
      ρ.ker.map M.subtype = commutatorPreimage M U C ∧ pCore 2 M ≤ ρ.ker ∧
      Function.Injective (imageRepresentation ρ) ∧ pCore 2 (actionImage ρ) = ⊥ ∧
      fixedSpace (imageRepresentation ρ) (pResidual 2 (actionImage ρ)) = ⊥ ∧
      (∀ T : Sylow 2 M, ∃ R : Sylow 2 (actionImage ρ),
        (R : Subgroup (actionImage ρ)) = (T : Subgroup M).map (actionHom ρ) ∧
        GeneratedByFixedSpace (imageRepresentation ρ) R) ∧
      ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
        ¬ A ≤ (P (other i)).pCoreIn 2 ∧
        IsQuadratic (imageRepresentation ρ) ((A.subgroupOf M).map (actionHom ρ)) ∧
        Nat.card (W ⧸ fixedSpace (imageRepresentation ρ)
          ((A.subgroupOf M).map (actionHom ρ))) ≤ ((P (other i)).pCoreIn 2).relIndex A := by
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let V := conjugateSpanBy (sylowCenterSpan (P i)) X
  let M := localEnlargement d
  let := d.finite_P
  let : Finite M := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  have hXM : X ≤ M := core_closure_le_localEnlargement h hB i d
  have hVX : V ≤ X := ((source_replacement_span_le_inter_omega_of_inter_normal h i hn).trans
    ((map_subtype_le _).trans inf_le_left)).trans (le_conjugateSpanBy _ _)
  have hVM : V ≤ M := hVX.trans hXM
  let : Finite V := Finite.of_injective (inclusion hVM) (inclusion_injective _)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le
    (source_replacement_span_le_inter_omega_of_inter_normal h i hn)
  have hnormal : M ≤ normalizer (V : Set G) := by
    change M ≤ normalizer (conjugateSpanBy (sylowCenterSpan (P i)) X : Set G)
    rw [show conjugateSpanBy (sylowCenterSpan (P i)) X =
      conjugateSpanBy (sylowCenterSpan (P i)) (P (other i)) from
      source_replacement_span_eq_full_span h hB i hn]
    exact (localEnlargement_le d).trans (le_normalizer_conjugateSpanBy _ _)
  obtain ⟨hE,hh⟩ := exists_faithful_quotient_action M V hVM hnormal
  let := hE
  obtain ⟨K,hK,hh⟩ := hh
  let := hK
  obtain ⟨σ,_,_,⟨act⟩⟩ := hh
  let ρ₀ := σ.comp (QuotientGroup.mk' K)
  let : FiniteDimensional (ZMod 2) (Additive (V.subgroupOf M)) := Module.Finite.of_finite
  have hmove : ¬ pResidual 2 M ≤ ρ₀.ker := by
    intro hk
    apply source_replacement_residual_not_central h hB i hn
    intro v hv r hr
    have hrM : r ∈ (pResidual 2 M).map M.subtype := embedded_pResidual_mono 2 hXM hr
    obtain ⟨a,ha,rfl⟩ := hrM
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (mem_bot.mp ((act.action_mem_ker_iff a).mp (hk ha) v hv))
  obtain ⟨U,C,hUV,W,hW,hWM,hWf,ρ,⟨s⟩,hi,hker,hcore,hfaith,hzero,hres,hgen⟩ :=
    act.exists_faithful_residual_simple_section hmove
  let := hW
  let := hWM
  let := hWf
  let : Finite U := Finite.of_injective (inclusion hUV) (inclusion_injective _)
  have he : (imageRepresentation ρ).comp (actionHom ρ) = ρ :=
    MonoidHom.ext (imageRepresentation_actionHom ρ)
  have simg : BinaryConjugationSection M U C ((imageRepresentation ρ).comp (actionHom ρ)) :=
    he.symm ▸ s
  refine ⟨U,C,hUV,W,hW,hWM,hWf,ρ,⟨s⟩,hi,hker,hcore,hfaith,hzero,hres,hgen,?_⟩
  obtain ⟨A,hA,hout,_,hquad,hbound⟩ := source_replacement_quadratic_offender_of_inter_normal h i hn
  refine ⟨A,hA,hout,?_,?_⟩
  · apply isQuadratic_of_triple_commutator_le M U C A (imageRepresentation ρ) (actionHom ρ) simg
    have hh : ⁅A,⁅A,U⁆⁆ ≤ ⁅⁅V,A⁆,A⁆ := by
      rw [commutator_comm A ⁅A,U⁆,commutator_comm A U]
      exact commutator_mono (commutator_mono hUV le_rfl) le_rfl
    exact hh.trans (hquad.le.trans bot_le)
  · have hb := fixed_quotient_card_le_centralizer_index (imageRepresentation ρ) (actionHom ρ) simg A
    have hm : (centralizer (A : Set G)).relIndex U ≤ (centralizer (A : Set G)).relIndex V :=
      relIndex_le_of_le_right hUV index_ne_zero_of_finite
    rw [inf_relIndex_left] at hbound
    exact (hb.trans hm).trans hbound

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original reduced F.1.1 triple supplies all the section construction premises. -/
theorem reduced_enlarged_replacement_simple_section (h : HypothesisF11 L S) (i : Fin 2)
    (hn : (P₀ L S (other i)).subgroupOf (G₀ L S) ≤ normalizer
      ((((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S))) :
    let P := fun k => (P₀ L S k).subgroupOf (G₀ L S)
    let d := Classical.choice ((reduced_triple h).local_data (other i))
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    let M := localEnlargement d
    ∃ U C : Subgroup (G₀ L S), U ≤ V ∧ ∃ (W : Type u) (_ : AddCommGroup W)
      (_ : Module (ZMod 2) W) (_ : Finite W) (ρ : Representation (ZMod 2) M W),
      Nonempty (BinaryConjugationSection M U C ρ) ∧ IsIrreducible ρ ∧
      ρ.ker.map M.subtype = commutatorPreimage M U C ∧ pCore 2 M ≤ ρ.ker ∧
      Function.Injective (imageRepresentation ρ) ∧ pCore 2 (actionImage ρ) = ⊥ ∧
      fixedSpace (imageRepresentation ρ) (pResidual 2 (actionImage ρ)) = ⊥ ∧
      (∀ T : Sylow 2 M, ∃ R : Sylow 2 (actionImage ρ),
        (R : Subgroup (actionImage ρ)) = (T : Subgroup M).map (actionHom ρ) ∧
        GeneratedByFixedSpace (imageRepresentation ρ) R) ∧
      ∃ A : Subgroup (G₀ L S), A ∈ thompsonAbelianSubgroups ((P i).pCoreIn 2) ∧
        ¬ A ≤ (P (other i)).pCoreIn 2 ∧
        IsQuadratic (imageRepresentation ρ) ((A.subgroupOf M).map (actionHom ρ)) ∧
        Nat.card (W ⧸ fixedSpace (imageRepresentation ρ)
          ((A.subgroupOf M).map (actionHom ρ))) ≤ ((P (other i)).pCoreIn 2).relIndex A :=
  source_enlarged_replacement_simple_section (reduced_triple h) (reduced_borel_core_sylow h)
    i (Classical.choice ((reduced_triple h).local_data (other i))) hn

end Reduction

end CFSG.Quasithin.ChapterF.Source.DGS85
