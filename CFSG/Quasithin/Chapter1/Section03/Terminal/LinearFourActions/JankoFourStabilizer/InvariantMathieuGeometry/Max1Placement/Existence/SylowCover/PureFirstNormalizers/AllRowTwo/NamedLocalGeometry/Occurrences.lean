module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.OccurrenceChecks
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.SeedIntersection
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.FiniteCertificate.Checks

/-!
# Exhaustive ambient F occurrences through the marked point

The certified word tree puts every label in an actual conjugate of F. The
separation witnesses prove that all 330 ambient subgroups are distinct, using
commutativity of F and the faithful native kernel coordinates. The independent
ambient occurrence count then proves this table exhaustive. This is the bridge
from finite incidence data to the canonical whole-normalizer construction.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489; native ATLAS action
and word attribution are retained in the imported certificates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
open FiniteConfigurations
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
open FiniteTree
attribute [local irreducible] modelGroup matrixA matrixB

theorem nativeWord_mul_fast (m n : Fin 8192) :
    nativeWord m * nativeWord n = nativeWord
      ⟨fastMultiply m.val n.val % 8192, Nat.mod_lt _ (by decide)⟩ := by
  have hb : maskMultiply m.val n.val < 8192 := by
    apply Nat.xor_lt_two_pow (n := 13) (Nat.xor_lt_two_pow m.isLt n.isLt)
    cases correction m.val n.val <;> decide
  have hf : fastMultiply m.val n.val = maskMultiply m.val n.val := by
    simp only [fastMultiply,maskMultiply,correction_fast]
  change nativeWord m * nativeWord n =
    ((maskProduct kernelFactor (fastMultiply m.val n.val % 8192) : sourceSubgroup) : Model)
  rw [hf,Nat.mod_eq_of_lt hb]
  exact congrArg (fun x : sourceSubgroup => (x : Model)) (source_mask_multiply m.val n.val).symm

theorem nativeWord_noncommute (m n : Fin 8192)
    (h : fastMultiply m.val n.val % 8192 ≠ fastMultiply n.val m.val % 8192) :
    nativeWord m * nativeWord n ≠ nativeWord n * nativeWord m := by
  intro he
  rw [nativeWord_mul_fast,nativeWord_mul_fast] at he
  exact h (congrArg Fin.val (kernelProduct_injective (Subtype.ext he)))

theorem wordF_append (w v : List Bool) :
    (wordF w).map (MulAut.conj ((actorWord v : Model)⁻¹)).toMonoidHom = wordF (w ++ v) := by
  simp only [wordF,map_map]
  congr 1
  ext x
  simp [actorWord,List.map_append,List.prod_append,mul_assoc]

theorem wordF_elementary (w : List Bool) : IsElementaryAbelian 2 (wordF w) := by
  rw [wordF_eq]
  let := LinearFive.F_elementary
  exact IsElementaryAbelian.map _

theorem nativeWord_one_markedT : nativeWord 1 = markedT := by
  have hh : kernelProduct 1 = kernelFactor 0 := by
    change kernelFactor 0 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1)))))))))))) = _
    simp only [mul_one]
  change (kernelProduct 1 : Model) = t
  rw [hh]
  exact coe_sourceSeed_sq


open OccurrenceTable in
/-- Every listed generator lies in its actual ambient F occurrence. -/
theorem occurrence_label_mem (i : Fin 330) (j : Fin 7) :
    nativeWord (label i j) ∈ wordF (word i) := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    by_cases hi : i = 0
    · subst i
      rw [root_labels,root_word]
      have hm := seedCoordinate_mem ⟨2^j.val % 128,Nat.mod_lt _ (by decide)⟩
      change nativeWord (seedCoordinate ⟨2^j.val % 128,Nat.mod_lt _ (by decide)⟩) ∈ seedF at hm
      simpa [wordF,actorWord] using hm
    · have he := edges i hi
      have hm := mem_map_of_mem
        (MulAut.conj ((actorWord [step i] : Model)⁻¹)).toMonoidHom (ih (parent i) he.1)
      have hc := nativeWord_conjugates [step i] (label (parent i) j) (label i j)
        (by simpa only [actMask,action_fast] using he.2.2 j)
      rw [wordF_append,← he.2.1] at hm
      exact hc ▸ hm

/-- The entire word-defined F occurrence contains the same marked point. -/
theorem markedT_mem_occurrence (i : Fin 330) :
    markedT ∈ wordF (OccurrenceTable.word i) := by
  have hm := occurrence_label_mem i 0
  rwa [OccurrenceTable.central_labels,nativeWord_one_markedT] at hm

private theorem occurrences_ne_of_lt (i j : Fin 330) (hij : i < j) :
    wordF (OccurrenceTable.word i) ≠ wordF (OccurrenceTable.word j) := by
  intro he
  let W := wordF (OccurrenceTable.word i)
  let := wordF_elementary (OccurrenceTable.word i)
  let p := (OccurrenceTable.separator i j).1
  let q := (OccurrenceTable.separator i j).2
  have hp : nativeWord (OccurrenceTable.label i p) ∈ W := occurrence_label_mem i p
  have hq : nativeWord (OccurrenceTable.label j q) ∈ W := by
    change nativeWord (OccurrenceTable.label j q) ∈ wordF (OccurrenceTable.word i)
    rw [he]
    exact occurrence_label_mem j q
  have hc := congrArg (fun x : W => (x : Model))
    (mul_comm (⟨_,hp⟩ : W) (⟨_,hq⟩ : W))
  exact nativeWord_noncommute _ _ (OccurrenceTable.separation i j hij) hc

/-- Distinct entries are distinct ambient subgroups, witnessed by noncommutation. -/
theorem occurrence_injective : Function.Injective (fun i => wordF (OccurrenceTable.word i)) := by
  intro i j he
  by_contra hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact occurrences_ne_of_lt i j h he
  · exact occurrences_ne_of_lt j i h he.symm

/-- The occurrence table maps into the literal ambient family, with no normalizer premise. -/
def occurrenceEmbedding (i : Fin 330) : fOccurrences (zpowers markedT) :=
  ⟨wordF (OccurrenceTable.word i),
    (actorWord (OccurrenceTable.word i) : Model)⁻¹ * BridgeCertificates.bridge⁻¹,
    wordF_eq _,zpowers_le.mpr (markedT_mem_occurrence i)⟩

/-- The checked table exhausts the ambient family by its independently proved order. -/
theorem occurrenceEmbedding_bijective : Function.Bijective occurrenceEmbedding := by
  have hinj : Function.Injective occurrenceEmbedding := by
    intro i j h
    exact occurrence_injective (congrArg Subtype.val h)
  exact hinj.bijective_of_nat_card_le (by rw [marked_point_F_occurrences_card,Nat.card_fin])

/-- Exact occurrence enumeration at the actual point used by every shared row. -/
theorem mem_marked_point_fOccurrences_iff (Y : Subgroup Model) :
    Y ∈ fOccurrences (zpowers markedT) ↔ ∃ i : Fin 330, Y = wordF (OccurrenceTable.word i) := by
  constructor
  · intro hY
    obtain ⟨i,hi⟩ := occurrenceEmbedding_bijective.2 ⟨Y,hY⟩
    exact ⟨i,(congrArg Subtype.val hi).symm⟩
  · rintro ⟨i,rfl⟩
    exact (occurrenceEmbedding i).property

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
