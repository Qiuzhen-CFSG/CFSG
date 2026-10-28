module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingJankoFour
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Max2Exclusion.MathieuMap
import all CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Max2Exclusion.MathieuMap

/-!
# The full Mathieu image of the J₄ involution centralizer

The two certified generator words show that the existing twelve-dimensional
map has the entire action group as its range. Its derived map is therefore
onto the literal M₂₂ quotient. Restricting a normalized local component to
the original derived subgroup preserves a full Sylow intersection; the proved
solvable kernel preserves its exceptional two-core quotient. The M₂₂
normalized-section exclusion then rules out the original max2 configuration.

The `import all` is an intentional internal proof extension of MathieuMap:
we prove surjectivity of its existing map without changing or re-exporting
its private implementation. Only the map's public surjectivity and its local
consumer are exported here.

Source: Aschbacher–Smith A.3.12 and 5.1.12, printed pp.47–48 and635;
GLS3 Table5.3i describes the actual centralizer quotient.
-/

public noncomputable section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.sourceSubgroup
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.Max2Exclusion
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData TwoCoreCentralizerData.LowerBound
open TwoCoreComparison.CoordinateGenerators TwoCoreLinearModel

private theorem ambientMap_range_eq : ambientMap.range = actionGroup := by
  apply le_antisymm ambientMap_range_le
  change closure {unitC,unitD} ≤ ambientMap.range
  apply (closure_le _).mpr
  have hx : MulAut.conj basisUnit rawUnitX ∈ ambientMap.range :=
    ⟨sourceX, by
      change alignQuotient (quotientMap sourceX) = _
      rw [quotientMap_sourceX,alignQuotient_x]⟩
  have hy : MulAut.conj basisUnit rawUnitY ∈ ambientMap.range :=
    ⟨sourceY, by
      change alignQuotient (quotientMap sourceY) = _
      rw [quotientMap_sourceY,alignQuotient_y]⟩
  rintro x (rfl | rfl)
  · rw [← align_first]
    simp only [firstWord, map_pow, map_mul]
    exact ambientMap.range.pow_mem (ambientMap.range.mul_mem hx hy) 7
  · rw [← align_second]
    simp only [secondWord, map_mul, map_pow, map_inv]
    have hxy := ambientMap.range.mul_mem hx hy
    have hxyx := ambientMap.range.mul_mem hxy hx
    exact ambientMap.range.mul_mem
      (ambientMap.range.mul_mem (ambientMap.range.inv_mem hxyx)
        (ambientMap.range.pow_mem
          (ambientMap.range.mul_mem
            (ambientMap.range.mul_mem
              (ambientMap.range.mul_mem
                (ambientMap.range.mul_mem (ambientMap.range.pow_mem hxy 3) hy)
                (ambientMap.range.pow_mem hxy 2)) hy)
            (ambientMap.range.pow_mem hxy 2)) 3)) hxyx

private theorem commutatorLinearMap_surjective : Function.Surjective commutatorLinearMap := by
  intro x
  have hx : (x : Matrix12ˣ) ∈ (commutator sourceSubgroup).map ambientMap := by
    rw [map_commutator_eq, ambientMap_range_eq]
    exact x.property
  obtain ⟨g,hg,he⟩ := hx
  exact ⟨⟨g,hg⟩, Subtype.ext he⟩

/-- The same concrete derived-subgroup map is onto the full Mathieu group. -/
theorem commutatorMathieuMap_surjective : Function.Surjective commutatorMathieuMap :=
  derivedQuotientEquivM22.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp commutatorLinearMap_surjective)

/-- A normalized exceptional section cannot occur in the literal max2 carrier. -/
theorem not_exceptional_section_max2
    (S : Sylow 2 sourceSubgroup) (B : Subgroup sourceSubgroup)
    (hl : B ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup sourceSubgroup) ≤ normalizer (B : Set sourceSubgroup))
    (hm : ChapterA.Section03.SourceEmbeddings.Exceptional.IsModel (B ⧸ pCore 2 B)) : False := by
  let := ChapterA.Section03.SourceEmbeddings.Exceptional.local_perfect hl
  have hBD : B ≤ commutator sourceSubgroup := by
    rw [← B.commutator_eq_self]
    exact commutator_mono le_top le_top
  obtain ⟨R,hR,hlR⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    S hl hBD (inferInstance : (commutator sourceSubgroup).Normal).isSubnormal
  have hnR : (R : Subgroup (commutator sourceSubgroup)) ≤
      normalizer (B.subgroupOf (commutator sourceSubgroup) : Set (commutator sourceSubgroup)) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro b
    have hs' : s ∈ (S : Subgroup sourceSubgroup).subgroupOf (commutator sourceSubgroup) := by
      rwa [← hR]
    exact mem_normalizer_iff.mp (hn hs') (b : sourceSubgroup)
  have hmR := hm.of_equiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBD)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hBD)))
  let : Group.IsSolvable commutatorMathieuMap.ker := commutatorMathieuMap_ker_isSolvable
  obtain ⟨_,hN,hQ⟩ := ChapterA.Section03.SourceEmbeddings.Exceptional.local_section_map
    hlR hnR hmR commutatorMathieuMap
  exact ChapterA.Section03.SourceEmbeddings.Exceptional.not_mathieu_twentyTwo
    (R.mapSurjective commutatorMathieuMap_surjective)
    ((B.subgroupOf (commutator sourceSubgroup)).map commutatorMathieuMap)
    hN hQ (MulEquiv.refl _)
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.Max2Exclusion
