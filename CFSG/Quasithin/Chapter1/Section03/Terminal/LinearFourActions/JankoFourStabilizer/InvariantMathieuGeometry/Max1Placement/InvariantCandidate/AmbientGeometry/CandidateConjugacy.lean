module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.CandidateConjugacy.Qualifications
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max1
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer

/-!
# Ambient conjugacy of max1 candidates

The candidate's actual isomorphism to literal max1 and its proved odd index
supply a new ambient Sylow contained in the candidate. The characteristic
Sylow-core comparison, with the proved literal core-normalizer containment,
then conjugates the candidate to literal max1. Inverting the conjugator gives
the requested `g H g⁻¹ = certifiedMathieuSubgroup` orientation.

This proof uses neither maximality nor ambient simplicity, perfectness or
full model order. Neither local witness is identified with the new ambient
Sylow, and no relative normality is promoted to ambient normality. The earlier
conditional maximal-cover and model-order assemblies are retained below.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48, and the proof of
1.3.9, p.514; GLS3 Table 5.3i. The separate embedding contract refers to
Kleidman–Wilson, *The maximal subgroups of J₄* (1988), pp.484–510. Its truth
does not follow from defining the three listed matrix subgroups.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry

open CandidateConjugacyReduction
open Janko4.LocalStructure.SymmetricLinear
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

/-- Every source-local max1 candidate is conjugate in the actual matrix model
to the literal certified subgroup. Odd index supplies a new contained ambient
Sylow; the literal two-core normalizer bound completes the comparison. -/
theorem candidateConjugacy : CandidateConjugacy := by
  intro A S H hA hlocal hH
  obtain ⟨e⟩ := hH.2.1
  have hindex : ¬ 2 ∣ certifiedMathieuSubgroup.index := by
    simpa only [certifiedMathieuSubgroup] using
      Janko4.OuterReduction.max1_odd_index_unconditional
  obtain ⟨P, hPH⟩ := exists_sylow_le_max1_copy e hindex
  let eLiteral : H ≃*
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four :=
    e.trans (MulEquiv.subgroupCongr (by simp only [certifiedMathieuSubgroup]))
  obtain ⟨g, hg⟩ := max1CopyConjugacy_of_coreNormalizer
    Janko4.LocalStructure.normalizer_embedded_localKernel_le_max1 P H hPH eLiteral
  have hHconj : H = certifiedMathieuSubgroup.map (MulAut.conj g).toMonoidHom := by
    simpa only [certifiedMathieuSubgroup] using hg
  refine ⟨g⁻¹, ?_⟩
  rw [hHconj, map_map]
  have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Janko4.Model := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hi, map_id]

/-- Conditional use of the separate maximal-embedding theorem. Every hypothesis
besides its simplicity requirement is supplied explicitly or proved above. -/
theorem candidateConjugacy_of_maximal_cover [IsSimpleGroup Janko4.Model]
    (hindex : ¬ 2 ∣ certifiedMathieuSubgroup.index)
    (hcover : MaximalSylowCover)
    (e4 : (max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel)
    (hconj : ListedMaximalEmbeddingConjugacy) : CandidateConjugacy := by
  let : Group.IsPerfect Janko4.Model := model_isPerfect
  intro A S H hA hlocal hH
  obtain ⟨e⟩ := hH.2.1
  obtain ⟨P, hPH⟩ := exists_sylow_le_max1_copy e hindex
  have hmax := max1_copy_isCoatom_of_cover e hindex hcover e4
  have hlisted : certifiedMathieuSubgroup ∈ listedSubgroups := by
    simp only [listedSubgroups, certifiedMathieuSubgroup, Set.mem_insert_iff, true_or]
  obtain ⟨g, hg⟩ := hconj P H certifiedMathieuSubgroup hmax hPH hlisted ⟨e⟩
  refine ⟨g⁻¹, ?_⟩
  rw [hg, map_map]
  have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Janko4.Model := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hi, map_id]

/-- A proved exact model order would discharge odd index. This alternative
allows the existing model-certification task to supply both order and simplicity. -/
theorem candidateConjugacy_of_model_order [IsSimpleGroup Janko4.Model]
    (hcard : Nat.card Janko4.Model = 86775571046077562880)
    (hcover : MaximalSylowCover)
    (e4 : (max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel)
    (hconj : ListedMaximalEmbeddingConjugacy) : CandidateConjugacy := by
  apply candidateConjugacy_of_maximal_cover (hcover := hcover) (e4 := e4) (hconj := hconj)
  have hi := certifiedMathieuSubgroup.card_mul_index
  rw [max1_copy_card (MulEquiv.refl certifiedMathieuSubgroup), hcard] at hi
  have heq : certifiedMathieuSubgroup.index = 173067389 := by omega
  rw [heq]
  decide

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry
