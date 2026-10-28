module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Blocks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Quotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InflatedCharacters.Marking
public import Theory.Character.AlternatingSix.Blocks
public import Theory.Character.AlternatingSix.Rational
public import Theory.Character.AlternatingSix.Golden
public import Theory.Character.SurjectiveInflation

/-!
# Inflation of the two ordinary A6 character blocks

The actual complement supplies a surjection from N(E) to A6. Its marked
representatives have the orders and order-three separation proved in
`InflatedCharacters.Marking`. Pulling back actual irreducible representations
preserves irreducibility and gives all 84 entries in the seven inflated rows.
The trivial representation supplies the principal row.

The rational permutation-character construction and the complementary
irreducible-character construction discharge both A6 inputs in
`normalizerInflatedBlock_nonempty`. It requires only local analysis and the
explicit marked class data. The four rational rows have degrees `9,10,5,5`;
the two complementary rows have degree eight and interchanged fifth-order
values satisfying `t² = t + 1`. No character-construction premise remains.
Constructing the marked class data and the five noninflated rows belongs to
the full normalizer-table assembly.

Source: Janko, *A characterization of the Mathieu simple groups, I*, §6,
pp.10–11. The finite numerical identities are separate from the representation
transport, keeping table reduction out of the group-theoretic proofs.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
open Theory.Character.AlternatingSix

private theorem principal_values (t : ℂ) (r : Fin 12) :
    normalizerFullValues t 0 r = 1 := by
  fin_cases r <;> first
  | rfl
  | exact (Int.cast_one : ((1 : ℤ) : ℂ) = 1)

private theorem rational_values (t : ℂ) (j : Fin 4) (r : Fin 12) :
    normalizerFullValues t (![1, 2, 5, 6] j) r =
      (rationalValues j (![0, 2, 4, 1, 1, 0, 1, 2, 3, 4, 5, 5] r) : ℂ) := by
  fin_cases j <;> fin_cases r <;> first
  | rfl
  | exact (Int.cast_zero : ((0 : ℤ) : ℂ) = 0).symm
  | exact (by norm_num : (-1 : ℂ) = ((-1 : ℤ) : ℂ))

private theorem golden_values (t : ℂ) (j : Fin 2) (r : Fin 12) :
    normalizerFullValues t (![3, 4] j) r =
      ![8, -1, 0, 0, 0, 8, 0, -1, -1, 0, ![t, 1 - t] j, ![1 - t, t] j] r := by
  fin_cases j <;> fin_cases r <;> first
  | rfl
  | exact (Int.cast_zero : ((0 : ℤ) : ℂ) = 0)
  | exact (by norm_num : ((8 : ℤ) : ℂ) = 8)
  | exact (by norm_num : ((-1 : ℤ) : ℂ) = -1)

universe u
variable {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (K : Subgroup (normalizer (CaseII.E D k : Set G)))
    (hK : ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).IsComplement' K)
    (eK : K ≃* alternatingGroup (Fin 6))

local notation "π" => normalizerQuotient D k K hK eK

private theorem inflated_rational_values (L : LocalAnalysisData D k)
    (Q : NormalizerClassData D k)
    (R : RationalBlock (π (normalizerCentralizer D k CaseII.c)))
    (t : ℂ) (j : Fin 4) (r : Fin 12) :
    R.character j (π (Q.representative r)) = normalizerFullValues t (![1, 2, 5, 6] j) r := by
  have ha := normalizerQuotient_a_order D k K hK eK
  have hd := normalizerQuotient_d_order D k K hK eK
  have hbd := normalizerQuotient_bd_order D k K hK eK
  have hc' := normalizerQuotient_otherThree_order D k K hK eK L Q
  have hnc := normalizerQuotient_otherThree_not_isConj D k K hK eK L Q
  have hm := normalizerQuotient_five_order D k K hK eK L Q
  have hm2 : orderOf ((π Q.five) ^ 2) = 5 := by rw [orderOf_pow, hm]; decide
  rw [rational_values, normalizerQuotient_representative]
  fin_cases r
  · exact R.one j
  · exact R.three j
  · exact R.four j _ hbd
  · exact R.two j _ ha
  · exact R.two j _ hd
  · exact R.one j
  · exact R.two j _ ha
  · exact R.three j
  · exact R.otherThree j _ hc' hnc
  · exact R.four j _ hbd
  · exact R.five j _ hm
  · exact R.five j _ hm2

private theorem inflated_golden_values (L : LocalAnalysisData D k)
    (Q : NormalizerClassData D k) (B : GoldenBlock (π Q.five))
    (j : Fin 2) (r : Fin 12) :
    B.character j (π (Q.representative r)) =
      normalizerFullValues B.parameter (![3, 4] j) r := by
  have ha := normalizerQuotient_a_order D k K hK eK
  have hc := normalizerQuotient_c_order D k K hK eK
  have hd := normalizerQuotient_d_order D k K hK eK
  have hbd := normalizerQuotient_bd_order D k K hK eK
  have hc' := normalizerQuotient_otherThree_order D k K hK eK L Q
  rw [golden_values, normalizerQuotient_representative]
  fin_cases r
  · exact B.one j
  · exact B.three j _ hc
  · exact B.four j _ hbd
  · exact B.two j _ ha
  · exact B.two j _ hd
  · exact B.one j
  · exact B.two j _ ha
  · exact B.three j _ hc
  · exact B.three j _ hc'
  · exact B.four j _ hbd
  · exact B.five j
  · exact B.five_sq j

/-- Inflate the actual A6 characters along the actual quotient and verify
all twelve columns with the original centralizer marking. -/
public def normalizerInflatedBlockOfBlocks (L : LocalAnalysisData D k)
    (Q : NormalizerClassData D k)
    (R : RationalBlock (π (normalizerCentralizer D k CaseII.c)))
    (B : GoldenBlock (π Q.five)) : NormalizerInflatedBlock Q where
  parameter := B.parameter
  parameter_equation := B.parameter_equation
  character j x := combinedCharacter R B j (π x)
  irreducible j := (combinedCharacter_irreducible R B j).comp_surjective
    (π) (normalizerQuotient_surjective D k K hK eK)
  principal := rfl
  values := by
    intro j r
    fin_cases j
    · exact (principal_values B.parameter r).symm
    · exact inflated_rational_values D k K hK eK L Q R B.parameter 0 r
    · exact inflated_rational_values D k K hK eK L Q R B.parameter 1 r
    · exact inflated_golden_values D k K hK eK L Q B 0 r
    · exact inflated_golden_values D k K hK eK L Q B 1 r
    · exact inflated_rational_values D k K hK eK L Q R B.parameter 2 r
    · exact inflated_rational_values D k K hK eK L Q R B.parameter 3 r

/-- Local analysis and the two A6 construction theorems give the requested
normalizer block. Both character-construction premises remain explicit. -/
public theorem normalizerInflatedBlock_of_alternatingSix_blocks
    (L : LocalAnalysisData D k) (Q : NormalizerClassData D k)
    (rational : ∀ c : alternatingGroup (Fin 6), orderOf c = 3 → Nonempty (RationalBlock c))
    (golden : ∀ c μ : alternatingGroup (Fin 6), orderOf c = 3 → orderOf μ = 5 →
      RationalBlock c → Nonempty (GoldenBlock μ)) :
    Nonempty (NormalizerInflatedBlock Q) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  obtain ⟨R⟩ := rational _ (normalizerQuotient_c_order D k K hK eK)
  obtain ⟨B⟩ := golden _ _ (normalizerQuotient_c_order D k K hK eK)
    (normalizerQuotient_five_order D k K hK eK L Q) R
  exact ⟨normalizerInflatedBlockOfBlocks D k K hK eK L Q R B⟩

/-- The seven actual irreducible characters of the normalizer inflated from A6,
with degrees `1,9,10,8,8,5,5`, principal row zero, and every prescribed value on
the original marked representatives. Both A6 character producers are proved;
only the local analysis and the independently constructed class data are inputs. -/
public theorem normalizerInflatedBlock_nonempty
    (L : LocalAnalysisData D k) (Q : NormalizerClassData D k) :
    Nonempty (NormalizerInflatedBlock Q) :=
  normalizerInflatedBlock_of_alternatingSix_blocks D k L Q
    rationalBlock_nonempty goldenBlock_of_rational

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
