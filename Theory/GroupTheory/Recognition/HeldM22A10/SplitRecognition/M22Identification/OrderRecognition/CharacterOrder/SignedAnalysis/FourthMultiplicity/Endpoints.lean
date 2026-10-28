module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.FourthArithmetic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.SignedCoordinates

/-!
# Suzuki contradictions for the two remaining fourth-induction patterns

Each premise is an equality of actual class functions in a family of distinct
signed irreducibles. Evaluating at the identity and the distinguished involution
and pairing with the actual involution-pair count derives the displayed Suzuki
equations. The first pattern forces an extra factor of three in the group order;
the last yields the integer quadratic excluded modulo nine.

Signed degrees, including their signs, are kept in every denominator. These
conditional lemmas are used by FourthMultiplicity to discharge both remaining
patterns constructed from the complete integral expansion.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 11, p.13.
-/

noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
variable {G : Type*} [Group G] [Finite G]
namespace SignedAnalysis.FourthMultiplicity

public theorem first_pattern_impossible
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 3)
    (he4 : I.induced 3 = F.term 0 + (2 : ℂ) • F.term 1)
    (he2 : I.induced 1 = F.term 1 - F.term 0 + F.term 2) : False := by
  have hd4 : F.term 0 1 + 2 * F.term 1 1 = 0 := by
    have h := I.degree_zero 3
    change I.induced 3 1 = 0 at h
    simpa only [he4, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have hd2 : F.term 1 1 - F.term 0 1 + F.term 2 1 = 0 := by
    have h := I.degree_zero 1
    change I.induced 1 1 = 0 at h
    simpa only [he2, Pi.add_apply, Pi.sub_apply] using h
  have hv4 : F.term 0 D.z + 2 * F.term 1 D.z = 32 := by
    have h : I.induced 3 D.z = 32 := by
      simpa [SpecialInductionData.induced, specialRepresentative, exceptionalValues,
        CaseII.into_z_zero] using I.values 3 0
    simpa only [he4, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have hv2 : F.term 1 D.z - F.term 0 D.z + F.term 2 D.z = 0 := by
    have h : I.induced 1 D.z = 0 := by
      simpa [SpecialInductionData.induced, specialRepresentative, exceptionalValues,
        CaseII.into_z_zero] using I.values 1 0
    simpa only [he2, Pi.add_apply, Pi.sub_apply] using h
  have hd0 : F.term 0 1 = -2 * F.term 1 1 := by linear_combination hd4
  have hdY : F.term 2 1 = -3 * F.term 1 1 := by linear_combination hd4 + hd2
  have hv0 : F.term 0 D.z = 32 - 2 * F.term 1 D.z := by linear_combination hv4
  have hvY : F.term 2 D.z = 32 - 3 * F.term 1 D.z := by linear_combination hv4 + hv2
  have hs : (Nat.card G : ℂ) / 147456 *
      (F.term 1 D.z ^ 2 / F.term 1 1 - F.term 0 D.z ^ 2 / F.term 0 1 +
        F.term 2 D.z ^ 2 / F.term 2 1) = -1 := by
    have h := hI 1
    rw [he2] at h
    simp only [scalarProduct_sub_left, scalarProduct_add_left, F.term_pairing D k L] at h
    dsimp [pairingConstants] at h
    norm_num at h
    simp only [← Nat.card_eq_fintype_card] at h
    linear_combination h
  have hy : F.term 1 1 ≠ 0 := by
    rw [F.term_one]
    exact_mod_cast F.signedDegree_ne_zero 1
  have hg := fourth_first_suzuki_elimination (Nat.card G) (F.term 1 1) (F.term 1 D.z) hy
    (by simpa only [hd0, hdY, hv0, hvY] using hs)
  have hg' : (Nat.card G : ℤ) = -864 * F.signedDegree 1 := by
    rw [F.term_one] at hg
    exact_mod_cast hg
  exact fourth_first_order_impossible D k L (F.signedDegree 1) hg'

public theorem last_pattern_impossible
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 3)
    (he4 : I.induced 3 = F.term 0 + (2 : ℂ) • F.term 1)
    (he3 : I.induced 2 = 1 + F.term 1 - F.term 0 + F.term 2)
    (hv0 : F.term 0 D.z = 4) (hv1 : F.term 1 D.z = 14) (hvY : F.term 2 D.z = 5) :
    False := by
  have hd4 : F.term 0 1 + 2 * F.term 1 1 = 0 := by
    have h := I.degree_zero 3
    change I.induced 3 1 = 0 at h
    simpa only [he4, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have hd3 : 1 + F.term 1 1 - F.term 0 1 + F.term 2 1 = 0 := by
    have h := I.degree_zero 2
    change I.induced 2 1 = 0 at h
    simpa only [he3, Pi.add_apply, Pi.sub_apply, Pi.one_apply] using h
  have hd0 : F.term 0 1 = -2 * F.term 1 1 := by linear_combination hd4
  have hdY : F.term 2 1 = -1 - 3 * F.term 1 1 := by linear_combination hd4 + hd3
  have hs4 : (Nat.card G : ℂ) / 147456 *
      (4 ^ 2 / (-2 * F.term 1 1) + 2 * 14 ^ 2 / F.term 1 1) = 25 / 6 := by
    have h := hI 3
    rw [he4] at h
    simp only [scalarProduct_add_left, scalarProduct_smul_left,
      F.term_pairing D k L, hd0, hv0, hv1] at h
    dsimp [pairingConstants] at h
    norm_num at h
    simp only [← Nat.card_eq_fintype_card] at h
    linear_combination h
  have hp : scalarProduct G 1 (fun g => (Theory.Character.involutionPairCount g : ℂ)) =
      (Nat.card G : ℂ) / 147456 := by
    have h := Theory.Character.scalarProduct_irreducible_involutionPairCount_of_fusion
      D.z D.z_order L.involution_fusion 1 isIrreducibleCharacter_one
    rw [D.centralizer_card] at h
    simpa only [Pi.one_apply, one_pow, div_one, mul_one, Nat.cast_ofNat,
      show (384 : ℂ) ^ 2 = 147456 by norm_num] using h
  have hs3 : (Nat.card G : ℂ) / 147456 *
      (1 + 14 ^ 2 / F.term 1 1 - 4 ^ 2 / (-2 * F.term 1 1) +
        5 ^ 2 / (-1 - 3 * F.term 1 1)) = 91 / 12 := by
    have h := hI 2
    rw [he3] at h
    simp only [scalarProduct_add_left, scalarProduct_sub_left, hp,
      F.term_pairing D k L, hd0, hdY, hv0, hv1, hvY] at h
    dsimp [pairingConstants] at h
    norm_num at h
    simp only [← Nat.card_eq_fintype_card] at h
    linear_combination h
  have hy : F.term 1 1 ≠ 0 := by
    rw [F.term_one]
    exact_mod_cast F.signedDegree_ne_zero 1
  have hu : -1 - 3 * F.term 1 1 ≠ 0 := by
    rw [← hdY, F.term_one]
    exact_mod_cast F.signedDegree_ne_zero 2
  have h := fourth_last_suzuki_elimination (Nat.card G) (F.term 1 1) hy hu hs4 hs3
  have h' : 25 * F.signedDegree 1 ^ 2 - 12572 * F.signedDegree 1 - 4124 = 0 := by
    rw [F.term_one] at h
    exact_mod_cast h
  exact fourth_last_quadratic_impossible (F.signedDegree 1) h'

end SignedAnalysis.FourthMultiplicity
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
