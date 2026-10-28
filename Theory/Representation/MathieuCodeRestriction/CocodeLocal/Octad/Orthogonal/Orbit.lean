module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Orthogonal

/-!
# Nonsingular octad classes and the actual weight-two orbit

Complementing within the octad produces a representative of weight at most
four. If its cocode class is a duad, Golay minimum distance forces the
representative to be that duad itself. Thus both points belong to the octad,
and the half-weight form is one precisely on the intersection with the
native M24 weight-two orbit.

Source: Aschbacher--Smith, H.15.2(2--3), printed pp.398--399.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.CocodeOctad

private lemma extend_weight (B : Finset (Fin 24)) (w : B → Bit) :
    hammingNorm (extend B w) = hammingNorm w := by
  rw [Atlas.Codes.hammingNorm_eq_sum, Atlas.Codes.hammingNorm_eq_sum]
  calc
    _ = ∑ i ∈ B, if extend B w i = 0 then 0 else 1 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ B)
      intro i _ hi
      simp [extend_apply_not_mem B w i hi]
    _ = ∑ i : B, if extend B w i = 0 then 0 else 1 :=
      Finset.sum_subtype B (fun _ => Iff.rfl) _
    _ = _ := by simp

private lemma complement_weight_sum {ι : Type*} [Fintype ι] (w : ι → Bit) :
    hammingNorm w + hammingNorm (w + fun _ => 1) = Fintype.card ι := by
  rw [Atlas.Codes.hammingNorm_eq_sum, Atlas.Codes.hammingNorm_eq_sum,
    ← Finset.sum_add_distrib]
  have ht : ∀ a : Bit, (if a = 0 then 0 else 1 : ℕ) +
      (if a + 1 = 0 then 0 else 1) = 1 := by decide
  simp only [Pi.add_apply, ht, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one]

/-- Every octad class has a supported representative of weight at most four. -/
lemma exists_small_representative (O : Octad) (v : supportedPairSpace O.val) :
    ∃ w : BinaryPermutation.core O.val, toCocode O.val w = v.val ∧
      hammingNorm (extend O.val w.val) ≤ 4 := by
  have hc : Fintype.card O.val = 8 := by simp [m24Blocks_card _ O.property]
  let : Nonempty O.val := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨w, hw⟩ := (show v.val ∈ (toCocode O.val).range by
    rw [range_toCocode]; exact v.property)
  by_cases hs : hammingNorm w.val ≤ 4
  · exact ⟨w, hw, by rwa [extend_weight]⟩
  let one : BinaryPermutation.core O.val := ⟨BinaryPermutation.allOne O.val,
    (BinaryPermutation.constants_le_core_iff O.val).mpr (by rw [hc]; decide)
      (Submodule.subset_span (Set.mem_singleton _))⟩
  have hz : toCocode O.val one = 0 := by
    change one ∈ (toCocode O.val).ker
    rw [ker_toCocode]
    exact Submodule.subset_span (Set.mem_singleton _)
  refine ⟨w + one, by rw [map_add, hz, add_zero, hw], ?_⟩
  rw [extend_weight]
  have h := complement_weight_sum w.val
  rw [hc] at h
  change hammingNorm (w.val + fun _ => 1) ≤ 4
  omega

/-- Minimum distance forces every weight-two class in the supported space to
have its two coordinates inside the octad. -/
lemma pairVector_mem_supportedPairSpace_iff (O : Octad) (P : PointPair) :
    pairVector P ∈ supportedPairSpace O.val ↔ P.val ⊆ O.val := by
  constructor
  · intro hv
    obtain ⟨w, hw, hs⟩ := exists_small_representative O ⟨pairVector P, hv⟩
    have hg : extend O.val w.val - wordOfSet P.val ∈ golay := by
      have hq : codeInCore.mkQ (coreInclusion O.val w -
          ⟨wordOfSet P.val, wordOfSet_mem_core P⟩) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr hw
      exact (Submodule.Quotient.mk_eq_zero codeInCore).mp hq
    have he : extend O.val w.val = wordOfSet P.val := by
      apply sub_eq_zero.mp
      by_contra hn
      have hmin := native_golay_minimum hg hn
      have hweight := Atlas.Codes.binary_weight_add (extend O.val w.val) (wordOfSet P.val)
      rw [wordOfSet_weight, P.property] at hweight
      have heq : extend O.val w.val - wordOfSet P.val =
          extend O.val w.val + wordOfSet P.val := by
        ext i
        exact CharTwo.sub_eq_add _ _
      rw [heq] at hmin
      omega
    intro i hi
    by_contra hn
    have h := congrFun he i
    rw [extend_apply_not_mem _ _ _ hn] at h
    simp [wordOfSet, hi] at h
  · exact pairVector_mem_supportedPairSpace P

/-- The nonsingular set is precisely the intersection with the actual M24
weight-two orbit, including the converse containment. -/
lemma quadratic_one_iff_weightTwo (O : Octad) (v : supportedPairSpace O.val) :
    quadratic O v = 1 ↔ v.val ∈ weightTwoOrbit := by
  constructor
  · exact quadratic_nonsingular_mem_weightTwo O
  · rintro ⟨P, hP⟩
    have hs : P.val ⊆ O.val := (pairVector_mem_supportedPairSpace_iff O P).mp
      (hP.symm ▸ v.property)
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp P.property
    have ha : a ∈ O.val := hs (by simp [he])
    have hb : b ∈ O.val := hs (by simp [he])
    have hab' : (⟨a, ha⟩ : O.val) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
    apply (quadratic_one_iff_internal_pair O v).mpr
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, hab', ?_⟩
    rw [← hP]
    have hstar : starWord O.val ⟨a, ha⟩ ⟨b, hb⟩ =
        ⟨Pi.single ⟨a, ha⟩ 1 + Pi.single ⟨b, hb⟩ 1,
          pair_mem_core ⟨a, ha⟩ ⟨b, hb⟩⟩ := by
      apply Subtype.ext
      exact add_comm _ _
    rw [hstar, toCocode_pair _ _ hab']
    exact congrArg pairVector (Subtype.ext he)

end MathieuCode.CocodeOctad
