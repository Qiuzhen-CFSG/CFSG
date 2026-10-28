module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.Existence.FirstThree.Arithmetic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.Rows

/-!
# Compatibility of the six genuine constituents in Janko's second case

Orthogonality fixes the first three signed multiplicities. The third degree,
involution and Suzuki equations force the X₁, Y₁, Z₁ rows. The first two
induction equations and the first Suzuki equation then force zero products
of the final two multiplicities for every row. The family signs square to
one, so the same conclusion holds for the actual irreducible multiplicities.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 6–7, pp.12–16.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.FirstThree
open LocalModelDichotomy CharacterOrder CharacterOrder.OrderExhaustion Arithmetic
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- Each of the six actual irreducibles has zero product of its last two multiplicities. -/
public theorem caseTwo_products_zero (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) (I : SpecialInductionData D k)
    (hcard : Nat.card G = 443520) (hI : HasSuzukiPairings I)
    (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 6)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 0 - F.term 3 + F.term 5) (j : Fin 6) :
    multiplicities I (F.irreducible j) 3 * multiplicities I (F.irreducible j) 4 = 0 := by
  let r (j : Fin 6) : Row :=
    ⟨caseTwoSignedDegree F j, caseTwoSignedMultiplicity I F j 3,
      caseTwoSignedMultiplicity I F j 4⟩
  let c : Fin 6 → ℤ := ![78,153,153,-329,-202,127]
  let v : Fin 6 → ℤ := ![2,7,7,-7,-6,1]
  have hb (j : Fin 6) (i : Fin 3) := caseTwo_base_multiplicities I F h1 h2 h3 j i
  have hr (j : Fin 6) : r j ∈ rows (c j) := by
    apply mem_rows
    · simpa only [hcard, Nat.cast_ofNat] using (caseTwo_signedDegree_dvd F j).2
    · exact caseTwo_signedMultiplicity_unit I hu F j 3
    · exact caseTwo_signedMultiplicity_unit I hu F j 4
    · have hh := caseTwo_signedDegree_congruence L I F j
      have h0 := hb j 0
      have h1' := hb j 1
      have h2' := hb j 2
      change caseTwoSignedMultiplicity I F j 0 = _ at h0
      change caseTwoSignedMultiplicity I F j 1 = _ at h1'
      change caseTwoSignedMultiplicity I F j 2 = _ at h2'
      rw [h0, h1', h2'] at hh
      change (128 : ℤ) ∣ caseTwoSignedDegree F j + c j +
        280 * caseTwoSignedMultiplicity I F j 3 + 45 * caseTwoSignedMultiplicity I F j 4
      have hc : 153*caseTwoBase j 0 - 202*caseTwoBase j 1 + 127*caseTwoBase j 2 = c j := by
        fin_cases j <;> decide +kernel
      convert hh using 1
      omega
  have hv (j : Fin 6) : (r j).value (v j) = caseTwoSignedValue I F j := by
    have hh := caseTwo_signedValue_formula I F j
    have h0 := hb j 0
    have h1' := hb j 1
    have h2' := hb j 2
    change caseTwoSignedMultiplicity I F j 0 = _ at h0
    change caseTwoSignedMultiplicity I F j 1 = _ at h1'
    change caseTwoSignedMultiplicity I F j 2 = _ at h2'
    rw [h0, h1', h2'] at hh
    have hvbase : 7*caseTwoBase j 0 - 6*caseTwoBase j 1 + caseTwoBase j 2 = v j := by
      fin_cases j <;> decide +kernel
    change v j + 8*caseTwoSignedMultiplicity I F j 3 +
      3*caseTwoSignedMultiplicity I F j 4 = caseTwoSignedValue I F j
    omega
  have ht := caseTwo_third_certificate (r 0) (hr 0) (r 3) (hr 3) (r 5) (hr 5)
  have he : r 0 = ⟨154,1,0⟩ ∧ r 3 = ⟨-55,0,0⟩ ∧ r 5 = ⟨-210,0,-1⟩ := by
    apply ht
    · exact caseTwo_third_degree I F h3
    · change 1 + (r 0).value (v 0) - (r 3).value (v 3) + (r 5).value (v 5) = 16
      rw [hv, hv, hv]
      exact caseTwo_third_value I F h3
    · change 443520 * ((r 0).d * (r 3).d * (r 5).d +
        ((r 0).value (v 0))^2 * (r 3).d * (r 5).d -
        ((r 3).value (v 3))^2 * (r 0).d * (r 5).d +
        ((r 5).value (v 5))^2 * (r 0).d * (r 3).d) =
        1118208 * (r 0).d * (r 3).d * (r 5).d
      rw [hv, hv, hv]
      simpa only [hcard, Nat.cast_ofNat] using caseTwo_third_suzuki_int D k L I hI F h3
  have hd := caseTwo_first_two_degrees I F h1 h2
  have hval := caseTwo_first_two_values I F h1 h2
  have hs := caseTwo_first_suzuki D k L I hI F h1
  rw [← caseTwo_signedRatio I F 0, ← caseTwo_signedRatio I F 1,
    ← caseTwo_signedRatio I F 2, hcard] at hs
  have hd0 : caseTwoSignedDegree F 0 = 154 := congrArg Row.d he.1
  have hd3 : caseTwoSignedDegree F 3 = -55 := congrArg Row.d he.2.1
  have hv0 : caseTwoSignedValue I F 0 = 10 := by rw [← hv, he.1]; norm_num [Row.value, v]
  have hv3 : caseTwoSignedValue I F 3 = -7 := by
    rw [← hv, he.2.1]
    change (-7 : ℤ) + 8*0 + 3*0 = -7
    norm_num
  rw [hd0, hd3] at hd
  rw [hv0, hv3] at hval
  rw [hd0, hv0] at hs
  have hpq : (r 1).a*(r 1).b = 0 ∧ (r 2).a*(r 2).b = 0 := by
    apply caseTwo_first_certificate (r 1) (hr 1) (r 2) (hr 2) hd.1
    · change 10+(r 1).value (v 1)+(r 2).value (v 2) = 16
      rw [hv, hv]
      exact hval.1
    · change (443520 : ℚ)/147456 * (100/154 +
        ((r 1).value (v 1) : ℚ)^2/(r 1).d + ((r 2).value (v 2) : ℚ)^2/(r 2).d) = 31/12
      rw [hv, hv]
      norm_num at hs ⊢
      exact hs
  have hp4 : (r 4).a*(r 4).b = 0 := by
    apply caseTwo_second_certificate (r 4) (hr 4)
    · exact hd.2
    · change 10-7+(r 4).value (v 4) = 0
      rw [hv]
      exact hval.2
  have hp : (r j).a*(r j).b = 0 := by
    fin_cases j
    · change (r 0).a*(r 0).b = 0
      rw [he.1]; norm_num
    · exact hpq.1
    · exact hpq.2
    · change (r 3).a*(r 3).b = 0
      rw [he.2.1]; norm_num
    · exact hp4
    · change (r 5).a*(r 5).b = 0
      rw [he.2.2]; norm_num
  change (F.sign j * multiplicities I (F.irreducible j) 3) *
    (F.sign j * multiplicities I (F.irreducible j) 4) = 0 at hp
  rcases F.sign_eq j with hsign | hsign <;> simpa [hsign] using hp
end
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.FirstThree
