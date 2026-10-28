module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.Existence.FirstThree.Arithmetic
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseOneLarge.Rows

/-!
# Excluding the first Janko decomposition at order 443520

The genuine X₂, Z₁, Z₂ constituents give signed rows with initial columns
(1,0,1), (0,0,1), (0,0,1). Degree divisibility, unit multiplicities and Sylow
two-group restriction put them in the complete arithmetic lists. Evaluation
at the identity and involution, together with the third Suzuki equation,
contradicts the kernel-checked certificate. No ratio bound is required.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 6–7, pp.12–16.
-/

open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.FirstThree
open LocalModelDichotomy CharacterOrder CharacterOrder.OrderExhaustion
open CaseOneLarge Arithmetic
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- The first decomposition contradicts the three actual character equations. -/
public theorem caseOne_impossible (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) (I : SpecialInductionData D k)
    (hcard : Nat.card G = 443520) (hI : HasSuzukiPairings I)
    (hu : HasUnitMultiplicities I.induced) (F : SignedFamily G 7)
    (h1 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (h2 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6) : False := by
  let r (j : Fin 3) : Row :=
    ⟨signedDegree F j, signedMultiplicity I F j 3, signedMultiplicity I F j 4⟩
  have hr (j : Fin 3) : r j ∈ rows (if j = 0 then 280 else 127) := by
    apply mem_rows
    · simpa only [hcard, Nat.cast_ofNat] using signedDegree_dvd F j
    · have ha := signedMultiplicity_bounds I hu F j 3
      change signedMultiplicity I F j 3 ∈ ([-1, 0, 1] : List ℤ)
      simp only [List.mem_cons]
      omega
    · have hb := signedMultiplicity_bounds I hu F j 4
      change signedMultiplicity I F j 4 ∈ ([-1, 0, 1] : List ℤ)
      simp only [List.mem_cons]
      omega
    · exact signedDegree_congruence D k L I F h1 h2 h3 j
  have hv0 : (r 0).value 8 = signedValue I F 0 := by
    simpa [Row.value, r] using (signedValue_columns I F h1 h2 h3 0).symm
  have hv1 : (r 1).value 1 = signedValue I F 1 := by
    simpa [Row.value, r] using (signedValue_columns I F h1 h2 h3 1).symm
  have hv2 : (r 2).value 1 = signedValue I F 2 := by
    simpa [Row.value, r] using (signedValue_columns I F h1 h2 h3 2).symm
  have hd : 1 + (r 0).d + (r 1).d + (r 2).d = 0 := by
    have hh := signedDegree_sum I F h3
    simp [Fin.sum_univ_succ] at hh
    change 1 + signedDegree F 0 + signedDegree F 1 + signedDegree F 2 = 0
    linarith
  have hv : 1 + signedValue I F 0 + signedValue I F 1 + signedValue I F 2 = 16 := by
    have hh := congrFun h3 D.z
    have hz : I.induced 2 D.z = 16 := by
      simpa [SpecialInductionData.induced, specialRepresentative, CaseII.into_z_zero,
        exceptionalValues] using I.values 2 0
    rw [hz] at hh
    simp only [Pi.add_apply, Pi.one_apply, SignedFamily.term, Pi.smul_apply,
      smul_eq_mul, involutionValue_eq I (F.irreducible _)] at hh
    simpa [signedValue, selected] using (show (1 : ℤ) +
      F.sign 1 * involutionValue I (F.irreducible 1) +
      F.sign 5 * involutionValue I (F.irreducible 5) +
      F.sign 6 * involutionValue I (F.irreducible 6) = 16 by exact_mod_cast hh.symm)
  apply caseOne_certificate (r 0) (hr 0) (r 1) (hr 1) (r 2) (hr 2) hd
  · rwa [hv0, hv1, hv2]
  · rw [hv0, hv1, hv2]
    simpa only [hcard, Nat.cast_ofNat] using signed_suzuki_polynomial D k L I hI F h3
end
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.FirstThree
