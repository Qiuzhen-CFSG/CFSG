module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalModel
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.Representative
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates

/-!
# Assembly of order-three coverage in the binary J4 model

An order-27 subgroup is Sylow when the model has its proposed order. Local
coverage by the two explicit words, followed by fusion of those words to
`primeRepresentative ... 2`, then proves coverage of every element of order
three. The imported matrix certificates discharge the local order, coverage,
and fusion obligations. Only the generator relations and proposed model order
remain hypotheses; the ATLAS class labels and simplicity of the model are not
used.

The local words and their source are documented in `Threes.LocalModel`.
`Threes.Representative` certifies the exact order of the designated word.
-/

public section

namespace Janko4.Simplicity

/-- An order-27 subgroup has index prime to three under the proposed model order. -/
theorem three_not_dvd_index (H : Subgroup Model)
    (hcard : Nat.card Model = 86775571046077562880) (hH : Nat.card H = 27) :
    ¬3 ∣ H.index := by
  intro hd
  have he : 81 ∣ Nat.card Model := by
    rw [← H.card_mul_index, hH]
    exact Nat.mul_dvd_mul_left 27 hd
  rw [hcard] at he
  exact (by decide : ¬81 ∣ 86775571046077562880) he

/-- The designated representative covers order-three elements once the
concrete local subgroup and its two fusion witnesses are certified. -/
theorem three_explicit_coverage_of_local_certificates
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card Model = 86775571046077562880)
    (hlocalCard : Nat.card (threeLocalSubgroup hA hB) = 27)
    (hlocal : ∀ y : Model, y ∈ threeLocalSubgroup hA hB → orderOf y = 3 →
      ∃ i k g, threeLocalRepresentative hA hB i = g * y ^ k * g⁻¹)
    (hfusion : ∀ i : Fin 2, ∃ k g,
      primeRepresentative (a hA) (b hB) 2 =
        g * threeLocalRepresentative hA hB i ^ k * g⁻¹) :
    ∀ x : Model, orderOf x = 3 → ∃ k g,
      primeRepresentative (a hA) (b hB) 2 = g * x ^ k * g⁻¹ := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : IsPGroup 3 (threeLocalSubgroup hA hB) :=
    IsPGroup.of_card (hlocalCard.trans (by decide : 27 = 3 ^ 3))
  let P : Sylow 3 Model := hp.toSylow
    (three_not_dvd_index _ hcard hlocalCard)
  have hc : ∀ x : Model, orderOf x = 3 →
      ∃ i k g, threeLocalRepresentative hA hB i = g * x ^ k * g⁻¹ :=
    prime_cyclic_coverage_of_sylow (threeLocalRepresentative hA hB) P hlocal
  intro x hx
  obtain ⟨i, k, g, hi⟩ := hc x hx
  obtain ⟨l, h, hh⟩ := hfusion i
  refine ⟨k * l, h * g, ?_⟩
  rw [hi, conj_pow, ← pow_mul] at hh
  simpa only [mul_inv_rev, mul_assoc] using hh

/-- The explicit endpoint implies the parent's prime-coverage interface. -/
theorem covers_three_of_explicit
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (h : ∀ x : Model, orderOf x = 3 → ∃ k g,
      primeRepresentative (a hA) (b hB) 2 = g * x ^ k * g⁻¹) :
    CoversPrime (primeRepresentative (a hA) (b hB)) 3 := by
  intro x hx
  obtain ⟨k, g, he⟩ := h x hx
  exact ⟨2, k, g, he⟩

/-- Every order-three element has a power conjugate to the designated word,
using the certified local subgroup and ambient fusion witnesses. -/
theorem three_explicit_coverage
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card Model = 86775571046077562880) :
    ∀ x : Model, orderOf x = 3 → ∃ k g,
      primeRepresentative (a hA) (b hB) 2 = g * x ^ k * g⁻¹ :=
  three_explicit_coverage_of_local_certificates hA hB hcard
    (threeLocal_card hA hB) (threeLocal_coverage hA hB)
    (threeLocalRepresentative_fusion hA hB)

/-- Order-three cyclic coverage in the actual binary J4 matrix model. -/
theorem covers_three
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card Model = 86775571046077562880) :
    CoversPrime (primeRepresentative (a hA) (b hB)) 3 :=
  covers_three_of_explicit hA hB (three_explicit_coverage hA hB hcard)

end Janko4.Simplicity
