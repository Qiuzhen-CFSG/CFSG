module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.Words
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Matrices

/-!
# Power-conjugacy bridges for the local eleven-elements

The prescribed representatives at indices 5 and 6 are conjugate to the seventh
power of `localZ` and to `localX`, respectively. Explicit straight-line words
provide the conjugators, and kernel-checked packed binary arithmetic proves
the identities in the actual matrix group. These results need neither local
subgroup cardinality nor a fusion or simplicity theorem.

The source words are the ATLAS J4 class words and J4G1-max7W1 program, documented
and attributed in `Simplicity.Words` and `Elevens.Words`. The witness search and
reproducible certificate generation are described in
`RepresentativeBridges.Witnesses`.
-/

@[expose] public section
namespace Janko4.Simplicity.Elevens

/-- An explicit word conjugating the seventh power of the central local element. -/
def centralConjugator {G : Type*} [Group G] (a b : G) : G :=
  BridgeCertificate.w104 a b

/-- An explicit word conjugating the noncentral local element. -/
def noncentralConjugator {G : Type*} [Group G] (a b : G) : G :=
  BridgeCertificate.w298 a b

/-- The prescribed representative at index 5 is conjugate to `localZ ^ 7`. -/
theorem primeRepresentative_five_eq_conjugate_localZ
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    primeRepresentative (a hA) (b hB) 5 =
      centralConjugator (a hA) (b hB) * localZ (a hA) (b hB) ^ 7 *
        (centralConjugator (a hA) (b hB))⁻¹ := by
  rw [← BridgeCertificate.target5_eq, ← BridgeCertificate.localZ_eq]
  exact BridgeCertificate.checked_z hA hB

/-- The prescribed representative at index 6 is conjugate to `localX`. -/
theorem primeRepresentative_six_eq_conjugate_localX
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    primeRepresentative (a hA) (b hB) 6 =
      noncentralConjugator (a hA) (b hB) * localX (a hA) (b hB) *
        (noncentralConjugator (a hA) (b hB))⁻¹ := by
  rw [← BridgeCertificate.target6_eq, ← BridgeCertificate.localX_eq]
  exact BridgeCertificate.checked_x hA hB

/-- Both local representatives connect to the prescribed prime representatives. -/
theorem localRepresentative_bridges
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ∀ j : Fin 2, ∃ (i : Fin 12) (m : ℕ) (g : Model),
      primeRepresentative (a hA) (b hB) i =
        g * localRepresentative (a hA) (b hB) j ^ m * g⁻¹ := by
  intro j
  fin_cases j
  · exact ⟨5, 7, centralConjugator (a hA) (b hB),
      primeRepresentative_five_eq_conjugate_localZ hA hB⟩
  · refine ⟨6, 1, noncentralConjugator (a hA) (b hB), ?_⟩
    change primeRepresentative (a hA) (b hB) 6 =
      noncentralConjugator (a hA) (b hB) * localX (a hA) (b hB) ^ 1 *
        (noncentralConjugator (a hA) (b hB))⁻¹
    simpa only [pow_one] using primeRepresentative_six_eq_conjugate_localX hA hB

end Janko4.Simplicity.Elevens
