module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.Words
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges

/-!
# Assembly of order-eleven cyclic coverage in the binary J₄ model

A subgroup of order 1331 is Sylow under the proposed model order. Coverage in
that subgroup transfers to the whole group, and power-conjugacy identities
connect its two local representatives to the prescribed ATLAS words.

The local subgroup order, its two cyclic orbits, and the representative
connections are certified in the imported modules. The proposed model order
remains an explicit input to the Sylow reduction. The word construction and
source reference are in `Elevens.Words`.
-/

public section

namespace Janko4.Simplicity.Elevens

/-- The proposed group order leaves no factor of eleven in the index of a
subgroup of order 1331. -/
theorem eleven_not_dvd_index
    (hcard : Nat.card Model = 86775571046077562880)
    (P : Subgroup Model) (hP : Nat.card P = 1331) : ¬ 11 ∣ P.index := by
  intro h
  have hd : 11 ^ 4 ∣ Nat.card Model := by
    rw [← P.card_mul_index, hP]
    exact Nat.mul_dvd_mul_left 1331 h
  rw [hcard] at hd
  norm_num at hd

/-- Local coverage in any subgroup of the full eleven-part suffices. -/
theorem coverage_of_card_1331
    (hcard : Nat.card Model = 86775571046077562880)
    {ι : Type*} (r : ι → Model) (P : Subgroup Model) (hP : Nat.card P = 1331)
    (hlocal : ∀ y : Model, y ∈ P → orderOf y = 11 →
      ∃ i k g, r i = g * y ^ k * g⁻¹) : CoversPrime r 11 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hp : IsPGroup 11 P := IsPGroup.of_card (n := 3) hP
  exact prime_cyclic_coverage_of_sylow r
    (hp.toSylow (eleven_not_dvd_index hcard P hP)) hlocal

/-- The two local cyclic representatives may be connected independently to
any prescribed representative family. -/
theorem coverage_transfer {G : Type*} [Group G] {ι κ : Type*}
    (r : ι → G) (s : κ → G) (p : ℕ)
    (hlocal : CoversPrime s p)
    (hbridge : ∀ j, ∃ i m g, r i = g * s j ^ m * g⁻¹) : CoversPrime r p := by
  intro y hy
  obtain ⟨j, n, h, hj⟩ := hlocal y hy
  obtain ⟨i, m, g, hi⟩ := hbridge j
  refine ⟨i, n * m, g * h, ?_⟩
  rw [hi, hj, conj_pow, ← pow_mul]
  simp only [mul_inv_rev, mul_assoc]

/-- Assemble order-eleven coverage once the three concrete local certificates
are established. The final theorem must discharge all three certificate inputs. -/
theorem coverage_of_local_certificates
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card Model = 86775571046077562880)
    (hP : Nat.card (localSubgroup hA hB) = 1331)
    (hlocal : ∀ y : Model, y ∈ localSubgroup hA hB → orderOf y = 11 →
      ∃ j k g, localRepresentative (a hA) (b hB) j = g * y ^ k * g⁻¹)
    (hbridge : ∀ j : Fin 2, ∃ (i : Fin 12) (m : ℕ) (g : Model),
      primeRepresentative (a hA) (b hB) i =
        g * localRepresentative (a hA) (b hB) j ^ m * g⁻¹) :
    CoversPrime (primeRepresentative (a hA) (b hB)) 11 := by
  exact coverage_transfer _ _ _
    (coverage_of_card_1331 hcard _ (localSubgroup hA hB) hP hlocal) hbridge

/-- The prescribed ATLAS words cover every cyclic subgroup of order eleven in
the matrix model, assuming the proposed model order. -/
theorem covers_eleven
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card Model = 86775571046077562880) :
    CoversPrime (primeRepresentative (a hA) (b hB)) 11 := by
  exact coverage_of_local_certificates hA hB hcard
    (local_card hA hB) (local_coverage hA hB)
    (localRepresentative_bridges hA hB)

end Janko4.Simplicity.Elevens
