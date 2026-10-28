module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Twos.Representatives

/-!
# Assembly of Thompson involution coverage

A subgroup of order `32768` has odd index in the proposed Thompson order and
is therefore Sylow. If it lies inside the fixed `ThG1-max2W1` word subgroup,
fusion of that subgroup's involutions to `a` gives ambient involution coverage.
Both concrete certificate obligations remain explicit here; neither follows
from the ATLAS label of the subgroup.

Source words and provenance: `Twos.LocalModel` and `Twos/source/`.
-/

public section

namespace Thompson.Simplicity

open PrimeCyclicCoverage

/-- A subgroup with the full two-part of the proposed order has odd index. -/
theorem two_not_dvd_index (S : Subgroup Model)
    (hcard : Nat.card Model = 90745943887872000) (hS : Nat.card S = 32768) :
    ¬2 ∣ S.index := by
  intro hd
  have he : 65536 ∣ Nat.card Model := by
    rw [← S.card_mul_index, hS]
    exact Nat.mul_dvd_mul_left 32768 hd
  rw [hcard] at he
  exact (by decide : ¬65536 ∣ 90745943887872000) he

/-- The order and ambient fusion of a subgroup suffice for coverage. -/
theorem covers_two_of_card_32768
    (hcard : Nat.card Model = 90745943887872000)
    (S : Subgroup Model) (hS : Nat.card S = 32768)
    (hfusion : ∀ y : Model, y ∈ S → orderOf y = 2 →
      ∃ g : Model, generatorA = g * y * g⁻¹) : CoversPrime primeRepresentative 2 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hp : IsPGroup 2 S := IsPGroup.of_card (n := 15) hS
  apply prime_cyclic_coverage_of_sylow primeRepresentative
    (hp.toSylow (two_not_dvd_index S hcard hS))
  intro y hy hord
  obtain ⟨g, hg⟩ := hfusion y hy hord
  exact ⟨0, 1, g, by simpa [primeRepresentative] using hg⟩

/-- The two concrete certificates imply the requested coverage interface.
The owner must still construct the subgroup and prove the local fusion. -/
theorem covers_two_of_local_certificates
    (hcard : Nat.card Model = 90745943887872000)
    (hsubgroup : ∃ S : Subgroup Model, S ≤ TwoLocal.localSubgroup ∧ Nat.card S = 32768)
    (hfusion : TwoLocal.LocalFusion) : CoversPrime primeRepresentative 2 := by
  obtain ⟨S, hle, hS⟩ := hsubgroup
  exact covers_two_of_card_32768 hcard S hS (fun y hy ho => hfusion y (hle hy) ho)

/-- Specialization to the ten fixed matrix words. Order and fusion are the
two remaining independent certificate obligations. -/
theorem covers_two_of_sylow_candidate
    (hcard : Nat.card Model = 90745943887872000)
    (hS : Nat.card TwoLocal.SylowCandidate.subgroup = 32768)
    (hfusion : TwoLocal.SylowCandidate.InvolutionFusion) :
    CoversPrime primeRepresentative 2 :=
  covers_two_of_card_32768 hcard TwoLocal.SylowCandidate.subgroup hS hfusion

/-- Assembly from the candidate's order, its local census, and the fifteen
explicit ambient conjugacy identities. All three still require certificates. -/
theorem covers_two_of_sylow_local_certificates
    (hcard : Nat.card Model = 90745943887872000)
    (hS : Nat.card TwoLocal.SylowCandidate.subgroup = 32768)
    (hlocal : TwoLocal.SylowCandidate.LocalCoverage)
    (hbridge : ∀ i : Fin 15,
      generatorA = TwoLocal.SylowCandidate.bridgeConjugator i *
        TwoLocal.SylowCandidate.representative i *
        (TwoLocal.SylowCandidate.bridgeConjugator i)⁻¹) :
    CoversPrime primeRepresentative 2 :=
  covers_two_of_sylow_candidate hcard hS
    (TwoLocal.SylowCandidate.involutionFusion_of_certificates hlocal hbridge)

end Thompson.Simplicity
