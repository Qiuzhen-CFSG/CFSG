module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SectorGeometry
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SectorOrbits
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SeedStabilizer
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.Representatives
public import Theory.GroupTheory.SubgroupEnumeration

/-!
# Assembly of the Rudvalis double-coset cover

Every translate of the exact 28-point seed is a candidate translate of an
inverse sector image, and its full setwise stabilizer is max4. Applying these
facts to the inverse of an arbitrary model element expresses it as a max4
element times one of the 76 sector words times a candidate element.

The published 21 local words cover max4 modulo the fixed candidate Sylow
subgroup. Each local word times a sector word has a certified factorization
through one of the 847 published representatives, with both outer factors
in the candidate. Combining these factorizations proves exhaustive coverage
of the actual Rudvalis model. The conditional reductions remain available;
`doubleCosetCover` discharges both geometric premises. This supplies the
coverage input for the separate generator-recovery assembly.

Source application: Aschbacher--Smith, printed p.511 (PDF p.528), citing
Aschbacher, *Overgroups of Sylow subgroups in sporadic groups* (1986), no.343.
The concrete carrier and word conventions are those of `Representatives`.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover
open Representatives RadicalCoverage.SylowCertificate
open scoped Pointwise

/-- Coverage by the 76 max4-left, candidate-right sectors combines with the
two certified finite factorizations to give the published double-coset cover. -/
public theorem doubleCosetCover_of_sectors
    (sector_cover : ∀ x : Model, ∃ s m p, m ∈ max4 ∧ p ∈ candidate ∧
      x = m * wordValue (sectorWords s) * p) :
    Theory.GroupTheory.SubgroupEnumeration.DoubleCosetCover candidate representative := by
  intro x
  obtain ⟨s, m, p, hm, hp, hx⟩ := sector_cover x
  obtain ⟨i, q, hq, hm'⟩ := exists_local_factor hm
  obtain ⟨k, l, r, hl, hr, he⟩ := local_sector_reduction i s
  refine ⟨k, q * l, r * p, candidate.mul_mem hq hl, candidate.mul_mem hr hp, ?_⟩
  calc
    x = (q * localValue (localWords i)) * wordValue (sectorWords s) * p := by
      rw [hx, hm']
    _ = q * (localValue (localWords i) * wordValue (sectorWords s)) * p := by
      rw [mul_assoc q]
    _ = q * (l * representative k * r) * p := by rw [he]
    _ = (q * l) * representative k * (r * p) := by simp only [mul_assoc]

/-- The two independent geometry contracts imply the published double-coset cover. -/
public theorem doubleCosetCover_of_seed_orbits
    (hstab : seedStabilizer ≤ max4)
    (horbit : ∀ x : Model, ∃ s n, x • seed = normalTranslate s n) :
    Theory.GroupTheory.SubgroupEnumeration.DoubleCosetCover candidate representative :=
  doubleCosetCover_of_sectors (sector_cover_of_seed_orbits hstab horbit)

/-- The 847 explicit representatives cover the actual model by candidate double cosets. -/
public theorem doubleCosetCover :
    Theory.GroupTheory.SubgroupEnumeration.DoubleCosetCover candidate representative :=
  doubleCosetCover_of_seed_orbits seedStabilizer_le_max4 seed_orbit_covered

/-- Every model element factors through a published representative, with both
outer factors in the certified candidate Sylow subgroup. -/
public theorem exists_representative_factor (x : Model) :
    ∃ (i : Index) (l r : Model), l ∈ candidate ∧ r ∈ candidate ∧
      x = l * representative i * r :=
  doubleCosetCover x

end Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover
