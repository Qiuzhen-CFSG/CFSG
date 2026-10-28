module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.Representatives
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.NormalFormCoverage
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# The 28-point geometry for Rudvalis sector coverage

The seed is the exact set used in the representative discovery, with labels
shifted from 1--4060 to 0--4059. Checked generator maps show that max4 fixes
it setwise. Its full stabilizer and the coverage of its translates remain
separate proof obligations.

The computational family consists of a candidate normal form acting on
the inverse image of the seed under a published sector word. Inverses are
essential: the discovery uses GAP's right action, while the model uses
inverse point maps as a left action. If this family covers all translates
and the seed stabilizer lies in max4, then every element is m r p with
m in max4, r a published sector word, and p in the candidate.

The exact seed and discovery code are retained in
`Representatives/source/Generate.py`. Source application: Aschbacher--Smith,
printed p.511 (PDF p.528), citing Aschbacher (1986), no.343. These conditional
reductions do not assert that source theorem or global sector coverage.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover
open Representatives RadicalCoverage.SylowCertificate
open scoped Pointwise

/-- The exact 28-set used to discover the published sectors, in model labels. -/
@[expose] public def seed : Finset (Fin 4060) :=
  {74, 404, 1022, 3326, 78, 727, 1182, 1152, 774, 3418, 2145, 1680, 2803, 1439,
    739, 1385, 2419, 3396, 2774, 2049, 2319, 3613, 125, 1751, 417, 3565, 745, 3146}

/-- Setwise stabilizer in the actual model, with no identification assumed. -/
@[expose] public def seedStabilizer : Subgroup Model := MulAction.stabilizer Model seed

public theorem seed_card : seed.card = 28 := by decide +kernel

/-- The actual max4 generators preserve the seed. -/
public theorem max4_le_seedStabilizer : max4 ≤ seedStabilizer := by
  apply (Subgroup.closure_le _).mpr
  have h (j : Fin 4) : candidateLetter j ∈ seedStabilizer := by
    change candidateLetter j • seed = seed
    rw [← Finset.image_smul]
    simp only [LocalOrder.letter_smul]
    revert j
    decide +kernel
  intro g hg
  rcases hg with rfl | hg
  · exact h 0
  · obtain rfl := Set.mem_singleton_iff.mp hg
    exact h 1

/-- Inverse sector images, evaluated using certified standard letter maps. -/
@[expose] public def sectorSet (s : Fin 76) : Finset (Fin 4060) :=
  seed.image (wordMap (inverseWord (sectorWords s)))

/-- Candidate translates evaluated using certified binary-product maps. -/
@[expose] public def normalTranslate (s : Fin 76) (n : Fin 16384) : Finset (Fin 4060) :=
  (sectorSet s).image (LocalOrder.normalMap n)

public theorem sectorSet_eq (s : Fin 76) :
    sectorSet s = (wordValue (sectorWords s))⁻¹ • seed := by
  rw [← wordValue_inverseWord, ← Finset.image_smul]
  simp only [wordValue_smul, sectorSet]

public theorem normalTranslate_eq (s : Fin 76) (n : Fin 16384) :
    normalTranslate s n = candidateNormalForm n •
      ((wordValue (sectorWords s))⁻¹ • seed) := by
  rw [← sectorSet_eq, ← Finset.image_smul]
  simp only [LocalOrder.normal_smul, normalTranslate]

/-- The finite normal forms express exactly the candidate translates of a sector. -/
public theorem exists_normalTranslate_iff (q : Finset (Fin 4060)) (s : Fin 76) :
    (∃ n, q = normalTranslate s n) ↔
      ∃ p : Model, p ∈ candidate ∧ q = p • ((wordValue (sectorWords s))⁻¹ • seed) := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨candidateNormalForm n, candidateNormalForm_mem n, normalTranslate_eq s n⟩
  · rintro ⟨p, hp, hq⟩
    obtain ⟨n, rfl⟩ := exists_candidateNormalForm hp
    exact ⟨n, hq.trans (normalTranslate_eq s n).symm⟩

/-- Stabilizer containment and coverage of seed translates imply sector coverage. -/
public theorem sector_cover_of_seed_orbits
    (hstab : seedStabilizer ≤ max4)
    (horbit : ∀ x : Model, ∃ s n, x • seed = normalTranslate s n) :
    ∀ x : Model, ∃ s m p, m ∈ max4 ∧ p ∈ candidate ∧
      x = m * wordValue (sectorWords s) * p := by
  intro x
  obtain ⟨s, n, he⟩ := horbit x⁻¹
  rw [normalTranslate_eq] at he
  let p := candidateNormalForm n
  have hp : p ∈ candidate := candidateNormalForm_mem n
  refine ⟨s, x * p * (wordValue (sectorWords s))⁻¹, p⁻¹, hstab ?_,
    candidate.inv_mem hp, ?_⟩
  · change (x * p * (wordValue (sectorWords s))⁻¹) • seed = seed
    rw [mul_smul, mul_smul, ← he, smul_inv_smul]
  · simp only [mul_assoc, inv_mul_cancel, mul_one, mul_inv_cancel]

end Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover
