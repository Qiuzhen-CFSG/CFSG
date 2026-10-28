module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Samples
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block00From64
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block02
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block03
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block04
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block05
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block06
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block07
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block08
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block09
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block11
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block12
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block13
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block14
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block15
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block16
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block17
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.Block18

/-!
# Prime-order obstructions for all nonlocal Held representatives

The initial 47 certificates and the remaining 4,754 certificates cover every
index of the unchanged 4,831-row representative list except its thirty local
rows. Each proves the existence of an element of prime order other than two
or three in the join of the marked subgroup with the representative's cyclic
subgroup. No coverage, two-group, simplicity, or ambient-order premise is used.

The intervals below only assemble kernel-checked point-orbit certificates;
the orbit soundness theorem supplies actual elements of the original Held
carrier. Source: `source/README.md` and `source/orbits.json`.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

private theorem obstruction_of_range (lo count : ℕ) (hbound : lo + count ≤ 4831)
    (checks : ∀ i : Fin count, localBranch ⟨lo + i.val, by omega⟩ = none →
      HasPrimeObstruction (representative ⟨lo + i.val, by omega⟩))
    (j : Fin 4831) (hlo : lo ≤ j.val) (hhi : j.val < lo + count)
    (h : localBranch j = none) : HasPrimeObstruction (representative j) := by
  let i : Fin count := ⟨j.val - lo, by omega⟩
  have hi : (⟨lo + i.val, by omega⟩ : Fin 4831) = j := by
    apply Fin.ext
    dsimp [i]
    omega
  have hh := checks i
  rw [hi] at hh
  exact hh h

/-- Every nonlocal representative has an actual forbidden prime-order element. -/
public theorem obstructionChecks : ObstructionChecks := by
  intro j h
  by_cases h64 : j.val < 64
  · exact obstruction_of_range 0 64 (by decide) obstruction_initial j (by omega) h64 h
  by_cases h256 : j.val < 256
  · exact obstruction_of_range 64 192 (by decide) obstruction_block00_from64
      j (by omega) (by omega) h
  by_cases h512 : j.val < 512
  · exact obstruction_of_range 256 256 (by decide) obstruction_block01
      j (by omega) (by omega) h
  by_cases h768 : j.val < 768
  · exact obstruction_of_range 512 256 (by decide) obstruction_block02
      j (by omega) (by omega) h
  by_cases h1024 : j.val < 1024
  · exact obstruction_of_range 768 256 (by decide) obstruction_block03
      j (by omega) (by omega) h
  by_cases h1280 : j.val < 1280
  · exact obstruction_of_range 1024 256 (by decide) obstruction_block04
      j (by omega) (by omega) h
  by_cases h1536 : j.val < 1536
  · exact obstruction_of_range 1280 256 (by decide) obstruction_block05
      j (by omega) (by omega) h
  by_cases h1792 : j.val < 1792
  · exact obstruction_of_range 1536 256 (by decide) obstruction_block06
      j (by omega) (by omega) h
  by_cases h2048 : j.val < 2048
  · exact obstruction_of_range 1792 256 (by decide) obstruction_block07
      j (by omega) (by omega) h
  by_cases h2304 : j.val < 2304
  · exact obstruction_of_range 2048 256 (by decide) obstruction_block08
      j (by omega) (by omega) h
  by_cases h2560 : j.val < 2560
  · exact obstruction_of_range 2304 256 (by decide) obstruction_block09
      j (by omega) (by omega) h
  by_cases h2816 : j.val < 2816
  · exact obstruction_of_range 2560 256 (by decide) obstruction_block10
      j (by omega) (by omega) h
  by_cases h3072 : j.val < 3072
  · exact obstruction_of_range 2816 256 (by decide) obstruction_block11
      j (by omega) (by omega) h
  by_cases h3328 : j.val < 3328
  · exact obstruction_of_range 3072 256 (by decide) obstruction_block12
      j (by omega) (by omega) h
  by_cases h3584 : j.val < 3584
  · exact obstruction_of_range 3328 256 (by decide) obstruction_block13
      j (by omega) (by omega) h
  by_cases h3840 : j.val < 3840
  · exact obstruction_of_range 3584 256 (by decide) obstruction_block14
      j (by omega) (by omega) h
  by_cases h4096 : j.val < 4096
  · exact obstruction_of_range 3840 256 (by decide) obstruction_block15
      j (by omega) (by omega) h
  by_cases h4352 : j.val < 4352
  · exact obstruction_of_range 4096 256 (by decide) obstruction_block16
      j (by omega) (by omega) h
  by_cases h4608 : j.val < 4608
  · exact obstruction_of_range 4352 256 (by decide) obstruction_block17
      j (by omega) (by omega) h
  exact obstruction_of_range 4608 223 (by decide) obstruction_block18
    j (by omega) (by omega) h

end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
