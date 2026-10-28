module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.PrimeDegree.Inputs
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeField

/-!
# Defining-prime coprimality for the source unitary cover

The original marked isomorphism from L/Z(L) to the arbitrary-form PSU₃(p)
model defines a perfect central cover whose kernel is exactly Z(L).
Simultaneous inversion in the model's root Sylow subgroup excludes p from
this kernel. This proves the covering input for both the binary degree
bound and the PSU₃(5) small-module calculation, for every source prime p > 3.

Sources: Aschbacher–Smith I.1.3(2), I.1.4(2), printed pp.407–408,
and the degree argument in K.2, printed p.453; Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, manuscript p.10.
-/

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v

/-- The center of the original source cover has order prime to its defining
prime. The marked quotient and arbitrary Hermitian form are preserved. -/
public theorem primeDegreeCenterCoprime : PrimeDegreeCenterCoprime.{u, v} := by
  intro G V _ _ _ _ _ ρ L _ p h hp
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h.quotient
  apply h.prime.coprime_iff_not_dvd.mpr
  simpa only [PerfectCentralCovering.centralQuotientCover_ker] using
    BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.not_defining_prime_dvd_kernel
      J h.prime (by omega : p ≠ 2) hcard hconj
      (PerfectCentralCovering.centralQuotientCover e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
