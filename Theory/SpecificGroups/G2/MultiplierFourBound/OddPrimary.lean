module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.SpecificGroups.G2.MultiplierFourBound.OddPrimary.ThreeLocal
public import Theory.SpecificGroups.G2.MultiplierFourBound.OddPrimary.FiveLocal
public import Theory.GroupTheory.PerfectCentralCoverSylowNine.PartialInversion

/-!
# Odd-primary exclusions for the actual G₂(4) universal kernel

At three, the binary Heisenberg subgroup embeds with prime-to-three index.
Its two cubic generators are simultaneously inverted by a root involution,
which fixes their commutator. In any finite perfect central cover the lifted
Sylow derived subgroup is consequently cyclic of order three and maps
injectively to the base; central Sylow transfer excludes a three-kernel.

At five, orthogonal long- and short-root elements generate an elementary
subgroup of order 25. A long-root involution inverts the first generator
and centralizes the second. The lifted Sylow subgroup is therefore abelian,
and the same transfer theorem excludes five.

Both calculations below apply to the literal `universalProjection` kernel
of the split-octonion model over `GaloisField 2 2`. They discharge the two
odd-prime premises of the parent bound; the two-primary calculation remains
separate. Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407 (PDF p.418),
and GLS III §6.1, Tables 6.1.2–6.1.3. The full multiplier calculation is
Griess, Trans. AMS 183 (1973), 355–421, DOI 10.1090/S0002-9947-1973-0338148-0.
-/

namespace Atlas.G2.FiniteCover.MultiplierFourBound.OddPrimary

open PerfectCentralCovering

/-- Three does not divide the kernel of the prescribed universal projection. -/
public theorem not_three_dvd_card_kernel : ¬ 3 ∣ Nat.card (Kernel FourField) := by
  obtain ⟨Q, x, y, r, hQ, hx, hy, hz, hxz, hyz, hrx, hry, hrz⟩ :=
    exists_three_configuration
  exact not_three_dvd_card_kernel_of_simultaneous_inversion
    (universalProjection FourBase) (universalProjection_surjective FourBase)
    (universalProjection_ker_le_center FourBase) Q x y r hQ hx hy hz hxz hyz hrx hry hrz

/-- Five does not divide the kernel of the prescribed universal projection. -/
public theorem not_five_dvd_card_kernel : ¬ 5 ∣ Nat.card (Kernel FourField) := by
  obtain ⟨Q, x, y, r, hQ, hx, hxy, hrx, hry⟩ := exists_five_configuration
  exact CentralExtension.not_dvd_card_kernel_of_partial_inversion
    (universalProjection FourBase) (universalProjection_surjective FourBase)
    (universalProjection_ker_le_center FourBase) Q x y r hQ
    (by decide : Nat.Coprime 5 2) hx hxy hrx hry

end Atlas.G2.FiniteCover.MultiplierFourBound.OddPrimary
