module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.Representation.SL2NaturalFirstCohomology
public import Theory.SpecificGroups.SL2.TwoCore

/-!
# Sylow and two-core facts for the quadratic four-group factors

The literal factor `PSL(2, GaloisField 2 n)` has cyclic Sylow subgroups at
all odd primes and trivial two-core. Both facts pass through the proved
characteristic-two projective quotient equivalence: the center of SL₂ is
trivial. Odd Sylow cyclicity follows from the faithful degree-two matrix
argument; the two-core assertion transports `Matrix.SL2.twoCore_eq_bot`.

These are the concrete model inputs to the central-cover elimination in
GLS, volume 2, Theorem 25.14, Steps 2--3, using Lemma 15.12(iv)
(`refs/KGroup/GLS2/ChapterG.tex` and `ChapterD.tex`). They concern each
individual factor and supply the two premises of
`PerfectCentralCovering.Cover.kernel_eq_twoCore`.
-/

namespace Representation.QuadraticFourGroup

/-- Every odd-prime Sylow subgroup of the concrete projective factor is cyclic.
The source restriction `1 < n` is not needed for this local model fact. -/
public theorem factor_oddSylow_isCyclic (n : ℕ) :
    ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p (Factor n), IsCyclic P := by
  intro p _ hp P
  let e := SL2NaturalH1.projectiveEquiv (K := GaloisField 2 n)
  exact Matrix.SL2.odd_pGroup_isCyclic_of_injective P.isPGroup' hp
    (e.toMonoidHom.comp (P : Subgroup (Factor n)).subtype)
    (e.injective.comp (P : Subgroup (Factor n)).subtype_injective)

/-- The intrinsic two-core of the concrete projective factor is trivial. -/
public theorem factor_twoCore_eq_bot (n : ℕ) : pCore 2 (Factor n) = ⊥ := by
  have h := pCore_map_iso 2 (SL2NaturalH1.projectiveEquiv (K := GaloisField 2 n)).symm
  rw [Matrix.SL2.twoCore_eq_bot, Subgroup.map_bot] at h
  exact h.symm

end Representation.QuadraticFourGroup
