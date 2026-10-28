module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic
public import CFSG.KnownSimple.FischerCarrierContribution
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinary
public import Theory.Quasithin.InvolutionCentralizerQuotientRank

/-!
# The rank route for the three Fischer centralizer obstructions

GLS3 Tables 5.3t--v supply the intended sections U₆(2) in Fi₂₂, and Fi₂₂
in Fi₂₃ and Fi₂₄′. Their double covers must be quotiented, not embedded
as if they split. For Fi₂₄′ use the inner 2A class; the 2C class in the
table is outside Fi₂₄′. The transcription's Fi₁₂ in Table 5.3u is Fi₂₂,
as confirmed by the explanatory paragraph on the Fischer groups there.

This module proves the downstream rank argument: 2-group kernels lift
3-rank, and the involution puts that rank in a genuine two-local. It uses
the fixed ATLAS permutation carriers and the fixed projective U₆(2)
matrix carrier. The actual three quotient maps and the U₆(2) rank bound
remain explicit premises. Accordingly these conditional theorems alone
do not prove any Fischer case of A.2.19.

Source: Aschbacher--Smith, A.2.19, printed pp. 40--41 (PDF pp. 51--52),
and GLS3, `refs/KGroup/GLS3/Chapter5(sec3-).tex`, Tables 5.3t--v.
-/

public section

namespace CFSG.Quasithin.ChapterA

namespace InvolutionCentralizerQuotientData

variable {G S : Type*} [Group G] [Finite G] [Group S] [Finite S]

/-- The section rank is genuinely local when the actual quotient kernel is a
2-group. No simplicity of either group is required. -/
theorem primeRank_le_twoLocalPrimeRank
    (d : InvolutionCentralizerQuotientData G S) (hk : IsPGroup 2 d.quotientMap.ker)
    (p : ℕ) [Fact p.Prime] (ho : Odd p) :
    primeRank p S ≤ twoLocalPrimeRank p G :=
  Theory.Quasithin.primeRank_le_twoLocalPrimeRank_of_centralizer_two_quotient
    d.involution_order d.numerator d.centralizes d.quotientMap d.surjective hk p ho

/-- A section of odd rank at least three excludes quasithinness of the ambient
group, provided its quotient kernel is a 2-group. -/
theorem not_quasithin_of_rank
    (d : InvolutionCentralizerQuotientData G S) (hk : IsPGroup 2 d.quotientMap.ker)
    (p : ℕ) [hp : Fact p.Prime] (ho : Odd p) (hr : 3 ≤ primeRank p S) :
    ¬ IsQuasithin G := by
  intro hG
  have hle := (hr.trans (d.primeRank_le_twoLocalPrimeRank hk p ho)).trans
    (isQuasithin_iff_twoLocalPrimeRank.mp hG p hp.out ho)
  omega

end InvolutionCentralizerQuotientData

namespace FischerCentralizerSections

open Sporadic.Fischer
open Theory.SpecificGroups

/-- Conditional final rank assembly for the fixed three Fischer carriers.
The concrete centralizer constructions and matrix rank calculation must be
supplied before applying this as a sporadic obstruction. -/
theorem not_quasithin_of_two_quotients
    (d22 : InvolutionCentralizerQuotientData Fi22.Carrier U6Two.Carrier)
    (h22 : IsPGroup 2 d22.quotientMap.ker)
    (d23 : InvolutionCentralizerQuotientData Fi23.Carrier Fi22.Carrier)
    (h23 : IsPGroup 2 d23.quotientMap.ker)
    (d24 : InvolutionCentralizerQuotientData Fi24Prime.Carrier Fi22.Carrier)
    (h24 : IsPGroup 2 d24.quotientMap.ker)
    (hr : 3 ≤ primeRank 3 U6Two.Carrier) :
    ¬ IsQuasithin Fi22.Carrier ∧ ¬ IsQuasithin Fi23.Carrier ∧
      ¬ IsQuasithin Fi24Prime.Carrier := by
  have ho : Odd (3 : ℕ) := by decide
  have hr22 : 3 ≤ primeRank 3 Fi22.Carrier :=
    (hr.trans (d22.primeRank_le_twoLocalPrimeRank h22 3 ho)).trans
      (twoLocalPrimeRank_le_primeRank 3)
  exact ⟨d22.not_quasithin_of_rank h22 3 ho hr,
    d23.not_quasithin_of_rank h23 3 ho hr22,
    d24.not_quasithin_of_rank h24 3 ho hr22⟩

end FischerCentralizerSections
end CFSG.Quasithin.ChapterA
