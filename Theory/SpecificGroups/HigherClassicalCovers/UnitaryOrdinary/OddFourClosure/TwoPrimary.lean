module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.Splitting

/-!
# Two-primary transfer from the unitary block-pair subgroup

The local lifting theorem splits every double cover on the marked
block-pair subgroup. Odd index and transfer then exclude its kernel;
the prime-kernel quotient reduction excludes two from arbitrary finite
covering kernels. The original projection to the actual SU₄ is retained
throughout.

The matrix construction of `BlockModel` and its odd index remain explicit
in these conditional results. Thus this file does not yet prove the
unconditional two-primary part of Aschbacher--Smith I.1.4(3), printed
p.408 of `refs/quasithin.pdf`, citing GLS3 §6.1.
-/

public section

open BenderSuzuki.MatrixGroups PerfectCentralCovering

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary

universe u
variable {F : Type u} [Field F] (J : HermitianForm 4 F)
variable {q : ℕ} [Fact q.Prime]

/-- Apply the actual range section and transfer to exclude a degree-two
cover. The geometric construction and index still require proof. -/
theorem noPrimeKernel_of_block_model (hq : 3 < q) (m : BlockModel J q)
    (hi : Odd m.inclusion.range.index) : NoPrimeKernel J 2 := by
  intro E _ _ f hcard
  obtain ⟨s, hs⟩ := exists_section_on_block_model J hq m f.toMonoidHom
    f.surjective f.ker_le_center hcard
  exact not_dvd_card_kernel_of_section f m.inclusion.range hi.not_two_dvd_nat s hs
    (hcard ▸ dvd_rfl)

variable [Finite F]

/-- The local calculation applies to arbitrary finite covering kernels,
including kernels with both odd and even parts. -/
theorem not_dvd_card_kernel_of_block_model (hq : 3 < q) (m : BlockModel J q)
    (hi : Odd m.inclusion.range.index)
    {E : Type u} [Group E] [Finite E] (f : Cover E J.specialSubgroup) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker :=
  f.not_dvd_card_kernel_of_no_prime_kernel (noPrimeKernel_of_block_model J hq m hi)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary
