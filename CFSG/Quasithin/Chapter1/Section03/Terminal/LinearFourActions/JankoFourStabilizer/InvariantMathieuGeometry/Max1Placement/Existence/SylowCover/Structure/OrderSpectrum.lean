module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders

/-!
# Assembling the order spectrum of the elementary central Sylow closure

The checked Mathieu Sylow bound settles the order-2048 endpoint. Every smaller
closure is transported by actual ambient conjugation to the fixed matrix
Sylow, where its normalizer is maximal and acts irreducibly. The checked
pure-kernel catalogue and exceptional normalizer calculations restrict the
kernel branch to orders two and eight. The exhaustive outside-kernel
catalogue and invariant matrix spans exclude that branch altogether.

The final theorem discharges both inputs of the conditional assembly below.
It proves that the exact normal closure inside M has order two, eight or 2048
whenever it is elementary abelian. Establishing elementary structure from
nontriviality of the two-core remains with the parent structure theorem.

Source: Aschbacher–Smith A.3.12, printed pp.47–48, citing Aschbacher (1986);
Kleidman–Wilson (1988), pp.484–510. The imported calculations retain the
literal matrix Sylow, Mathieu kernel and ambient normalizer conventions.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover

/-- Complete assembly of the large-order calculation and the two small-order branches.
The two explicit normalizer-analysis premises are not discharged here. -/
theorem centralClosureOrderSpectrum_of_small_branches
    (hkernel : SmallKernelClosureOrders) (houtside : SmallOutsideKernelClosureOrders) :
    CentralClosureOrderSpectrum := by
  intro S M hM hSM he
  let := he
  by_cases hsmall : Nat.card (centralClosure S M hSM) < 2048
  · obtain ⟨A, hA, hc⟩ := centralClosure_fixedSylow S M hM hSM
    have hAsmall : Nat.card A < 2048 := hc ▸ hsmall
    have horder : Nat.card A = 2 ∨ Nat.card A = 8 := by
      by_cases hle : A ≤ orderSpectrumKernel
      · exact hkernel A hA hle hAsmall
      · exact houtside A hA hle hAsmall
    rw [hc] at horder
    exact horder.imp_right Or.inl
  · exact Or.inr (Or.inr (centralClosure_card_eq_2048_of_le S M hSM (by omega)))

/-- The elementary normal closure in a maximal Sylow overgroup has order two,
eight or 2048. Both exhaustive small-order branches are discharged by the
checked literal Sylow calculations. -/
theorem centralClosureOrderSpectrum : CentralClosureOrderSpectrum :=
  centralClosureOrderSpectrum_of_small_branches
    smallKernelClosureOrders smallOutsideKernelClosureOrders

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
