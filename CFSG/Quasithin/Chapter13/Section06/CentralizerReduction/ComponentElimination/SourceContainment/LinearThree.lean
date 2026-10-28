module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.ContainmentLift
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.Source
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.OriginalSource

/-!
# Source deductions for the L₃(2) containment branch

The source doubled-natural argument proves the nonzero plus commutator.
The constructed projection has a two-group kernel on Lᵥ; the actual image
of Tᵥ ∩ K is Sylow in K⁺ and generates the projected residual by
commutators. Its normalizer is the order-twenty-four parabolic.

`lv_le_and_noncentral_original_source` constructs the normal containing
component and derives normalization of the original K before applying the
lift. The L₃(2) branch of 13.6.20 now retains only the genuine earlier
A.3.12, 13.3.2 and 13.6.3 inputs on the original marked local data.
The older conditional interfaces remain available.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.931.
-/
