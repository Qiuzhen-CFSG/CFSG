module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.LocalAlgebra
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.Candidates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.Markings

/-!
# Covered source nodes and exact overlap in the parabolic reduction

The literal residuals of Notation 13.2.1 are identified in one Sylow
flag through the supplied component marking. Their cubic quotient orders
come from the genuine covered natural action; their join has actual
E₉ two-core quotient, excluding dimension three. The two distinct nodes
are individually T*-invariant, so the source outer-action theorem gives
T* ≤ K* and extends the original marking to all of H*.

The full two-node residual normalizer and O₂(H) ≤ T recover the exact
original-subgroup equality H∩M = L₁T. Kernel lifting uses only
N_G(L₀) ≤ M to give N_{H*}(L₀*) ≤ N_{H*}(L₁,+*).
The degree-five output supplies every marking and overlap input to
`exclude_five_marked_pair`; its source adapter discharges them all.
The degree-four output retains the two ordered end nodes, their marked
residuals, and the projective line of binary rank two.

The genuine natural setup and explicitly named earlier chapter results
remain inputs to these conditional source deductions. The full 13.8.25
assembly, including its module conclusion and H = G₁, belongs downstream.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed pp.959–960 (PDF pp.976–977).
-/
