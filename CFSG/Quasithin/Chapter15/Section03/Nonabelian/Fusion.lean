module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Constructions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Centralizers
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Orbit
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.InvolutionCount
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Assembly

/-!
# The fusion stage of the nonabelian case

The centralizer comparison in 15.3.60, its two nonfusion deductions, and
the final four-orbit implication in 15.3.61 are proved under their precise
local inputs. The definitions retain the actual fixed-point preimage in
`U/Z`, the blocks `B_i = C_P(D_i)V`, and generating involutions for the
source's two order-two subgroups.

The local-product check also detects the printed `E₁₆` in the proof of
15.3.61: in the actual `E₈ × D₈` product the two covering elementary
subgroups have order 32. The model is not identified with an arbitrary
ambient subgroup merely by its order.

`Assembly.source_fusion_of_earlier_data` now combines the core calculation,
the constructed cubic centralizers and separating involution, and the actual
natural/dual orbits and block normalizers. It proves all four clauses of
15.3.59 and supplies the exact transfer inputs of 15.3.60–61.
`Assembly.false_of_earlier_data` applies transfer to these witnesses.
The earlier local geometry and recognition through 15.3.58 remain explicit
inputs, to be discharged by the enclosing 15.3.50 source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1149–1151.
-/
