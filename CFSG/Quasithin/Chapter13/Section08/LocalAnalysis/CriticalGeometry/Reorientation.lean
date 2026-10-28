module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Equivalence
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Alternatives

/-!
# Critical-pair reorientation and geometric alternatives

`Reorientation.strict_iff` proves 13.8.7 under H=G₁=C_G(z), including
the constructed reversal of the other asymmetric orientation.
`Reorientation.alternatives_corrected` proves the complete model-or-selection
alternative needed from 13.8.8, retaining nonidentity transvection actors,
all of 13.8.5, the actual selected critical pair, the positive star rank,
the comparison with U_H/D_H, the quadratic factor-two bound, and the
constructed H-element placing the endpoint module in O₂(L₁T)≤R₁.

The corrected first alternative names its actual actors and vertices.
The literal printed δ=γg_b⁻¹ equals γ₁, whereas the proof uses γ₁g_b⁻¹.
`printed_delta_eq_base` and `corrected_delta_ne_printed` certify this
distinction. `Actors` documents the group choices, including the full
transported V_H in the commuting case. No assertion of the literal
misprinted formula is made.

All earlier source conclusions remain explicit and enumerated in the
descendant documentation. The §13.8 source assembly owner supplies them;
these results use no later §13.8 theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.7–8, printed pp.948–949 (PDF pp.965–966).
-/
