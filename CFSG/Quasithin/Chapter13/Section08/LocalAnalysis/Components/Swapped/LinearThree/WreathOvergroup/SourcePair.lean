module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.ParabolicPair
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.SourcePair.Numerics
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.WreathOvergroup.SourcePair.Selection

/-!
# The source-compatible moving PSL₃(2) parabolic pair

The relative component images form a marked direct product of two actual
PSL₃(2) groups. The earlier prime-to-three residual identity places L₁ in
that product, and the ambient Sylow subgroup restricts to H and descends to
H*. The numerical consequence is 27 ∤ |H|.

The actual projections of the solvable subgroup (L₁T)* intersected with K₀*
are proper non-two-group Sylow overgroups. Concrete parabolic recognition
identifies them with S₄, and covariance of the projections proves compatibility
with T*. `Input.parabolicPair` constructs the published pair inside the two
respective component images. Its lift is a solvable overgroup of L₁T in H.
`Input.numerical_outputs` supplies the order bound and actual Sylow marking;
the wreath quotient and overlap automizer remain with their assembly owners.

Source: Aschbacher–Smith 13.8.16(1), printed p.952 (PDF p.969).
-/
