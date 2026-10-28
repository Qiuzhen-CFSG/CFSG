module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models.TensorIdentification
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models.Normalizers

/-!
# Concrete s = 1 calculations for the two-layer residual argument

`Models.LayerActions` retains the common matrix actor and the actual
conjugation actions on the tensor layer V and the direct sum layer P/V.
It proves the core and central-derived identities and all five numerical
conclusions needed by the local-core argument. The two actual Y-images,
also when defined using M, are elementary-layer automizers of order nine.
`Models.LayerActions.tensorCoordinates_compatible` supplies the literal
`TensorProduct` interpretation of the lower coordinates.
`Models.binaryAutEquiv` is the canonical identification of their full
automorphism groups with binary general linear groups.

`Models.LayerActions.lower_normalizer_residual` and
`Models.LayerActions.upper_normalizer_residual` prove the two literal
`IsNormalizerResidual` premises of `residual_eq_of_local_core_and_automizers`.
They apply the general order-nine normalizer theorem to the actual images.
The parent source assembly must still supply the earlier action witnesses
and local core equality before concluding the source identity O²(M) = Y.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.53–55, 15.3.58, and proof of 15.3.59, pp.1146–1150.
-/
