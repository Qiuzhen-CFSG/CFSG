module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceFlag
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.PlaneCover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.FixedPlane
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceFixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.DisplacementNormalizer

/-!
# The marked G₂ natural flag

All three field dimensions, original T-invariance and uniqueness under T
intersect L are proved for the supplied full G₂ marking. The same flag
discharges the uniqueness input of the source Cartan-normalization theorem.
The original quotient and its possible central kernel are retained.

Parabolic residual identifications and plane-orbit geometry are separate
source obligations. The PlaneCover leaf records a concrete obstruction to
deducing Irr⁺ for the entire plane preimage from a central natural cover alone.
FixedPlane proves that the actual point-parabolic residual's plane orbit is
not its family of ordinary Sylow fixed spaces in the third space. SourceFixed
transports the fixed-line obstruction through the original supplied marking.

DisplacementNormalizer provides the corrected displacement-family transport
and its literal normalizer-control application. SourceDisplacement proves
centralization of the full first preimage by the point residual. Its intrinsic
fixed-subgroup characterization retains the precise point-residual image input;
the final application also retains the genuine incidence, component uniqueness
and generation inputs. These conditional results do not complete 11.1.4.

Source: Aschbacher--Smith, 11.0.2, opening §11.1 and 11.1.3--4, pp.759--761,765.
-/
