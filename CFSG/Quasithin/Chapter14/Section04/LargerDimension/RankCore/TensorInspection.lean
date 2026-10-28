module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.TensorInspection.AlternatingCore
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.TensorInspection.Natural
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.TensorInspection.Assembly

/-!
# Tensor rank calculations for 14.4.6(a)

For the orthogonal A₅-module tensor product, a nonidentity low-rank actor
must be a pure S₅ transposition and has moved rank exactly two. Parity
excludes the A₅ × S₃ alternative. For a natural degree-two semilinear tensor
model, every nonidentity actor has moved rank at least four. All applications
retain the actual H/O₂(H) action on U/Z(U) and explicit equivariance.

`SourceAction.tensor_inspection` assembles all four group/module alternatives
from an A₅-only constituent marking. It proves semilinearity of the natural
extension and equivariance of the deleted extension. Sylow normalization of
the actual binary quotient line gives nonzero singular tensor coordinates
and excludes that line from displacement. The precise earlier-source inputs
are the faithful quotient action, the model marking, and the normalized
one-dimensional image; no rank or singular-coordinate conclusion is assumed.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 14.4.2(5)
and 14.4.6(a), printed pp.1006,1008.
-/
