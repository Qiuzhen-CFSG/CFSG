module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.ClosureBounds
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.LocalIdentification
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.Branches
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.CoverGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.Initial

/-!
# The original symplectic radical action and conditional closure assembly

The Cartan calculation proves [V,KY]≤O₂(KY) from 11.5.6(4--5), and
therefore V,W_H≤O₂(G₁). The preceding closure theorem supplies U≤O₂(G₁)
and [U,O₂(G₁)]≤V₁ on the strict original flag.

The full original L-action has kernel O₂(L). Factoring it through the
supplied marking transports the native point-radical chief series and
indecomposability to Aut(V), preserving C_V(L). The literal local residual
is identified from a symplectic point coordinate. Conditional closure
assembly then proves U abelian, the auxiliary W's root image, both requested
commutators, and Φ(W)≤V₁. The W=U branch uses Φ(U)=1.

The full-cover root/radical commutators are proved in CoverGeometry on the
original marked module, retaining C_V(L). FullAmbient proves the R₁-image
and local hyperplane-fixer bounds through the faithful quotient action.
Initial combines these results: only preceding flag, Cartan and 11.5.6
inputs remain explicit. Final assembly remains with
qt-d-1222-natural-closure-sp4.
Source: Aschbacher--Smith 11.5.7, printed pp.782--783.
-/
