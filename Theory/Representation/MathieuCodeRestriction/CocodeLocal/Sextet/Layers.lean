module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.Parity
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.AtlasModel
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.NativeMiddle

/-!
# Native sextet cocode layers

The parity map identifies the quotient by the seven-dimensional within-tetrad
pair span with the natural module on the six parts, compatibly with the actual
stabilizer action. `Layers.Parity` proves this from Golay orthogonality and
minimum distance. Code-preserving coordinates transport the affine sextet
stabilizer, its surjective part action, and the perfect middle-factor pairing
with the hexacode. `Layers.NativeMiddle` descends the same coordinates to the
native pair quotient and retains the actual translation conjugation action.
The chapter adapter identifies its quotient representation with this dual.

Source: H.15.3(1), printed p.400 of the
Aschbacher–Smith manuscript of 1 March 2004.
-/
