module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.CoreAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.Relative
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.MarkedAction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.SourceAssembly

/-!
# The original paired line section

The module calculation in the proof of 15.3.67 is established from its
preceding local inputs. `Q_E` centralizes `U/E` in the genuine relative
quotient `G_E/E`. Actual fixed lifts identify the images of `C_U(τ)` and
`C_U(τ^y)` as complementary centralizer-invariant summands. Right conjugation
by the selected cubic element identifies the first with the second.

`SourceInputs.pairedEquiv` supplies binary coordinates in two copies of the
first summand, with diagonal `C_E` action; `ambientPairedEquiv` identifies
these coordinates on the actual relative group image. The marked projection
is surjective with exact kernel `E`. `SourceInputs.pairedSection` connects
the construction to the offender API using `G_E/C_{G_E}(U)`.
The second marked factor remains the actual centralizer image. The parent
retains the preceding local group inputs and assembly of the full 15.3.67.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, PDF p.1170, before the temporary replacement.
-/
