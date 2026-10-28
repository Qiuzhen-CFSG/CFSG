module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.FieldResidual
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Action
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.ModelAction

/-!
# The corrected field-centralizer argument

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
Lemma 15.3.38, printed p.1137; the two-component convention is on p.414.

The genuine I.3.2 embedding and the odd-core injection into E₉ imply that the
actual field residual O²(C_L(f)), identified with PSL₃(2), lies in E(C_G(f)).
For a quasisimple component normal in C_G(f), fusion constructs a conjugate
TI four-group U with joint residual E₉. This residual is the joint odd core.
The plane acts nontrivially and faithfully on the component and fixes the
two-residual of each of its nonidentity elements' centralizers there.

`ModelAction` reduces the containment to the three-core of the actual action
image of the joint centralizer. It proves the image contains the fixed inner
automorphisms and centralizes the faithful plane action. The conditional
terminal theorem assembles the contradiction from an intrinsic model theorem;
that theorem has not yet been proved for the three component alternatives.

The remaining obligations are the rank-one component exclusion, the selection
of the rank-two component containing the field residual, its three exact
central-quotient alternatives, and the model calculation forcing the joint
residual to centralize that component. `FieldModels` retains PSL₃(4), J₂,
PSL₃(7), both exceptional SL₃ covers and the unique-order-three odd-center
clause. `JointCentralizer.jointResidual_not_le_component_centralizer` supplies
the opposing containment obstruction once these obligations are discharged.
No unconditional terminal contradiction or numbered source theorem is asserted.
-/
