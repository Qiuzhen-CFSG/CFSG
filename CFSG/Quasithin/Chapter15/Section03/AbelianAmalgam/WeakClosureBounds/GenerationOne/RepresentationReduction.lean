module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.Setup
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.LocalInputs
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RankTwo
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SLTwoExtension

/-!
# Representation calculations for the generation-one argument

The actor and vector space remain the literal H/O₂(H) and U/Z from Setup.
The earlier O²(M∩H)-centralization and T-fixation imply Borel fixation of
the literal seed, by relative normality and the residual/Sylow supplement.
The B.2.14 decomposition then reduces H-fixation to the calculation on
[U/Z,O²(H)]. These implications are proved in `LocalInputs` and `FixedSpace`.

The natural SL₂, SL₃ and Sp₄ Borel fixed spaces are zero. The rank-two
calculations retain an actual automorphism twist and transport through an
equivariant linear identification of the central quotient of an invariant
subspace. Odd-index trace makes equality of Borel-fixed and group-fixed
vectors pass through extensions, including the two natural layers in the
SL₂ exception without assuming splitting.

This module does not yet establish the source representation restrictions or
15.3.65. Final assembly still requires the F.9.18(4--6), B.4.2, B.4.5 and
B.5.1 restriction argument, the Suzuki/unitary/Ω₄⁺ calculations, and their
application to the actual Irr⁺ sections and commutator module. In particular,
`seedSpace_le_fixedSpace_of_local_inputs` explicitly assumes the remaining
commutator-space calculation and the B.2.14 decomposition. Its conclusion
must not be used as an unconditional source theorem.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.65, printed p.1152; F.9.18, pp.325--326; B.2.14, p.78;
B.4.2 and B.4.5, pp.86--87; B.5.1, pp.99--100.
-/
