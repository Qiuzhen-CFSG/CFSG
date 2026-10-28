module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.ResidualSpan
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.BaumannAssembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.InitialAssembly

/-!
# Initial local deductions for 15.3.67

`initialStructure` assembles the original local groups from the genuine
earlier conclusions and the selected escaping singular line. It proves
Thompson and Baumann equality using the actual maximum elementary family,
characteristic-normalizer control, and Sylow promotion to `G_E`.

The action of `P_c` gives the residual normal-closure equality and relative
normality of `Y_E`. The span is elementary abelian, lies in `Q_E`, and is
generated already by `C_G(E)`. The constructed marked quotient and its
selected element give the actual paired fixed-subgroup decomposition and
the offender section. The second quotient factor remains the actual
centralizer image. Frattini supplies `G_E = I M_E`, escape of `I`, and its
nontrivial image modulo `Q_E`.

All inputs to those local calculations are discharged in `initialStructure`.
Its `EarlierData` retains only the earlier source results and line selection.
The later offender classification and descent from the temporary normalizer
remain with their owners; no complete statement of 15.3.67 is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67, printed p.1153, PDF p.1170.
-/
