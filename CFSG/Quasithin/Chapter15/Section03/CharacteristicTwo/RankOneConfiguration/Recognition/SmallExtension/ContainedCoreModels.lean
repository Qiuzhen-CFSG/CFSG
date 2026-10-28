module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.CoverDuality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.BlockTransport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.G2Source

/-!
# Core containment in the small marked configurations

The source normalizer and residual identities put [Q,Y₊] in O₂(Y₊).
For the A₆ and G₂ blocks, contragredient cocycle detection generates
the whole short-block covering module, including its central kernel.
The third linear configuration uses both dual summands and lifts through
the full natural center of Q. In all three cases this gives Q = [Q,Y₊],
Q ≤ O₂(Y₊), centralization by D = C_I(Y₊), and exclusion through
SourceData.excluded_of_models.

These results take exactly the corresponding MarkedModels fields and
SourceData. Construction of the marked models, and the two abelian
linear configurations, remain with the parent source assembly.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149).
-/
