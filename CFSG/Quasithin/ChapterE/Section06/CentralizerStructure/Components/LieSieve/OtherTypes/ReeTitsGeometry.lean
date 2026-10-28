module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry.Tits
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry.ReeModels
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.ReeTitsGeometry.Ree

/-!
# Ree and Tits invariant-parabolic geometry for E.6.8

`tits_geometry` proves Q-normalization and constructs the complete block-free
family in the literal component quotient. It uses the actual Parrott carrier,
its proved Atlas equivalence, the two concrete parabolics and relative block
obstructions in their joins with Q.

`ree_geometry` proves the same output for the exact LocalBlockInput carrier
in `RankTwoTheoremC.ree`. The embedded Tits subgroup forces Q-normalization;
Sylow marking and two-power stability give invariant full parabolics, including
their complementary tori. The intrinsic core and block calculations discharge
characteristic two and absence of relatively subnormal chi-zero blocks in
their lifted joins with Q. No additional model premise remains in either
branch. The E.6.7 application and final exclusions remain with the OtherTypes
assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/
