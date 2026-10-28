module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.LocalCentralizers
public import Theory.SpecificGroups.Janko1.Model.Basic

/-!
# J₁ recognition: source hypotheses and local structure

This module exposes the exact local input for Aschbacher–Smith, I.4.9
(printed p.418), together with its proved elementary consequences. The
source statement still requires the global recognition argument: for finite
simple `G`, `IsJanko1Type G` must imply `Nonempty (G ≃* Janko1.Model)`.
No unconditional recognition theorem is asserted here. The source cites
Janko (1966) for uniqueness, and Bender (1974), §4, for an alternative
order calculation; knowing the order alone is not an isomorphism proof.
-/
