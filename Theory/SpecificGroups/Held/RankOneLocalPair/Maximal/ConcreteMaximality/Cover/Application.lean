module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality

/-!
# Applying the unconditional Held max5 cover certificate

The checked commutation equations discharge the cover premise of the existing
assembly for the actual max5 subgroup. Absolute maximality now needs only the
independent generator-recovery certificate. Source: ATLAS HeG1-max5W1 and
Aschbacher–Smith E.1.14(4), printed p.214; see ../source/README.md.
-/

namespace Held.RankOneLocalPair.ConcreteMaximality

/-- The 34 specified representatives cover the actual Held carrier modulo max5. -/
public theorem covers (g : Held.He) :
    Theory.GroupTheory.DoubleCosetTransitions.Covered
      Held.TwoLocalCandidates.max5 shortRepresentative g :=
  covers_of_checks coverChecks g

/-- Only generator recovery remains in the absolute-maximality assembly. -/
public theorem max5_isCoatom_of_recovery (h : RecoveryChecks) :
    IsCoatom Held.TwoLocalCandidates.max5 :=
  max5_isCoatom_of_checks coverChecks h

end Held.RankOneLocalPair.ConcreteMaximality
