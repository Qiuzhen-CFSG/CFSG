module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.SmallOvergroups
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.SectionTransport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointTransport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.SixPoint
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.NaturalDual

/-!
# Toward the final model exclusions in 15.3.49

The completed deductions transport strong and best offenders from the actual
conjugation action on `U_H/Z`, identify point stabilizers and their intrinsic
two-cores under equivariant coordinates, and apply the proved six-letter
offender classification. An overgroup with literal quotient `S₃ × S₃` is
proved solvable, so (j) puts it in `M_H`.

The full conditional final contradiction remains open. Its remaining work is:

* derive the binary parabolic-generation alternative from `BinaryLocalData`;
* apply B.5.1 at the `L₃(2)` point and localize this reduction to smaller
  overgroups with their own quotient actions;
* select the natural-plus-dual section in the `S₈` middle-node case and
  apply B.4.9(2iii) to the actual `O₂(Y₀* T*)` offender;
* assemble these with the exact (i)–(l), (h), (n) outputs, the B.4.2 ratio
  bounds on identified exceptional-model sections, and all six-letter
  module alternatives supplied by B.5.1.

The transport lemmas take module identifications or numerical bounds as
explicit inputs. They do not establish those earlier source results or
identify an arbitrary module with a conjugation section. In particular the
containment premise for smaller `L₃(2)` overgroups in
`exclude_by_small_overgroups` must be proved before source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1144–1145. No completed numbered source theorem is asserted here.
-/
