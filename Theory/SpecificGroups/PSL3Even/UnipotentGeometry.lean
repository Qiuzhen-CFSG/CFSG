module

public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Transport
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.RootOrbits
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.MatrixModel

/-!
# Even-field UT₃ geometry for PSL₃

The concrete coordinate group is faithfully realized by upper-unitriangular
SL₃ and PSL₃ matrices. Its center is the highest-root subgroup; its quotient
by the center is abelian. In characteristic two the two root planes, each of
order |F|², are exactly the maximal elementary abelian subgroups, and each
noncentral involution has one of these planes as its centralizer.

The exports include transport through an actual marked group equivalence and
the natural SL₂ orbit of the highest-root subgroup in each plane. The latter
has |F|+1 distinct subgroup members. These are the local matrix facts used in
Aschbacher--Smith 5.3.5--5.3.7, printed p. 660 (PDF p. 677); ambient fusion and
identification of the source amalgam are separate inputs to the consumer.
-/
