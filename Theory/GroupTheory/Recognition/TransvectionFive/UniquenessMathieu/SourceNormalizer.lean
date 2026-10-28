module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Boundary
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Fusion
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Catalogue
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Intersections
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Column
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Plane
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Row
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Transport
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.ThreeSpace
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Centralizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Assembly
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Complete
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Geometry

/-!
# The proved source Mathieu normalizer family

`SourceData.ofFusion` orients the original marking to the 21/45 counts and
constructs all corrected source-local data from `MathieuFusion` in a finite
group. No further normalizer, centralizer or fusion premise remains.

The literal row quotient has its faithful natural L₄(2) action and splits;
the column normalizer is C_G(z). The plane quotient is L₃(2) × S₃ with its
marked tensor action. The original A₂ quotient has order 2160, and its
action on six actual elementary four-subgroups has normal kernel of order
three and quotient S₆. All marked intersection orders and normalizer
identities are retained.

For the source second involution class, the actual I/A₂ is S₅ and
C_{A₂}(I^∞) is exactly its exceptional four-subgroup. A genuine cubic
subgroup X has XA₂ normal in N_G(A₂), and the four-subgroup normalizer is
XI as both a subgroup join and a set product. The missing fusion exclusion
is proved by transporting the 42-element non-root involution orbit in the
literal point two-core to a rank-two element of the 21-point rectangle.

`oriented_row_flag_generate` applies these constructed data to the actual
source coset geometry. The legacy normalizer and pair-graph APIs remain
unchanged; ambient M₂₄ recognition is a separate source-geometry theorem.

Source: Aschbacher, *Sporadic Groups* (1994), §§39–41, printed pp.213–222.
-/
