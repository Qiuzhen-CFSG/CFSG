module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Displacement
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Statements
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Constituents
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Minimal
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Assembly

/-!
# Normal-subgroup reductions for nonabelian recognition

The full constituent conclusion of 15.3.57(2) and the opening normal reduction
of 15.3.58 are proved for the actual quotient action. The earlier source
inputs are enumerated in `NormalReduction.EarlierSourceInputs`.

`NormalReduction.normal_reduction_of_earlier_source` derives positivity of s,
the three-prime quotient restrictions with the stabilizer preimage, and a
nonsolvable minimal normal subgroup with full commutator span. This subgroup
is perfect, equals its two-residual, and is actually isomorphic to a product
of one or two isomorphic nonabelian simple groups in the supplied K-class.
The constituent dimension bound then supplies the full irreducible-or-two-
summand alternative, including equal dimensions and rank-one displacement.

The subsequent recognition branches and discharge of the earlier source
inputs remain with the source-theorem parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1148–1149.
-/
