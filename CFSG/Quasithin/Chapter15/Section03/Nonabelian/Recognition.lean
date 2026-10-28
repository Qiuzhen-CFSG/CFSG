module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Displacement
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Statements
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Degree
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly.PlusType

/-!
# Recognition in the nonabelian branch of Section 15.3

The exports prove the full conditional 15.3.57(2), construct the nonsolvable
minimal normal subgroup, and discharge every irreducible G.9.3 alternative.
G.6.4 then supplies actual natural–dual constituent coordinates for the same
K*-action on the literal U/Z. This proves s = 1. The singular constituent's
preimage and the source power form give an actual equivalence between U and
the external central product of three D₈ groups, completing 15.3.58(2).

The explicit earlier premises are enumerated in
`NormalReduction.EarlierSourceInputs`, `EarlierActionInputs`, and
`EarlierPowerInputs`, together with the exact universal G.6.4 and adequate
G.9.3 witnesses. The parent retains their discharge. Recognition of the entire
actor as Aut(L₃(2)), its two-residual, and the specified t-interchange in
15.3.58(1),(3) remain to be proved; `ActorRecognition` is only their shared
conclusion interface. Existing conditional split-assembly APIs are preserved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1148–1149.
-/
