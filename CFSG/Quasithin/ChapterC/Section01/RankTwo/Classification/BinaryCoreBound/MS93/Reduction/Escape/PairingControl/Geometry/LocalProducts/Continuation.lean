module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.Triple
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.DualQuadratic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.Forward

/-!
# The local-product continuation after MS93 (4.3.2)(6)

The selected critical configuration transports to every M-vertex. The
backward product obtained from the residual span makes its second
Q-commutator normal in the starting stabilizer. A subgroup of the moving
neighbor's natural group with this normality is trivial, by the common
edge displacement and natural irreducibility. Quadratic duality for the actual
opposite section supplies this natural-group bound. Thus the triple vanishes,
the first commutator lies in X = Z, and Z_start lies in Vcirc_back Z_back.

The forward product uses alpha in nu(alpha+2). Transporting a whole selected
configuration, then moving its escaping edge onto the required incident edge,
makes alpha an actual backward choice for the new configuration. Its residual
span proves normality in G_(alpha+2). This deduction needs no additional
backward-commutator premise.

The residual-span outputs remain explicit conditional inputs. Their construction
from step (6), and the final source-theorem assembly, belong to the parent.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2), printed pp.885--886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- The actual dual section and backward-product normality kill the triple. -/
theorem backward_triple_eq_bot (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (q : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a)
    (hlarge : 6 < geometry.b R) (span : ResidualSpanFacts q)
    (choice : BackwardChoice q) :
    ⁅⁅Vcirc R choice.back, Q R q.a⁆, Q R q.a⁆ = ⊥ :=
  backward_triple_eq_bot_of_le_natural source hb modules facts q initial bad choice
    hlarge (span.residual choice)
    (backward_triple_le_natural hb facts q initial bad choice)

/-- The first backward commutator lies in the actual start Z-layer. -/
theorem backward_commutator_le_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (q : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a)
    (hlarge : 6 < geometry.b R) (span : ResidualSpanFacts q)
    (choice : BackwardChoice q) :
    ⁅Vcirc R choice.back, Q R q.a⁆ ≤ Z R q.a :=
  backward_commutator_le_Z_of_triple source modules choice hlarge
    (backward_triple_eq_bot source hb modules facts q initial bad hlarge span choice)

/-- The source Z-containment, with its commutator premise discharged. -/
theorem start_Z_le_backward_moving_sup_Z_of_residual_span (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (q : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a)
    (hlarge : 6 < geometry.b R) (span : ResidualSpanFacts q)
    (choice : BackwardChoice q) :
    Z R q.a ≤ Vcirc R choice.back ⊔ Z R choice.back :=
  start_Z_le_backward_moving_sup_Z source hb modules facts q initial bad choice
    (backward_commutator_le_Z source hb modules facts q initial bad hlarge span choice)

/-- The product on the original path is normal in the forward stabilizer.
The quantified spans apply to whole transported selected configurations. -/
theorem forward_product_normal (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (q : Counterexample geometry) (selected : CentralizerChoice q)
    (spans : ∀ r : Counterexample geometry, CentralizerChoice r → ResidualSpanFacts r) :
    ∃ s, Before q.a' q.a s 2 ∧
      ((Vcirc R q.a ⊔ Vcirc R s).subgroupOf (stabilizer R s)).Normal :=
  forward_product_normal_of_backward_bound source hb modules q selected spans

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
