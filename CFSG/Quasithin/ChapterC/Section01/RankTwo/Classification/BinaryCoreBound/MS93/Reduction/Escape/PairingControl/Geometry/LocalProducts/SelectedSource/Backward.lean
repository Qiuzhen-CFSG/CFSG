module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.SelectedSource.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.DualQuadratic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.Forward.Cover

/-!
# Backward local products from the separating source choice

Apply the checked opposite-section calculation and triple-commutator
normality to the residual bound of the actual separating choice. This
kills the triple, puts the first commutator in Z_alpha, and covers Z_alpha
by Vcirc_(alpha-2) Z_(alpha-2). The final existence theorem constructs
the choice and discharges its separation and residual premises.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2), the final paragraph
of printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.SelectedSource
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : MS93.Geometry R}

/-- The actual opposite section bounds the triple; local normality makes it vanish. -/
theorem backward_triple_eq_bot (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (q : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a)
    (hlarge : 6 < geometry.b R) (span : ResidualFacts q)
    (choice : BackwardChoice q)
    (hsep : ¬ criticalCommutator q.a q.a' ≤ edgeDisplacement q.a choice.edge) :
    ⁅⁅Vcirc R choice.back, Q R q.a⁆, Q R q.a⁆ = ⊥ :=
  Continuation.backward_triple_eq_bot_of_le_natural source hb modules facts q initial bad
    choice hlarge (span.residual choice hsep)
    (Continuation.backward_triple_le_natural hb facts q initial bad choice)

/-- The first backward commutator lies in the starting Z-layer. -/
theorem backward_commutator_le_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (q : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a)
    (hlarge : 6 < geometry.b R) (span : ResidualFacts q)
    (choice : BackwardChoice q)
    (hsep : ¬ criticalCommutator q.a q.a' ≤ edgeDisplacement q.a choice.edge) :
    ⁅Vcirc R choice.back, Q R q.a⁆ ≤ Z R q.a :=
  Continuation.backward_commutator_le_Z_of_triple source modules choice hlarge
    (backward_triple_eq_bot source hb modules facts q initial bad hlarge span choice hsep)

/-- The source Z-containment for the same separating backward choice. -/
theorem start_Z_le_backward_moving_sup_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (q : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a)
    (hlarge : 6 < geometry.b R) (span : ResidualFacts q)
    (choice : BackwardChoice q)
    (hsep : ¬ criticalCommutator q.a q.a' ≤ edgeDisplacement q.a choice.edge) :
    Z R q.a ≤ Vcirc R choice.back ⊔ Z R choice.back :=
  Continuation.start_Z_le_backward_moving_sup_Z source hb modules facts q initial bad choice
    (backward_commutator_le_Z source hb modules facts q initial bad hlarge span choice hsep)

/-- Source inputs construct one actual choice with all backward local-product deductions. -/
theorem exists_backward_deductions (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (selected : CentralizerChoice p) :
    ∃ choice : BackwardChoice p,
      (¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge) ∧
      ⁅choice.W, Ltilde R p.a⁆ ≤ Vcirc R p.a ∧
      ((Vcirc R p.a ⊔ Vcirc R choice.back).subgroupOf (stabilizer R p.a)).Normal ∧
      ⁅⁅Vcirc R choice.back, Q R p.a⁆, Q R p.a⁆ = ⊥ ∧
      ⁅Vcirc R choice.back, Q R p.a⁆ ≤ Z R p.a ∧
      Z R p.a ≤ Vcirc R choice.back ⊔ Z R choice.back := by
  have span := residual_facts source hb modules transfer initial facts p bad hlarge selected
  obtain ⟨choice, hsep⟩ := span.backward
  exact ⟨choice, hsep, span.residual choice hsep,
    backward_product_normal_of_separating source span choice hsep,
    backward_triple_eq_bot source hb modules facts p initial bad hlarge span choice hsep,
    backward_commutator_le_Z source hb modules facts p initial bad hlarge span choice hsep,
    start_Z_le_backward_moving_sup_Z source hb modules facts p initial bad hlarge span choice hsep⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.SelectedSource
