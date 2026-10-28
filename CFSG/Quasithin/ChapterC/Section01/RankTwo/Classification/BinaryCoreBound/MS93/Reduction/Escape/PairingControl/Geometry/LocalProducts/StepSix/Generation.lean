module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Choice

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Generation.Obstruction

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Generation.SeparatingChoice
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Generation.PlaneNormalizer

/-!
# A separating backward choice and its local generation

For an escaping backward displacement E, its commutator with the endpoint
Z-layer is exactly the critical commutator line R. Consequently that endpoint
normalizes E precisely when R lies in E. In that case the literal relative
normalizer P and the endpoint cannot generate the starting stabilizer.

The source-specific producer selects an actual edge omitting R, proves that
its order-four displacement escapes the endpoint kernel, and supplies a moving
backward neighbor. For every such separating choice, the full matrix
plane-stabilizer image of P and the nonnormalizing endpoint generate the
marked quotient. The contained local kernel lifts this to P joined with the
endpoint Z-layer equaling the starting stabilizer.

The older universal claim for every `BackwardChoice` remains unresolved;
`BackwardChoice` and the legacy stage interfaces are unchanged. In particular,
noncentrality alone is not substituted for separation. The matrix example in
Generation/Obstruction.lean and all the necessary-condition lemmas are retained.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.881,885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- Generation requires the critical commutator to escape the selected plane. -/
theorem backwardChoice_generation_requires_critical_avoidance
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    {q : Counterexample geometry} (choice : BackwardChoice q)
    (hgen : choice.P ⊔ Z R q.a' = stabilizer R q.a) :
    ¬ criticalCommutator q.a q.a' ≤ edgeDisplacement q.a choice.edge := by
  intro hcrit
  have hE : edgeDisplacement q.a choice.edge ≤ Z R q.a :=
    (Initial.edge_le_natural source _ _ q.color_a choice.adjacent_start).trans (U_le_Z _)
  have hJ : Z R q.a' ≤ normalizer (edgeDisplacement q.a choice.edge : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr ((commutator_mono hE le_rfl).trans hcrit)
  have hnorm : stabilizer R q.a ≤ normalizer (edgeDisplacement q.a choice.edge : Set (FreeAmalgam R)) := by
    rw [← hgen]
    exact sup_le inf_le_right hJ
  have hz := Selection.edge_normal_subgroup_eq_bot source hb modules facts
    q.color_a choice.adjacent_start _ le_rfl hnorm
  exact EdgeTransfer.edge_commutator_ne_bot modules _ _ q.color_a choice.adjacent_start hz

/-- The escaping plane has the same endpoint commutator as the full Z-layer. -/
theorem backwardChoice_endpoint_commutator
    (source : LocalSource L R) (modules : ModuleFacts source geometry)
    {q : Counterexample geometry} (initial : InitialFacts q) (choice : BackwardChoice q) :
    ⁅edgeDisplacement q.a choice.edge, Z R q.a'⁆ = criticalCommutator q.a q.a' := by
  have hE : edgeDisplacement q.a choice.edge ≤ Z R q.a :=
    (Initial.edge_le_natural source _ _ q.color_a choice.adjacent_start).trans (U_le_Z _)
  have hle : ⁅edgeDisplacement q.a choice.edge, Z R q.a'⁆ ≤ criticalCommutator q.a q.a' :=
    commutator_mono hE le_rfl
  have hne : ⁅edgeDisplacement q.a choice.edge, Z R q.a'⁆ ≠ ⊥ := by
    intro hz
    apply choice.escapes
    rw [← modules.natural.centralizer q.a' q.end_color]
    exact le_inf
      (hE.trans (source.critical_Z_le_stabilizer geometry q.a q.color_a q.a' q.critical).1)
      ((commutator_eq_bot_iff_le_centralizer.mp hz).trans (centralizer_le (U_le_Z _)))
  let := q.radius_finite
  let : Finite (criticalCommutator q.a q.a') := Finite.of_injective
    (inclusion (q.critical_le_radius_inf_start.trans inf_le_left)) (inclusion_injective _)
  let : Finite (⁅edgeDisplacement q.a choice.edge, Z R q.a'⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective _)
  apply eq_of_le_of_card_ge hle
  rw [initial.critical_card]
  exact (one_lt_card_iff_ne_bot _).mpr hne

/-- In this configuration normalization is equivalent to containing the critical line. -/
theorem backwardChoice_endpoint_normalizes_iff
    (source : LocalSource L R) (modules : ModuleFacts source geometry)
    {q : Counterexample geometry} (initial : InitialFacts q) (choice : BackwardChoice q) :
    Z R q.a' ≤ normalizer (edgeDisplacement q.a choice.edge : Set (FreeAmalgam R)) ↔
      criticalCommutator q.a q.a' ≤ edgeDisplacement q.a choice.edge := by
  rw [le_normalizer_iff_commutator_le_left,
    backwardChoice_endpoint_commutator source modules initial choice]

/-- The invariant-plane branch prevents the asserted generation equality. -/
theorem backwardChoice_not_generation_of_critical_le
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    {q : Counterexample geometry} (choice : BackwardChoice q)
    (hcrit : criticalCommutator q.a q.a' ≤ edgeDisplacement q.a choice.edge) :
    choice.P ⊔ Z R q.a' ≠ stabilizer R q.a :=
  fun hgen => backwardChoice_generation_requires_critical_avoidance
    source hb modules facts choice hgen hcrit

/-- Every backward choice avoiding the critical line generates locally. -/
theorem backwardChoice_generation_of_separating (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (facts : ContraryLocalFacts geometry) {q : Counterexample geometry}
    (choice : BackwardChoice q)
    (hsep : ¬ criticalCommutator q.a q.a' ≤ edgeDisplacement q.a choice.edge) :
    choice.P ⊔ Z R q.a' = stabilizer R q.a := by
  obtain ⟨o⟩ := facts.opposite q.a q.color_a
  apply PlaneNormalizer.generation_of_not_normalizing o _ _
    (Initial.edge_le_natural source _ _ q.color_a choice.adjacent_start)
    (Selection.Centralizer.Generation.edge_image_card source q (by omega) initial
      q.color_a choice.adjacent_start o) q.end_Z_le_start_stabilizer
  exact fun h => hsep ((backwardChoice_endpoint_normalizes_iff source modules
    (Classical.choice (initial q)) choice).mp h)

/-- Source selection and local generation, with all separation premises discharged. -/
theorem exists_separating_generating_backwardChoice (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (facts : ContraryLocalFacts geometry)
    (q : Counterexample geometry) (bad : ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a) :
    ∃ choice : BackwardChoice q,
      (¬ criticalCommutator q.a q.a' ≤ edgeDisplacement q.a choice.edge) ∧
      choice.P ⊔ Z R q.a' = stabilizer R q.a := by
  obtain ⟨choice, hsep⟩ := exists_separating_backwardChoice source hb modules transfer
    initial facts q bad
  exact ⟨choice, hsep, backwardChoice_generation_of_separating source hb modules
    initial facts choice hsep⟩


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
