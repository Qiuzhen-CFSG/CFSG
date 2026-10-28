module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction

/-!
# The separating-choice source package for MS93 (4.3.2)(6)

Choose an actual backward edge whose displacement omits the critical
commutator line. For any such choice, failure of its literal P-conjugate span
bound selects an actual element of P. This relative normalizer fixes the
starting vertex and the edge displacement; inverse conjugation agrees with
the graph action on the backward radius. Thus the moved choice still
separates the original critical line.

Critical minimality constructs the R_4 witness with that exact choice, and
the lambda/mu construction retains the same radius witness. The proved
R_mu contradiction applies with its separation premise discharged. Together
with the constructed separating edge and the genuine plane-normalizer
generation theorem, this gives all three clauses below from source inputs.
Separation depends only on the edge, so the clauses apply to every moving
backward neighbor chosen at a separating edge.

This package is separate from the legacy universal `StepSixFacts`: it proves
span and generation for every separating choice, and does not assert either
universal conclusion for arbitrary `BackwardChoice`.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(6) and its local
generation consequence, printed p.885. The first R_4 support obstruction
uses Z_alpha, as in the corrected source assembly of Contradiction.lean.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- The source stage retains separation at the actual edge and works for every
moving backward neighbor at that edge. -/
structure SeparatingStepSixFacts (p : Counterexample geometry) : Prop where
  backward : ∃ choice : BackwardChoice p,
    ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge
  bound : ∀ choice : BackwardChoice p,
    (¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge) →
    ∀ d, Before p.a p.a' d 4 → choice.W ≤ Q R d
  generation : ∀ choice : BackwardChoice p,
    (¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge) →
    choice.P ⊔ Z R p.a' = stabilizer R p.a

namespace StepSix
variable [Finite M]

/-- The relative normalizer fixes the displacement, even when it moves the edge. -/
theorem conjugateChoice_edgeDisplacement (hb : 2 < geometry.b R)
    {p : Counterexample geometry} (choice : BackwardChoice p) (g : choice.P) :
    edgeDisplacement p.a (conjugateChoice hb choice g).edge =
      edgeDisplacement p.a choice.edge := by
  have hga : act R (g : FreeAmalgam R) p.a = p.a := g.property.1
  have he := FirstPairing.edgeDisplacement_act (g : FreeAmalgam R) p.a choice.edge
  rw [hga] at he
  change edgeDisplacement p.a (act R (g : FreeAmalgam R) choice.edge) = _
  rw [he]
  exact mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (edgeDisplacement p.a choice.edge : Set (FreeAmalgam R))).inv_mem
      g.property.2)

/-- The graph action agrees with the inverse conjugation used in the literal W. -/
theorem conjugateChoice_radius (hb : 2 < geometry.b R)
    {p : Counterexample geometry} (choice : BackwardChoice p) (g : choice.P) :
    V R (conjugateChoice hb choice g).back =
      NormalizerTransfer.rightConjugate (V R choice.back) (g : FreeAmalgam R) :=
  V_act R (g : FreeAmalgam R) choice.back

/-- The endpoint and critical commutator stay fixed in this normalizer action. -/
theorem conjugateChoice_critical_avoidance (hb : 2 < geometry.b R)
    {p : Counterexample geometry} (choice : BackwardChoice p) (g : choice.P)
    (hsep : ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge) :
    ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a (conjugateChoice hb choice g).edge := by
  rwa [conjugateChoice_edgeDisplacement hb choice g]

omit [Finite M] in
/-- Critical minimality supplies a radius witness with this exact backward choice. -/
theorem exists_radiusWitness_of_failed_radius_with_choice (p : Counterexample geometry)
    {d : Vertex R} (hd : Before p.a p.a' d 4) (choice : BackwardChoice p)
    (hbad : ¬ V R choice.back ≤ Q R d) :
    ∃ w : RadiusWitness p d, w.choice = choice := by
  classical
  have hc := moving_color p.color_a choice.moving
  obtain ⟨x, hxcol, hxb, hx⟩ : ∃ x, color R x = false ∧
      (cosetGraph R).dist x choice.back ≤ 2 ∧ ¬ Z R x ≤ Q R d := by
    by_contra! h
    exact hbad (V_le_of_m_ball hc _ h)
  have hmin := criticalDistance_le R x (geometry.exists_critical x hxcol) hx
  rw [geometry.distance_constant x hxcol] at hmin
  change geometry.b R ≤ _ at hmin
  have hpath := hd.2
  rw [p.distance_eq_b] at hpath
  have hba : (cosetGraph R).dist choice.back p.a = 2 := by
    rw [SimpleGraph.dist_comm]
    exact choice.moving.1
  have htri₁ := (cosetGraph_connected R).dist_triangle
    (u := choice.back) (v := p.a) (w := d)
  have htri₂ := (cosetGraph_connected R).dist_triangle
    (u := x) (v := choice.back) (w := d)
  have hxd : (cosetGraph R).dist x d = geometry.b R := by omega
  have hxb' : (cosetGraph R).dist x choice.back = 2 := by omega
  obtain ⟨t, hxt, hbt⟩ := exists_common_neighbor_of_dist_two R x choice.back hxb'
  have hcrit : CriticalPair R x d (geometry.exists_critical x hxcol) := by
    refine ⟨?_, hx⟩
    rw [geometry.distance_constant x hxcol]
    exact hxd
  exact ⟨⟨choice, t, x, hbt, hxt, hxcol, hxb', hcrit⟩, rfl⟩

/-- The lambda/mu construction retains the entire supplied radius witness. -/
theorem exists_escapingWitness_of_radius_with_radius (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {d : Vertex R} (hd : Before p.a p.a' d 4) (w : RadiusWitness p d) :
    ∃ e : EscapingWitness p d, e.toRadiusWitness = w := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  obtain ⟨lam, hlam, he⟩ := exists_avoiding_edge source hb modules facts hdc
    w.Rfour (w.Rfour_ne_bot source)
  obtain ⟨mu, hmu, hm⟩ := exists_moving_at_edge hb transfer p bad hdc hlam
  exact ⟨{
    toRadiusWitness := w
    lam := lam
    mu := mu
    lam_adjacent := hlam
    mu_adjacent := hmu
    mu_moving := hm
    escapes := he }, rfl⟩

/-- Failure of the fixed span selects an actual P-conjugate, preserving separation. -/
theorem exists_radiusWitness_of_failed_span_of_critical_avoidance
    (hb : 2 < geometry.b R) (p : Counterexample geometry)
    {d : Vertex R} (hd : Before p.a p.a' d 4) (choice : BackwardChoice p)
    (hsep : ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge)
    (hbad : ¬ choice.W ≤ Q R d) :
    ∃ g : choice.P, ∃ w : RadiusWitness p d,
      w.choice = conjugateChoice hb choice g ∧
      ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a w.choice.edge := by
  classical
  have hstart : V R p.a ≤ Q R d := by
    apply V_le_Q_of_distance p.color_a
    have hh := hd.2
    rw [p.distance_eq_b] at hh
    omega
  have hconj : ¬ NormalizerTransfer.conjugatesIn (V R choice.back) choice.P ≤ Q R d :=
    fun h => hbad (sup_le h hstart)
  obtain ⟨g, hg⟩ : ∃ g : choice.P,
      ¬ NormalizerTransfer.rightConjugate (V R choice.back) (g : FreeAmalgam R) ≤ Q R d := by
    simpa only [NormalizerTransfer.conjugatesIn, iSup_le_iff, not_forall] using hconj
  have hradius : ¬ V R (conjugateChoice hb choice g).back ≤ Q R d := by
    rwa [conjugateChoice_radius hb choice g]
  obtain ⟨w, hw⟩ := exists_radiusWitness_of_failed_radius_with_choice p hd
    (conjugateChoice hb choice g) hradius
  refine ⟨g, w, hw, ?_⟩
  rw [hw]
  exact conjugateChoice_critical_avoidance hb choice g hsep

/-- The complete P-conjugate span is bounded for every separating backward choice. -/
theorem span_bound_of_critical_avoidance (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (choice : BackwardChoice p)
    (hsep : ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge)
    {d : Vertex R} (hd : Before p.a p.a' d 4) : choice.W ≤ Q R d := by
  by_contra hbad
  obtain ⟨_, w, _, havoid⟩ := exists_radiusWitness_of_failed_span_of_critical_avoidance
    hb p hd choice hsep hbad
  obtain ⟨e, he⟩ := exists_escapingWitness_of_radius_with_radius
    source hb modules transfer facts p bad hd w
  have heavoid : ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a e.choice.edge := by
    rwa [he]
  exact escapingWitness_false_of_critical_avoidance
    source hb modules facts initial p bad hlarge hd e heavoid

end StepSix

/-- Source inputs alone produce a separating choice, and span and generation for
every such choice. The original centralizer choice is retained in the interface. -/
theorem step_six_separating [Finite M] (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (_selected : CentralizerChoice p) :
    SeparatingStepSixFacts p := by
  obtain ⟨choice, hsep, _⟩ := StepSix.exists_separating_generating_backwardChoice
    source hb modules transfer initial facts p bad
  exact ⟨⟨choice, hsep⟩,
    fun c hc _ hd => StepSix.span_bound_of_critical_avoidance
      source hb modules transfer initial facts p bad hlarge c hc hd,
    fun c hc => StepSix.backwardChoice_generation_of_separating
      source hb modules initial facts c hc⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
