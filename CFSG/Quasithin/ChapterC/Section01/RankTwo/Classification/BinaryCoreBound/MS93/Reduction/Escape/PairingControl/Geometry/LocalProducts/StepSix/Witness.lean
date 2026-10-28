module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Choice
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Endpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Source

/-!
# The nontrivial R_4 configuration in MS93 (4.3.2)(6)

A failed P-conjugate span bound gives another actual backward choice, since
P fixes the starting vertex and normalizes the chosen edge displacement.
Critical minimality then selects alpha-3 and alpha-4 and the genuine critical
pair (alpha-4, alpha'-4). Its commutator R_4 is nontrivial. The intersection
argument selects lambda, and local transitivity selects the moving mu.

This constructs the configurations for the two R_mu branches; it does not
assume the step-(6) bound or identify a new critical pair with the old one.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(6), printed p.885.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- The normalizer moves both backward vertices, preserving the escaping group. -/
def conjugateChoice (hb : 2 < geometry.b R) {p : Counterexample geometry}
    (choice : BackwardChoice p) (g : choice.P) : BackwardChoice p where
  edge := act R (g : FreeAmalgam R) choice.edge
  back := act R (g : FreeAmalgam R) choice.back
  adjacent_start := by
    have hga : act R (g : FreeAmalgam R) p.a = p.a := g.property.1
    simpa only [hga] using
      (adjacent_act_iff R (g : FreeAmalgam R) p.a choice.edge).mpr choice.adjacent_start
  adjacent_back := (adjacent_act_iff R _ _ _).mpr choice.adjacent_back
  moving := by
    have hga : act R (g : FreeAmalgam R) p.a = p.a := g.property.1
    have h := (FirstPairing.movingNeighbors_act_iff hb (g : FreeAmalgam R)
      p.a choice.back p.color_a).mpr choice.moving
    rwa [hga] at h
  escapes := by
    have hga : act R (g : FreeAmalgam R) p.a = p.a := g.property.1
    have he := FirstPairing.edgeDisplacement_act (g : FreeAmalgam R) p.a choice.edge
    rw [hga] at he
    have hn : (edgeDisplacement p.a choice.edge).map
        (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom = edgeDisplacement p.a choice.edge :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (edgeDisplacement p.a choice.edge : Set (FreeAmalgam R))).inv_mem g.property.2)
    rw [he, hn]
    exact choice.escapes

/-- Bounding every backward radius bounds every conjugate in the literal W. -/
theorem span_bound_of_radius_bounds (hb : 2 < geometry.b R)
    (p : Counterexample geometry) {d : Vertex R} (hd : Before p.a p.a' d 4)
    (bounds : ∀ choice : BackwardChoice p, V R choice.back ≤ Q R d)
    (choice : BackwardChoice p) : choice.W ≤ Q R d := by
  apply sup_le
  · apply iSup_le
    intro g
    change (V R choice.back).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom ≤ _
    rw [← V_act]
    exact bounds (conjugateChoice hb choice g)
  · apply V_le_Q_of_distance p.color_a
    have hh := hd.2
    rw [p.distance_eq_b] at hh
    omega

/-- These are the literal alpha-3 and alpha-4 of the failed-bound argument. -/
structure RadiusWitness (p : Counterexample geometry) (d : Vertex R) where
  choice : BackwardChoice p
  third : Vertex R
  fourth : Vertex R
  back_adjacent : Adjacent R choice.back third
  fourth_adjacent : Adjacent R fourth third
  fourth_color : color R fourth = false
  fourth_back_distance : (cosetGraph R).dist fourth choice.back = 2
  critical : CriticalPair R fourth d (geometry.exists_critical fourth fourth_color)

omit [Finite M] in
/-- A failed radius bound supplies exact distance b, not just a noncentral pair. -/
theorem radiusWitness_of_failed_radius (p : Counterexample geometry)
    {d : Vertex R} (hd : Before p.a p.a' d 4) (choice : BackwardChoice p)
    (hbad : ¬ V R choice.back ≤ Q R d) : Nonempty (RadiusWitness p d) := by
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
  refine ⟨⟨choice, t, x, hbt, hxt, hxcol, hxb', ?_, hx⟩⟩
  rw [geometry.distance_constant x hxcol]
  exact hxd

theorem radiusWitness_of_failed_span (hb : 2 < geometry.b R)
    (p : Counterexample geometry) {d : Vertex R} (hd : Before p.a p.a' d 4)
    (choice : BackwardChoice p) (hbad : ¬ choice.W ≤ Q R d) :
    Nonempty (RadiusWitness p d) := by
  classical
  obtain ⟨other, ho⟩ : ∃ other : BackwardChoice p, ¬ V R other.back ≤ Q R d := by
    by_contra! h
    exact hbad (span_bound_of_radius_bounds hb p hd h choice)
  exact radiusWitness_of_failed_radius p hd other ho

namespace RadiusWitness
variable {p : Counterexample geometry} {d : Vertex R} (w : RadiusWitness p d)

/-- The R_4 in the printed proof. -/
noncomputable def Rfour : Subgroup (FreeAmalgam R) := ⁅Z R w.fourth, Z R d⁆

theorem Rfour_ne_bot (source : LocalSource L R) : w.Rfour ≠ ⊥ :=
  source.critical_noncommutation geometry w.fourth w.fourth_color w.critical

omit [Finite M] in
theorem back_color : color R w.choice.back = false := moving_color p.color_a w.choice.moving

omit [Finite M] in
theorem back_before (hd : Before p.a p.a' d 4) :
    Before w.fourth d w.choice.back (geometry.b R - 2) := by
  have hc : (cosetGraph R).dist w.fourth d = geometry.b R :=
    w.critical.1.trans (geometry.distance_constant _ w.fourth_color)
  have hb : (cosetGraph R).dist w.choice.back p.a = 2 := by
    rw [SimpleGraph.dist_comm]
    exact w.choice.moving.1
  have hp := hd.2
  rw [p.distance_eq_b] at hp
  have h₁ := (cosetGraph_connected R).dist_triangle
    (u := w.fourth) (v := w.choice.back) (w := d)
  have h₂ := (cosetGraph_connected R).dist_triangle
    (u := w.choice.back) (v := p.a) (w := d)
  have hf := w.fourth_back_distance
  constructor <;> omega

omit [Finite M] in
theorem fourth_start_distance (hd : Before p.a p.a' d 4) :
    (cosetGraph R).dist w.fourth p.a = 4 := by
  have hc : (cosetGraph R).dist w.fourth d = geometry.b R :=
    w.critical.1.trans (geometry.distance_constant _ w.fourth_color)
  have hb : (cosetGraph R).dist w.choice.back p.a = 2 := by
    rw [SimpleGraph.dist_comm]
    exact w.choice.moving.1
  have hp := hd.2
  rw [p.distance_eq_b] at hp
  have h₁ := (cosetGraph_connected R).dist_triangle
    (u := w.fourth) (v := w.choice.back) (w := p.a)
  have h₂ := (cosetGraph_connected R).dist_triangle
    (u := w.fourth) (v := p.a) (w := d)
  have hf := w.fourth_back_distance
  omega

theorem Rfour_le_naturals (source : LocalSource L R)
    (modules : ModuleFacts source geometry) : w.Rfour ≤ U R w.fourth ⊓ U R d := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  obtain ⟨hx, hd⟩ := source.critical_Z_le_stabilizer geometry w.fourth w.fourth_color d w.critical
  change ⁅Z R w.fourth, Z R d⁆ ≤ _
  rw [s.critical_commutator_eq geometry w.fourth w.fourth_color d w.critical]
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp ((U_le_Z d).trans (hd.trans (U_normalized _))))
    (le_normalizer_iff_commutator_le_right.mp ((U_le_Z w.fourth).trans (hx.trans (U_normalized _))))

/-- The edge supplement removes the fixed edge layer from the R_4 commutator. -/
theorem Rfour_le_backward_natural (source : LocalSource L R)
    (facts : ContraryLocalFacts geometry) (hd : Before p.a p.a' d 4) :
    w.Rfour ≤ U R w.choice.back := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hpath := hd.2
  rw [p.distance_eq_b] at hpath
  have hbd : (cosetGraph R).dist w.choice.back d + 2 ≤ geometry.b R := by
    have htri := (cosetGraph_connected R).dist_triangle
      (u := w.choice.back) (v := p.a) (w := d)
    have hba : (cosetGraph R).dist w.choice.back p.a = 2 := by
      rw [SimpleGraph.dist_comm]
      exact w.choice.moving.1
    omega
  have hZd : Z R d ≤ Q R w.choice.back := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdc)
    rw [geometry.distance_constant d hdc, SimpleGraph.dist_comm]
    change (cosetGraph R).dist w.choice.back d < geometry.b R
    omega
  have hlocal : V R w.choice.back ≤ stabilizer R d :=
    V_le_stabilizer_of_distance w.back_color hbd
  have hcentral : V R w.choice.edge ≤ centralizer (Z R d : Set (FreeAmalgam R)) := by
    apply V_le_of_h_neighbors p.color_a w.choice.adjacent_start
    intro u hu
    have huc : color R u = false := by
      have h₁ := adjacent_color_ne R w.choice.adjacent_start
      have h₂ := adjacent_color_ne R hu
      rw [p.color_a] at h₁
      cases ht : color R w.choice.edge <;> cases hc : color R u <;> simp_all
    have hdu : Z R d ≤ Q R u := by
      apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdc)
      rw [geometry.distance_constant d hdc]
      change (cosetGraph R).dist d u < geometry.b R
      have h₁ := (cosetGraph_connected R).dist_triangle
        (u := d) (v := p.a) (w := w.choice.edge)
      have h₂ := (cosetGraph_connected R).dist_triangle
        (u := d) (v := w.choice.edge) (w := u)
      rw [SimpleGraph.dist_comm (u := d) (v := p.a),
        SimpleGraph.dist_eq_one_iff_adj.mpr
          ((cosetGraph_adj R _ _).mpr w.choice.adjacent_start)] at h₁
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj R _ _).mpr (adjacent_symm R hu))] at h₂
      omega
    exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes u huc)).trans
      (centralizer_le hdu)
  have heq : ⁅Z R d, Vcirc R w.choice.back⁆ = ⁅Z R d, V R w.choice.back⁆ :=
    commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (radius_eq_moving_sup_edge source w.back_color
        w.choice.adjacent_back).symm) hcentral
      ((Vcirc_le_V _).trans (hlocal.trans (Z_normalized R d)))
  have hZ : Z R w.fourth ≤ V R w.choice.back :=
    le_iSup_of_le w.fourth (le_iSup_of_le w.fourth_back_distance.le le_rfl)
  change ⁅Z R w.fourth, Z R d⁆ ≤ _
  apply (commutator_mono hZ le_rfl).trans
  rw [commutator_comm, ← heq, commutator_comm, ← facts.H_eq_U _ w.back_color]
  exact commutator_mono le_rfl hZd

theorem Rfour_centralizes_endpoint (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (hlarge : 6 < geometry.b R)
    (hd : Before p.a p.a' d 4) :
    w.Rfour ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)) := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hQ : U R d ≤ Q R p.a' := by
    apply (U_le_Z d).trans
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdc)
    rw [geometry.distance_constant d hdc, hd.1]
    change 4 < geometry.b R
    omega
  exact ((w.Rfour_le_naturals source modules).trans (inf_le_right.trans hQ)).trans
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes p.a' p.end_color)))

end RadiusWitness

/-- The literal lambda and mu, retaining the R_4 witness and its backward choice. -/
structure EscapingWitness (p : Counterexample geometry) (d : Vertex R)
    extends RadiusWitness p d where
  lam : Vertex R
  mu : Vertex R
  lam_adjacent : Adjacent R d lam
  mu_adjacent : Adjacent R mu lam
  mu_moving : mu ∈ movingNeighbors geometry d
  escapes : ¬ toRadiusWitness.Rfour ≤ edgeDisplacement d lam

theorem escapingWitness_of_radius (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {d : Vertex R} (hd : Before p.a p.a' d 4) (w : RadiusWitness p d) :
    Nonempty (EscapingWitness p d) := by
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
    escapes := he }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
