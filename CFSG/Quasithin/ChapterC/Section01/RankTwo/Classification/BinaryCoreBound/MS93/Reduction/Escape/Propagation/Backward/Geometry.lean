module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Stages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Geometry of the backward span in MS93 (4.3.6)

Only M-colored vertices are needed to generate a radius-two group. Critical
minimality then bounds nearby radius groups and turns a failed backward-span
containment into an actual critical pair. Covariance retains the reverse
condition in W(t), so the edge stabilizer normalizes this precise span.

The elementary radius arguments are adapted from
DistanceEight/PathCentrality/Paths.lean, without its CommonFacts interface or
any escape theorem. Source: Meierfrankenfeld--Stellmacher (1993), (4.3.6),
printed pp.886--887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

include geometry in
/-- Two specified points on the geodesic have the difference of their
endpoint distances, rather than just a triangle-inequality upper bound. -/
theorem before_dist {a a' c d : Vertex R} {m n : ℕ}
    (hc : Before a a' c m) (hd : Before a a' d n) (hnm : n ≤ m) :
    (cosetGraph R).dist c d = m - n := by
  obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a a'
  have hm : m ≤ w.length := by have := hc.2; omega
  have hnm' : w.length - m ≤ w.length - n := by omega
  have hs := SimpleGraph.length_eq_dist_of_subwalk hw
    (((w.take (w.length - n)).isSubwalk_drop (w.length - m)).trans
      (w.isSubwalk_take (w.length - n)))
  simp only [SimpleGraph.Walk.drop_length, SimpleGraph.Walk.take_length,
    inf_eq_left.mpr (Nat.sub_le w.length n), SimpleGraph.Walk.take_getVert,
    inf_eq_right.mpr hnm'] at hs
  rw [hc.getVert (geometry := geometry) w hw, hd.getVert (geometry := geometry) w hw] at hs
  omega

/-- Odd-colored vertices in a radius-two ball add no generators. -/
theorem V_le_iff {a : Vertex R} (ha : color R a = false)
    (K : Subgroup (FreeAmalgam R)) :
    V R a ≤ K ↔ ∀ d, color R d = false →
      (cosetGraph R).dist d a ≤ 2 → Z R d ≤ K := by
  constructor
  · intro h d _ hd
    have hz : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le hd le_rfl)
    exact hz.trans h
  · intro h
    apply iSup_le
    intro d
    apply iSup_le
    intro hd
    by_cases hc : color R d = false
    · exact h d hc hd
    · obtain ⟨w, hw⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d a
      have hn : ¬ Even ((cosetGraph R).dist d a) := by
        rw [← hw, walk_even_iff_color_eq, ha]
        exact hc
      rw [Nat.even_iff] at hn
      have hd' : (cosetGraph R).dist d a = 1 := by omega
      have hadj : Adjacent R a d := adjacent_symm R
        ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hd'))
      exact (EdgeTransfer.edge_Z_le a d ha hadj).trans (h a ha (by simp))

/-- The radius-two bound uses strict critical minimality at each generator. -/
theorem V_le_Q_of_dist_add_two_lt {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c + 2 < geometry.b R) : V R a ≤ Q R c := by
  apply (V_le_iff ha _).mpr
  intro d hdc hda
  apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdc)
  rw [geometry.distance_constant d hdc]
  change (cosetGraph R).dist d c < geometry.b R
  have htri : (cosetGraph R).dist d c ≤
      (cosetGraph R).dist d a + (cosetGraph R).dist a c :=
    (cosetGraph_connected R).dist_triangle
  omega

/-- A failed radius bound, at the critical distance minus two, selects a
genuine critical pair with its exact distance and M-color. -/
theorem exists_critical_of_not_V_le {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c + 2 ≤ geometry.b R)
    (he : ¬ V R a ≤ Q R c) :
    ∃ d, ∃ hdc : color R d = false, (cosetGraph R).dist d a = 2 ∧
      CriticalPair R d c (geometry.exists_critical d hdc) := by
  classical
  obtain ⟨d, hdc, hda, hn⟩ : ∃ d, color R d = false ∧
      (cosetGraph R).dist d a ≤ 2 ∧ ¬ Z R d ≤ Q R c := by
    simpa only [V_le_iff ha, not_forall, exists_prop] using he
  have hmin := criticalDistance_le R d (geometry.exists_critical d hdc) hn
  rw [geometry.distance_constant d hdc] at hmin
  change geometry.b R ≤ _ at hmin
  have htri : (cosetGraph R).dist d c ≤
      (cosetGraph R).dist d a + (cosetGraph R).dist a c :=
    (cosetGraph_connected R).dist_triangle
  refine ⟨d, hdc, by omega, ?_, hn⟩
  rw [geometry.distance_constant d hdc]
  change _ = geometry.b R
  omega

/-- A moving neighbor has the same color as its base vertex. -/
theorem moving_color {a d : Vertex R} (ha : color R a = false)
    (hd : d ∈ movingNeighbors geometry a) : color R d = false := by
  have he := color_eq_of_dist_even R a d (hd.1.symm ▸ (by decide : Even 2))
  exact he.symm.trans ha

/-- Any two radius-two generators commute if their distance is below b. -/
theorem V_commutative {a : Vertex R} (ha : color R a = false)
    (hb : 4 < geometry.b R) : IsMulCommutative (V R a) := by
  apply le_centralizer_iff_isMulCommutative.mp
  apply (V_le_iff ha _).mpr
  intro d hd hda
  apply le_centralizer_iff.mpr
  apply (V_le_iff ha _).mpr
  intro e he hea
  have hZ : Z R e ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R e (geometry.exists_critical e he)
    rw [geometry.distance_constant e he]
    change (cosetGraph R).dist e d < geometry.b R
    have htri : (cosetGraph R).dist e d ≤
        (cosetGraph R).dist e a + (cosetGraph R).dist a d :=
      (cosetGraph_connected R).dist_triangle
    rw [SimpleGraph.dist_comm (u := a) (v := d)] at htri
    omega
  exact hZ.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)))

/-- Two radius groups commute when every pair of their M-generators is
closer than the critical distance. -/
theorem V_le_centralizer_V {a d : Vertex R} (ha : color R a = false)
    (hd : color R d = false)
    (hnear : (cosetGraph R).dist a d + 4 < geometry.b R) :
    V R a ≤ centralizer (V R d : Set (FreeAmalgam R)) := by
  apply (V_le_iff ha _).mpr
  intro x hx hxa
  apply le_centralizer_iff.mpr
  apply (V_le_iff hd _).mpr
  intro y hy hyd
  have hZ : Z R y ≤ Q R x := by
    apply Z_le_Q_of_dist_lt R y (geometry.exists_critical y hy)
    rw [geometry.distance_constant y hy]
    change (cosetGraph R).dist y x < geometry.b R
    have htri₁ := (cosetGraph_connected R).dist_triangle (u := y) (v := d) (w := x)
    have htri₂ := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := x)
    rw [SimpleGraph.dist_comm (u := d) (v := a),
      SimpleGraph.dist_comm (u := a) (v := x)] at htri₂
    omega
  exact hZ.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes x hx)))

/-- The generating radius group really occurs in W(t); the hypothesis is
the reverse moving condition from the printed definition. -/
theorem V_le_backwardSpan {a t d : Vertex R} (hdt : Adjacent R d t)
    (hmove : a ∈ movingNeighbors geometry d) :
    V R d ≤ backwardSpan geometry a t :=
  le_iSup_of_le d (le_iSup_of_le hdt (le_iSup_of_le hmove le_rfl))

/-- Before using any propagation result, W(t) already lies in Q at its
starting vertex when b > 4. -/
theorem backwardSpan_le_Q {a : Vertex R} (ha : color R a = false)
    (hb : 4 < geometry.b R) (t : Vertex R) :
    backwardSpan geometry a t ≤ Q R a := by
  apply iSup_le
  intro d
  apply iSup_le
  intro _
  apply iSup_le
  intro hd
  have hcol : color R d = false := by
    have he := color_eq_of_dist_even R d a (hd.1.symm ▸ (by decide : Even 2))
    exact he.trans ha
  exact V_le_Q_of_dist_add_two_lt hcol (by rw [hd.1]; exact hb)

/-- This is the distance argument [R₀,W(t)] = 1 in (4.3.6), proved first
for the whole starting radius group. -/
theorem backwardSpan_le_centralizer_V {a : Vertex R} (ha : color R a = false)
    (hb : 6 < geometry.b R) (t : Vertex R) :
    backwardSpan geometry a t ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  apply iSup_le
  intro d
  apply iSup_le
  intro _
  apply iSup_le
  intro hd
  have hcol : color R d = false :=
    (color_eq_of_dist_even R d a (hd.1.symm ▸ (by decide : Even 2))).trans ha
  exact V_le_centralizer_V hcol ha (by rw [hd.1]; exact hb)

/-- Select both backward vertices when W(t) fails its required bound.
The selected critical pair includes its noncontainment, not merely distance. -/
theorem exists_backward_critical (p : Counterexample geometry) (d t : Vertex R)
    (hd : Before p.a p.a' d 4) (hW : ¬ backwardSpan geometry p.a t ≤ Q R d) :
    ∃ e, Adjacent R e t ∧ p.a ∈ movingNeighbors geometry e ∧
      ∃ f, ∃ hf : color R f = false, (cosetGraph R).dist f e = 2 ∧
        CriticalPair R f d (geometry.exists_critical f hf) := by
  classical
  have hex : ∃ e, Adjacent R e t ∧ p.a ∈ movingNeighbors geometry e ∧
      ¬ V R e ≤ Q R d := by
    simpa only [backwardSpan, iSup_le_iff, not_forall, exists_prop] using hW
  obtain ⟨e, het, hea, he⟩ := hex
  have hecol : color R e = false :=
    (color_eq_of_dist_even R e p.a (hea.1.symm ▸ (by decide : Even 2))).trans p.color_a
  have hnear : (cosetGraph R).dist e d + 2 ≤ geometry.b R := by
    have htri := (cosetGraph_connected R).dist_triangle (u := e) (v := p.a) (w := d)
    have hpath := hd.2
    rw [p.distance_eq_b] at hpath
    rw [hea.1] at htri
    omega
  exact ⟨e, het, hea, exists_critical_of_not_V_le hecol hnear he⟩

/-- This proves the local containment part of (4.3.7)(i) independently
of the much stronger assertion of normality. -/
theorem product_le_Q {a d : Vertex R} (ha : color R a = false)
    (hb : 4 < geometry.b R) (hd : (cosetGraph R).dist a d = 2) :
    V R d ⊔ V R a ≤ Q R a := by
  have hcol : color R d = false :=
    (color_eq_of_dist_even R a d (hd.symm ▸ (by decide : Even 2))).symm.trans ha
  exact sup_le (V_le_Q_of_dist_add_two_lt hcol (by
    rw [SimpleGraph.dist_comm, hd]; exact hb))
    (V_le_Q_of_dist_add_two_lt ha (by simp only [SimpleGraph.dist_self]; omega))

variable [Finite M]

/-- The reverse-moving span is covariant under the actual amalgam action. -/
theorem backwardSpan_act (hb : 2 < geometry.b R) (g : FreeAmalgam R)
    (a t : Vertex R) (ha : color R a = false) :
    backwardSpan geometry (act R g a) (act R g t) =
      (backwardSpan geometry a t).map (MulAut.conj g⁻¹).toMonoidHom := by
  apply le_antisymm
  · apply iSup_le
    intro e
    apply iSup_le
    intro het
    apply iSup_le
    intro he
    let d := act R g⁻¹ e
    have hgd : act R g d = e := by simp [d, ← act_mul]
    have hdt : Adjacent R d t := by
      apply (adjacent_act_iff R g d t).mp
      rwa [hgd]
    have hcol : color R d = false := by
      have hae : color R (act R g a) = false := (action_preserves_color R g a).trans ha
      have hecol := color_eq_of_dist_even R e (act R g a)
        (he.1.symm ▸ (by decide : Even 2))
      exact (action_preserves_color R g⁻¹ e).trans (hecol.trans hae)
    have hmove : a ∈ movingNeighbors geometry d := by
      apply (PairingControl.FirstPairing.movingNeighbors_act_iff hb g d a hcol).mp
      rwa [hgd]
    rw [← hgd, V_act]
    exact map_mono (V_le_backwardSpan hdt hmove)
  · rw [backwardSpan, Subgroup.map_iSup]
    apply iSup_le
    intro d
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hdt
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hmove
    rw [← V_act]
    have hcol : color R d = false :=
      (color_eq_of_dist_even R d a (hmove.1.symm ▸ (by decide : Even 2))).trans ha
    exact V_le_backwardSpan ((adjacent_act_iff R g d t).mpr hdt)
      ((PairingControl.FirstPairing.movingNeighbors_act_iff hb g d a hcol).mpr hmove)

/-- Relative edge normalization of W(t), before adjoining the critical
endpoint group. No symmetry of movingNeighbors has been used. -/
theorem backwardSpan_normalized (hb : 2 < geometry.b R)
    (a t : Vertex R) (ha : color R a = false) :
    stabilizer R a ⊓ stabilizer R t ≤
      normalizer (backwardSpan geometry a t : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (backwardSpan geometry a t).map (MulAut.conj g).toMonoidHom =
    backwardSpan geometry a t
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg.1
  have hgt : act R g⁻¹ t = t := (stabilizer R t).inv_mem hg.2
  simpa only [hga, hgt, inv_inv] using (backwardSpan_act hb g⁻¹ a t ha).symm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
