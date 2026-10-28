module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry

/-!
# Conjugate selection and the last initial edge identity

The moving subgroup at the specified predecessor escapes the starting kernel.
For every moving neighbor d there, moving generation therefore selects an
actual local conjugate of Z_d escaping that kernel. Critical minimality and
the triangle inequality make it a new critical endpoint, retaining the
original start, predecessor and trapped radius. The uniform order-four
hypothesis bounds its commutator from below. Conjugation then gives the same
bound for [Z_d,Q_c]. The earlier edge upper bound turns containment into the
exact equality of source (4.3.1)(vii).

Source: Meierfrankenfeld--Stellmacher (1993), p.883. No later pairing or
escape conclusion is used.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Consequences
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

omit [Finite M] in
theorem moving_color {a d : Vertex R} (ha : color R a = false)
    (hd : d ∈ movingNeighbors geometry a) : color R d = false :=
  (color_eq_of_dist_even R a d (hd.1.symm ▸ (by decide : Even 2))).symm.trans ha

/-- The new endpoint is an explicit local conjugate; the initial vertex,
predecessor and contrary containment are those of p. -/
theorem exists_critical_conjugate (source : LocalSource L R)
    (hb : 2 < geometry.b R) (p : Counterexample geometry)
    (hsections : ∀ q : Counterexample geometry, Nonempty (SectionFacts q))
    (d : Vertex R) (hd : d ∈ movingNeighbors geometry p.c) :
    ∃ g : FreeAmalgam R, g ∈ stabilizer R p.c ∧
      ∃ q : Counterexample geometry,
        q.a = p.a ∧ q.a' = act R g d ∧ q.c = p.c := by
  classical
  have hgen := moving_generation_at p hsections p.c p.before_color d hd
  have hout := endpoint_moving_not_le source p hb
  obtain ⟨g, hg, hnot⟩ : ∃ g ∈ stabilizer R p.c, ¬ Z R (act R g d) ≤ Q R p.a := by
    by_contra! h
    apply hout
    apply hgen.trans
    apply iSup_le
    intro g
    change (Z R d).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom ≤ Q R p.a
    rw [← Z_act]
    exact h g g.property
  have hfix : act R g p.c = p.c := hg
  have hdc : color R d = false := moving_color p.before_color hd
  have hgc : color R (act R g d) = false := by rwa [action_preserves_color]
  have hdist : (cosetGraph R).dist p.c (act R g d) = 2 := by
    rw [← hfix, dist_act]
    exact hd.1
  have hmin := criticalDistance_le R (act R g d) (geometry.exists_critical _ hgc) hnot
  rw [geometry.distance_constant _ hgc] at hmin
  change geometry.b R ≤ _ at hmin
  have htri := (cosetGraph_connected R).dist_triangle
    (u := p.a) (v := p.c) (w := act R g d)
  have hpath := p.before.2
  rw [p.distance_eq_b] at hpath
  have hreverse : CriticalPair R (act R g d) p.a (geometry.exists_critical _ hgc) := by
    refine ⟨?_, hnot⟩
    rw [geometry.distance_constant _ hgc]
    change _ = geometry.b R
    rw [SimpleGraph.dist_comm]
    rw [SimpleGraph.dist_comm] at hmin
    omega
  have hcrit := source.critical_reverse geometry (act R g d) hgc p.a p.color_a hreverse
  refine ⟨g, hg, {
    a := p.a
    a' := act R g d
    c := p.c
    color_a := p.color_a
    critical := hcrit
    before := ⟨hdist, ?_⟩
    trapped := p.trapped
  }, rfl, rfl, rfl⟩
  rw [hcrit.1, geometry.distance_constant p.a p.color_a]
  exact hpath

/-- Order four propagates to every moving neighbor at the actual predecessor. -/
theorem predecessor_moving_commutator_card (source : LocalSource L R)
    (hb : 2 < geometry.b R) (p : Counterexample geometry)
    (hfour : ∀ q : Counterexample geometry, Nat.card (radiusCommutator q.a q.a') = 4)
    (hsections : ∀ q : Counterexample geometry, Nonempty (SectionFacts q))
    (d : Vertex R) (hd : d ∈ movingNeighbors geometry p.c) :
    4 ≤ Nat.card (⁅Z R d, Q R p.c⁆ : Subgroup (FreeAmalgam R)) := by
  obtain ⟨g, hg, q, hqa, hqe, _⟩ := exists_critical_conjugate source hb p hsections d hd
  have hlocal : Q R p.c ≤ stabilizer R d :=
    Q_le_stabilizer_of_dist_two R p.c d p.before_color hd.1
  have hcZ : ⁅Q R p.c, Z R d⁆ ≤ Z R d :=
    le_normalizer_iff_commutator_le_right.mp (hlocal.trans (Z_normalized R d))
  let := finite_stabilizer R d
  let : Finite (⁅Q R p.c, Z R d⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (hcZ.trans (Z_le_stabilizer R d))) (inclusion_injective _)
  have hfix : act R g p.c = p.c := hg
  have hmap : ⁅Q R p.c, Z R (act R g d)⁆ =
      (⁅Q R p.c, Z R d⁆).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [map_commutator, ← Q_act, ← Z_act, hfix]
  have hcard : Nat.card (⁅Q R p.c, Z R (act R g d)⁆ : Subgroup (FreeAmalgam R)) =
      Nat.card (⁅Q R p.c, Z R d⁆ : Subgroup (FreeAmalgam R)) := by
    rw [hmap, card_map_of_injective (MulAut.conj g⁻¹).injective]
  let : Finite (⁅Q R p.c, Z R (act R g d)⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have hle : radiusCommutator q.a q.a' ≤ ⁅Q R p.c, Z R (act R g d)⁆ := by
    rw [radiusCommutator, hqa, hqe]
    exact commutator_mono p.trapped le_rfl
  have hh := card_le_of_le hle
  rw [hfour q, hcard, commutator_comm] at hh
  exact hh

/-- The uniform hypotheses apply to a translated configuration whose specified
predecessor is a. The moving neighbor d remains the prescribed vertex. -/
theorem moving_commutator_card (source : LocalSource L R)
    (hb : 2 < geometry.b R) (p : Counterexample geometry)
    (hfour : ∀ q : Counterexample geometry, Nat.card (radiusCommutator q.a q.a') = 4)
    (hsections : ∀ q : Counterexample geometry, Nonempty (SectionFacts q))
    (a : Vertex R) (ha : color R a = false)
    (d : Vertex R) (hd : d ∈ movingNeighbors geometry a) :
    4 ≤ Nat.card (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) := by
  obtain ⟨q, hqc⟩ := counterexample_at_predecessor p a ha
  subst a
  exact predecessor_moving_commutator_card source hb q hfour hsections d hd

/-- Source (4.3.1)(vii), at any prescribed incident moving neighbor. -/
theorem moving_commutator_eq_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (hfour : ∀ q : Counterexample geometry, Nat.card (radiusCommutator q.a q.a') = 4)
    (hsections : ∀ q : Counterexample geometry, Nonempty (SectionFacts q))
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hd : d ∈ movingNeighbors geometry a) :
    ⁅Z R d, Q R a⁆ = edgeDisplacement d t := by
  have ht : color R t = true := by
    have hne := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hdc := moving_color ha hd
  have hle : ⁅Z R d, Q R a⁆ ≤ edgeDisplacement d t :=
    commutator_mono le_rfl (Q_le_adjacent_h R ht hat)
  let := finite_stabilizer R d
  let : Finite (edgeDisplacement d t) := Finite.of_injective
    (inclusion ((edge_le_natural source d t hdc hdt).trans
      ((U_le_Z d).trans (Z_le_stabilizer R d)))) (inclusion_injective _)
  exact eq_of_le_of_card_ge hle ((edge_card_le_four source hb modules d t hdc hdt).trans
    (moving_commutator_card source hb p hfour hsections a ha d hd))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Consequences
