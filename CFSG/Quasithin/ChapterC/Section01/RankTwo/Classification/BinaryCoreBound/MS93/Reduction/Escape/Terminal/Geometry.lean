module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Reversal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball

/-!
# Critical selection and the radius-six kernel bound

Selection from a noncommuting radius span is valid at arbitrary width.
Normal products at moving neighbors then give the positive radius-six
containment: failure would move the sixth predecessor at the eighth,
forcing the already excluded radius-four containment.

Source: Meierfrankenfeld--Stellmacher (1993), first full paragraph on
printed p.890. All path vertices and relative normalities are retained.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Terminal
open Propagation Propagation.RadiusFour
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

omit [Finite M] in
theorem exists_critical_of_not_commuting {a l : Vertex R} {n : ℕ}
    (ha : color R a = false) (hl : color R l = false)
    (hnear : (cosetGraph R).dist a l + n ≤ geometry.b R)
    (hne : ⁅VBall R a n, Z R l⁆ ≠ ⊥) :
    ∃ x, ∃ hx : color R x = false,
      (cosetGraph R).dist x a = n ∧
      (cosetGraph R).dist a l + n = geometry.b R ∧
      CriticalPair R x l (geometry.exists_critical x hx) := by
  classical
  have hn : ¬ VBall R a n ≤ centralizer (Z R l : Set (FreeAmalgam R)) := by
    intro h
    exact hne (commutator_eq_bot_iff_le_centralizer.mpr h)
  obtain ⟨x, hx, hxa, hnot⟩ : ∃ x, color R x = false ∧
      (cosetGraph R).dist x a ≤ n ∧
      ¬ Z R x ≤ centralizer (Z R l : Set (FreeAmalgam R)) := by
    simpa only [Forward.VBall_le_iff ha, not_forall, exists_prop] using hn
  have hQ : ¬ Z R x ≤ Q R l := by
    intro h
    exact hnot (h.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes l hl))))
  have hmin := criticalDistance_le R x (geometry.exists_critical x hx) hQ
  rw [geometry.distance_constant x hx] at hmin
  change geometry.b R ≤ (cosetGraph R).dist x l at hmin
  have htri := (cosetGraph_connected R).dist_triangle (u := x) (v := a) (w := l)
  refine ⟨x, hx, by omega, by omega, ?_, hQ⟩
  rw [geometry.distance_constant x hx]
  change (cosetGraph R).dist x l = geometry.b R
  omega

omit [Finite M] in
/-- A ball inside the critical distance is contained in the endpoint stabilizer. -/
theorem ball_le_stabilizer {a l : Vertex R} {n : ℕ} (ha : color R a = false)
    (hnear : (cosetGraph R).dist a l + n ≤ geometry.b R) :
    VBall R a n ≤ stabilizer R l := by
  rw [Forward.VBall_le_iff ha]
  intro x hx hxa
  apply Z_le_stabilizer_of_dist_le x (geometry.exists_critical x hx)
  rw [geometry.distance_constant x hx]
  change (cosetGraph R).dist x l ≤ geometry.b R
  have ht := (cosetGraph_connected R).dist_triangle (u := x) (v := a) (w := l)
  omega

/-- A noncommuting layer at the edge n+1 selects a critical endpoint moving
at the predecessor n+2. The distances are literal shortest-path equations. -/
theorem moving_of_ball_noncommutation (source : LocalSource L R)
    (hb : 2 < geometry.b R) (p : Counterexample geometry)
    {n : ℕ} {t s l : Vertex R} (ht : Before p.a p.a' t (n + 1))
    (hs : Before p.a p.a' s (n + 2)) (hlt : Adjacent R l t)
    (hl : color R l = false) (hne : ⁅VBall R p.a n, Z R l⁆ ≠ ⊥) :
    l ∈ movingNeighbors geometry s := by
  have hpath := ht.2
  rw [p.distance_eq_b] at hpath
  have htl : (cosetGraph R).dist t l = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (adjacent_symm R hlt))
  have hnear : (cosetGraph R).dist p.a l + n ≤ geometry.b R := by
    have htri := (cosetGraph_connected R).dist_triangle (u := p.a) (v := t) (w := l)
    omega
  obtain ⟨x, hx, hxa, hal, hcrit⟩ := exists_critical_of_not_commuting p.color_a hl hnear hne
  apply Forward.Reversal.critical_endpoint_moving source hb hx hcrit
  have hst : (cosetGraph R).dist s t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (hs.adjacent (geometry := geometry) ht))
  have hsPath := hs.2
  rw [p.distance_eq_b] at hsPath
  have htri₁ := (cosetGraph_connected R).dist_triangle (u := s) (v := t) (w := l)
  have htri₂ := (cosetGraph_connected R).dist_triangle (u := p.a) (v := s) (w := l)
  have hsl : (cosetGraph R).dist s l = 2 := by omega
  have hxl : (cosetGraph R).dist x l = geometry.b R :=
    hcrit.1.trans (geometry.distance_constant x hx)
  have htri₃ := (cosetGraph_connected R).dist_triangle (u := x) (v := p.a) (w := s)
  have htri₄ := (cosetGraph_connected R).dist_triangle (u := x) (v := s) (w := l)
  exact ⟨hsl, by omega⟩

/-- The normal product at a moving neighbor traps its radius group at any
vertex satisfying the exact distance bound. -/
theorem moving_radius_le_Q (propagation : PropagationFacts geometry)
    (p : Counterexample geometry) {a d x : Vertex R} (ha : color R a = false)
    (hmove : d ∈ movingNeighbors geometry a)
    (hnear : (cosetGraph R).dist a x + 2 < geometry.b R) : V R d ≤ Q R x := by
  have hb := propagation.six_lt p
  obtain ⟨q, hqa⟩ := counterexample_at_vertex p (by omega) a ha
  have hsym := propagation.moving_symmetric q d
  rw [hqa] at hsym
  have hh := propagation.product_normal q d (by simpa only [hqa] using hmove.1)
    (by simpa only [hqa] using hsym.mp hmove)
  rw [hqa] at hh
  exact le_sup_left.trans (Forward.normal_product_le_Q ha (by omega) hmove.1 hh.1 hh.2.1 hnear)

omit [Finite M] in
/-- The even critical distance supplies the actual eighth predecessor. -/
theorem eight_le (propagation : PropagationFacts geometry) (p : Counterexample geometry) :
    8 ≤ geometry.b R := by
  have hlarge := propagation.six_lt p
  have heven := geometry.even p.a p.color_a
  rw [geometry.distance_constant p.a p.color_a] at heven
  change Even (geometry.b R) at heven
  rw [Nat.even_iff] at heven
  omega

/-- The positive radius-six containment on printed p.890. Its contrary case
would make the forbidden radius-four containment follow from a normal product. -/
theorem radius_six_le (source : LocalSource L R) (hb : 2 < geometry.b R)
    (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {s : Vertex R} (hs : Before p.a p.a' s 6) : VBall R p.a 6 ≤ Q R s := by
  by_contra hn
  have hlarge := eight_le propagation p
  obtain ⟨d, hd⟩ := p.exists_before (show 4 ≤ geometry.b R by omega)
  obtain ⟨t₅, h₅⟩ := p.exists_before (show 5 ≤ geometry.b R by omega)
  obtain ⟨t₇, h₇⟩ := p.exists_before (show 7 ≤ geometry.b R by omega)
  obtain ⟨e, he⟩ := p.exists_before hlarge
  have hsc : color R s = false := (hs.color (by decide)).trans p.end_color
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hec : color R e = false := (he.color (by decide)).trans p.end_color
  have hcomm : ⁅VBall R p.a 6, Z R s⁆ ≠ ⊥ := by
    intro hc
    apply hn
    rw [← source.C_eq_Q geometry.radical_ne_bot s hsc]
    exact le_inf (ball_le_stabilizer p.color_a (hs.2.trans p.distance_eq_b).le)
      (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hmove := moving_of_ball_noncommutation source hb p h₇ he
    (adjacent_symm R (h₇.adjacent (geometry := geometry) hs)) hsc hcomm
  have hdV : Z R d ≤ V R s := by
    apply le_iSup_of_le d
    refine le_iSup_of_le ?_ le_rfl
    have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := t₅) (w := s)
    have hdt := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (adjacent_symm R (h₅.adjacent (geometry := geometry) hd)))
    have hts := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (adjacent_symm R (hs.adjacent (geometry := geometry) h₅)))
    omega
  apply (propagation.radius_four p d hd).1
  rw [← source.C_eq_Q geometry.radical_ne_bot d hdc]
  apply le_inf (ball_le_stabilizer p.color_a (hd.2.trans p.distance_eq_b).le)
  rw [Forward.VBall_le_iff p.color_a]
  intro x hx hxa
  have hnear : (cosetGraph R).dist e x + 2 < geometry.b R := by
    have hpath := he.2
    rw [p.distance_eq_b] at hpath
    have htri := (cosetGraph_connected R).dist_triangle (u := e) (v := p.a) (w := x)
    rw [SimpleGraph.dist_comm (u := e) (v := p.a),
      SimpleGraph.dist_comm (u := p.a) (v := x)] at htri
    omega
  have hQ := moving_radius_le_Q propagation p hec hmove hnear
  exact le_centralizer_iff.mpr ((hdV.trans hQ).trans
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes x hx))))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Terminal