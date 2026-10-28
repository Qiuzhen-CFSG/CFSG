module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Control
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Stages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Bounds

/-!
# Locality and the terminal contradiction for backward edge selection

Critical minimality puts the whole backward span inside G_(a'-4), even
when it does not lie in Q_(a'-4). Its commutator with Z_(a'-4) therefore
lies in the natural summand. That summand meets the actual local center
trivially, so a central commutator forces the span into the kernel.

A failed span bound, at a generating edge, also gives centrality of R_0
and hence of R by the contrapositive of (4.3.6). These are ingredients of
the two edge choices, not a construction of those choices.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.7)(i), pp.887--888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- The non-strict distance bound gives containment in the stabilizer,
including generators exactly at the critical distance. -/
theorem V_le_stabilizer_of_dist_add_two_le {a d : Vertex R}
    (ha : color R a = false)
    (hnear : (cosetGraph R).dist a d + 2 ≤ geometry.b R) :
    V R a ≤ stabilizer R d := by
  apply (V_le_iff ha _).mpr
  intro e he hea
  apply Z_le_stabilizer_of_dist_le e (geometry.exists_critical e he)
  rw [geometry.distance_constant e he]
  change (cosetGraph R).dist e d ≤ geometry.b R
  have htri := (cosetGraph_connected R).dist_triangle (u := e) (v := a) (w := d)
  omega

/-- Every W(t) is local at the vertex four before the endpoint; no kernel
containment or favorable choice is needed for this assertion. -/
theorem backwardSpan_le_before_stabilizer (p : Counterexample geometry)
    (d t : Vertex R) (hd : Before p.a p.a' d 4) :
    backwardSpan geometry p.a t ≤ stabilizer R d := by
  apply iSup_le
  intro e
  apply iSup_le
  intro _
  apply iSup_le
  intro hea
  have he : color R e = false :=
    (color_eq_of_dist_even R e p.a (hea.1.symm ▸ (by decide : Even 2))).trans p.color_a
  apply V_le_stabilizer_of_dist_add_two_le he
  have htri := (cosetGraph_connected R).dist_triangle (u := e) (v := p.a) (w := d)
  have hpath := hd.2
  rw [p.distance_eq_b] at hpath
  rw [hea.1] at htri
  omega

/-- This is the use of (4.3.6) after a generating edge fails its span bound. -/
theorem radius_le_center_of_failed_bound (bound : BoundFacts geometry)
    (p : Counterexample geometry) (d t : Vertex R) (hd : Before p.a p.a' d 4)
    (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a)
    (hbad : ¬ backwardSpan geometry p.a t ≤ Q R d) :
    radiusCommutator p.a p.a' ≤ localCenter d := by
  by_contra hn
  exact hbad ((bound.bound p d hd hn).2 t hat hgen)

variable [Finite M]

/-- The smaller critical commutator R is central whenever a generating
edge fails its backward-span bound. R and R_0 remain distinct groups. -/
theorem critical_le_center_of_failed_bound (bound : BoundFacts geometry)
    (p : Counterexample geometry) (d t : Vertex R) (hd : Before p.a p.a' d 4)
    (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a)
    (hbad : ¬ backwardSpan geometry p.a t ≤ Q R d) :
    criticalCommutator p.a p.a' ≤ localCenter d :=
  (p.critical_le_radius_inf_start.trans inf_le_left).trans
    (radius_le_center_of_failed_bound bound p d t hd hat hgen hbad)

/-- Locality places the commutator in the natural summand at its Z-end. -/
theorem local_commutator_le_natural (source : LocalSource L R)
    (d : Vertex R) (hd : color R d = false) (W : Subgroup (FreeAmalgam R))
    (hW : W ≤ stabilizer R d) : ⁅W, Z R d⁆ ≤ U R d := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl hW).trans (Initial.Z_commutator_stabilizer source d hd).le

/-- A central commutator with Z_d vanishes, since its natural summand has
no fixed points for G_d. The exact local centralizer then gives Q_d. -/
theorem le_Q_iff_commutator_le_center (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (d : Vertex R) (hd : color R d = false) (W : Subgroup (FreeAmalgam R))
    (hW : W ≤ stabilizer R d) :
    W ≤ Q R d ↔ ⁅W, Z R d⁆ ≤ localCenter d := by
  constructor
  · intro h
    apply (commutator_mono h le_rfl).trans
    rw [commutator_comm, geometry.centralizes d hd]
    exact bot_le
  · intro hc
    have hzero : ⁅W, Z R d⁆ = ⊥ := by
      apply le_bot_iff.mp
      rw [← Rigidity.U_inf_localCenter_eq_bot modules d hd]
      exact le_inf (local_commutator_le_natural source d hd W hW) hc
    rw [← source.C_eq_Q geometry.radical_ne_bot d hd]
    exact le_inf hW (commutator_eq_bot_iff_le_centralizer.mp hzero)

/-- The last contradiction on printed p.888: a span escaping Q_(a'-4)
cannot have its Z_(a'-4)-commutator central in G_(a'-4). -/
theorem backwardSpan_commutator_not_le_center (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (d t : Vertex R) (hd : Before p.a p.a' d 4)
    (hbad : ¬ backwardSpan geometry p.a t ≤ Q R d) :
    ¬ ⁅backwardSpan geometry p.a t, Z R d⁆ ≤ localCenter d := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  exact fun hc => hbad ((le_Q_iff_commutator_le_center source modules d hdc _
    (backwardSpan_le_before_stabilizer p d t hd)).mpr hc)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products
