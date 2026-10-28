module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Six
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball

/-!
# Radius escape along the original critical path

Repeated applications of (4.3) extend the starting endpoint by two edges
while moving the terminal endpoint backward. This proves escape of every
even-radius ball at its corresponding path vertex. Distance bounds show
that the actual failed-span commutator lies in V_a and centralizes each
ball used by the backward induction. The ball is centered at a, not a'.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.3) and the radius-group argument in (4.4.4), printed p.894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
open Escape.Propagation.RadiusFour
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

theorem path_distance {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.walk.length) :
    (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert j) = j - i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk p.shortest (p.walk.isSubwalk_drop i))
    ((p.walk.drop i).isSubwalk_take (j - i))
  have hmin : j - i ≤ p.walk.length - i := Nat.sub_le_sub_right hj i
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using hh.symm

theorem balls_commute {a : Vertex R} (ha : color R a = false)
    {m n : ℕ} (hmn : m + n < geometry.b R) :
    ⁅VBall R a m, VBall R a n⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply (Forward.VBall_le_iff ha _).mpr
  intro d hd hda
  apply le_centralizer_iff.mpr
  apply (Forward.VBall_le_iff ha _).mpr
  intro e he hea
  have hZ : Z R e ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R e (geometry.exists_critical e he)
    rw [geometry.distance_constant e he]
    change (cosetGraph R).dist e d < geometry.b R
    have htri := (cosetGraph_connected R).dist_triangle (u := e) (v := a) (w := d)
    rw [SimpleGraph.dist_comm (u := a) (v := d)] at htri
    omega
  exact hZ.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)))

theorem ball_escape (common : CommonFacts R source geometry)
    (n : ℕ) {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hn : 2 * n ≤ p.walk.length) :
    ¬ VBall R a (2 * n) ≤ Q R (p.walk.getVert (p.walk.length - 2 * n)) := by
  induction n generalizing a a' with
  | zero =>
      simpa only [Nat.mul_zero, Nat.sub_zero, SimpleGraph.Walk.getVert_length] using
        (fun h : VBall R a 0 ≤ Q R a' => p.critical.2 ((Z_le_VBall R a 0).trans h))
  | succ n ih =>
      obtain ⟨d, q, shifted, hq, hs⟩ := p.exists_shift common
      have hlen : shifted.walk.length = p.walk.length :=
        shifted.length_eq_b.trans p.length_eq_b.symm
      have hget (i : ℕ) (hi : i ≤ p.walk.length - 2) :
          shifted.walk.getVert (i + 2) = p.walk.getVert i := by
        rw [hs, SimpleGraph.Walk.getVert_append, hq, if_neg (by omega),
          Nat.add_sub_cancel, SimpleGraph.Walk.take_getVert, inf_eq_right.mpr hi]
      have hindex : shifted.walk.length - 2 * n = (p.walk.length - 2 * (n + 1)) + 2 := by
        omega
      have he := ih shifted (by omega)
      rw [hindex, hget _ (by omega)] at he
      intro h
      apply he
      apply le_trans (VBall_le_of_dist_add_le a d (2 * n) (2 * (n + 1)) ?_) h
      have hd := SimpleGraph.dist_le q
      rw [hq] at hd
      omega

theorem transportedSpan_le_radius {a a' : Vertex R}
    (p : CriticalPath R geometry a a') {g : FreeAmalgam R}
    (hg : g ∈ stabilizer R a) (hb : 2 ≤ geometry.b R) :
    (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤ V R a := by
  have hspan : prescribedSpan p ≤ V R a := by
    apply iSup_le
    intro u
    have hu : Stellmacher.PushingUp.AmalgamGraph.act R u a = a := u.property.1
    have hd : (cosetGraph R).dist
        (Stellmacher.PushingUp.AmalgamGraph.act R u (p.walk.getVert 2)) a ≤ 2 := by
      have hh := dist_act R (u : FreeAmalgam R) (p.walk.getVert 2) a
      rw [hu] at hh
      calc
        _ = (cosetGraph R).dist (p.walk.getVert 2) a := hh
        _ ≤ 2 := by
          rw [SimpleGraph.dist_comm, p.dist_start (by rw [p.length_eq_b]; exact hb)]
    exact le_iSup_of_le _ (le_iSup_of_le hd le_rfl)
  have hga : Stellmacher.PushingUp.AmalgamGraph.act R g a = a := hg
  have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hspan
  rwa [← V_act, hga] at hm

theorem failedSpanCommutator_le_radius {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (common : CommonFacts R source geometry)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a) :
    failedSpanCommutator p g ≤ V R a := by
  have hspan := transportedSpan_le_radius p hg (by have := common.large_distance; omega)
  have hlocal := p.endpoint_Z_le_start_stabilizer (by have := common.large_distance; omega)
  apply (commutator_mono hspan le_rfl).trans
  exact le_normalizer_iff_commutator_le_left.mp
    (hlocal.trans (VBall_normalized a 2))

theorem failedSpanCommutator_centralizes_ball {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (common : CommonFacts R source geometry)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    {n : ℕ} (hn : n + 2 < geometry.b R) :
    ⁅failedSpanCommutator p g, VBall R a n⁆ = ⊥ := by
  apply le_bot_iff.mp
  exact (commutator_mono (failedSpanCommutator_le_radius p common hg) le_rfl).trans_eq
    (balls_commute p.start_color (by omega : 2 + n < geometry.b R))

/-- A radius group is in every kernel whose distance plus its radius is below b. -/
theorem ball_le_Q_of_dist_add_lt {a c : Vertex R} (ha : color R a = false)
    {n : ℕ} (hd : (cosetGraph R).dist a c + n < geometry.b R) :
    VBall R a n ≤ Q R c := by
  apply (Forward.VBall_le_iff ha _).mpr
  intro d hdcol hda
  apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdcol)
  rw [geometry.distance_constant d hdcol]
  change (cosetGraph R).dist d c < geometry.b R
  have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := c)
  omega

/-- The actual ball used to switch an edge: it centralizes R₀, escapes Q at
that vertex, and lies in the kernel of its backward neighbor. The center
is the original starting vertex a, as on printed p.894. -/
theorem switching_ball_facts (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    {j : ℕ} (heven : Even j) (hj : 4 ≤ j) (hlen : j ≤ p.walk.length) :
    ⁅failedSpanCommutator p g, VBall R a (p.walk.length - j)⁆ = ⊥ ∧
      (¬ VBall R a (p.walk.length - j) ≤ Q R (p.walk.getVert j)) ∧
      VBall R a (p.walk.length - j) ≤ Q R (p.walk.getVert (j - 1)) := by
  have hlen' := p.length_eq_b
  have hlenEven : Even p.walk.length := by
    rw [hlen']
    exact geometry.even (alpha R) rfl
  refine ⟨failedSpanCommutator_centralizes_ball p common hg (by omega), ?_, ?_⟩
  · have he : 2 * ((p.walk.length - j) / 2) = p.walk.length - j := by
      rw [Nat.even_iff] at heven hlenEven
      omega
    have hn := ball_escape common ((p.walk.length - j) / 2) p (by omega)
    rwa [he, Nat.sub_sub_self hlen] at hn
  · apply ball_le_Q_of_dist_add_lt p.start_color
    rw [p.dist_start (by omega)]
    omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration
