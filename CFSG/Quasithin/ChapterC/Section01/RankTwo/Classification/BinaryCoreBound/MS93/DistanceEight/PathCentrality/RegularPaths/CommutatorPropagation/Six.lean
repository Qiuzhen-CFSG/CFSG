module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Assembly

/-!
# The fixed-core transport and the exclusion of critical distance six

The fixed-displacement case extends (4.4.1)(i) to every distance-two pair.
A regular turn can be chosen in the local residual, since the kernel fixes
the vertex two steps away. Thus D_c intersect D_d is carried into D_a when
a turn at c sends d to a. On a six-edge regular critical path, (4.4.1)(i)
at the two middle M-vertices places the critical commutator in both fixed
cores. The turn transports their intersection into D_a. This contradicts
the nonzero critical commutator's containment in the disjoint natural
summand U_a. Evenness and b > 4 therefore give b > 6.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1)--(4.4.3), printed pp.890--894.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}

/-- Include the fixed-displacement case in (4.4.1)(i). -/
theorem span_kernel_intersection_le_fixed (hb : 2 < geometry.b R)
    (hlocal : LocalCommutatorControl R) {a c : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) :
    ⁅localZSpan R a c, Q R a ⊓ Q R c⁆ ≤ fixedCore R c := by
  by_cases h : ⁅Z R a, Q R c⁆ ≤ fixedCore R c
  · exact (commutator_mono le_rfl inf_le_right).trans
      ((LocalCommutator.span_commutator_le_fixed_iff hc hd.le hb).mpr h)
  · exact (hlocal a c ha hc hd h).1

/-- A turn can be realized in the residual: Q_c fixes the target at distance two. -/
theorem exists_residual_turn [Finite M] (source : LocalSource L R)
    {a c d : Vertex R} (hc : color R c = false)
    (hca : (cosetGraph R).dist c a = 2)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hturn : Stellmacher.PushingUp.AmalgamGraph.act R g d = a) :
    ∃ l ∈ Ltilde R c, Stellmacher.PushingUp.AmalgamGraph.act R l d = a := by
  have hprod : g ∈ Ltilde R c ⊔ Q R c := (source.local_generation c hc).ge hg
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    ((Ltilde_le_stabilizer c).trans (Q_normalized R c))] at hprod
  obtain ⟨l, hl, q, hq, he⟩ := hprod
  have hqa : Stellmacher.PushingUp.AmalgamGraph.act R q⁻¹ a = a :=
    (stabilizer R a).inv_mem (Q_le_stabilizer_of_dist_two R c a hc hca hq)
  refine ⟨l, hl, ?_⟩
  have hh := congrArg (Stellmacher.PushingUp.AmalgamGraph.act R q⁻¹) hturn
  rw [← he, act_mul, ← act_mul, mul_inv_cancel, act_one, hqa] at hh
  exact hh

/-- The fixed-core intersection transported by a regular turn. -/
theorem fixedCore_intersection_le_of_turn [Finite M] (source : LocalSource L R)
    {a c d : Vertex R} (hc : color R c = false)
    (hca : (cosetGraph R).dist c a = 2)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hturn : Stellmacher.PushingUp.AmalgamGraph.act R g d = a) :
    fixedCore R c ⊓ fixedCore R d ≤ fixedCore R a := by
  obtain ⟨l, hl, he⟩ := exists_residual_turn source hc hca hg hturn
  intro x hx
  have hfix : (MulAut.conj l⁻¹) x = x := by
    have hh := hx.1.2 l⁻¹ ((Ltilde R c).inv_mem hl)
    change l⁻¹ * x * (l⁻¹)⁻¹ = x
    rw [hh, mul_inv_cancel_right]
  have hm := mem_map_of_mem (MulAut.conj l⁻¹).toMonoidHom hx.2
  rw [← Escape.EdgeTransfer.fixedCore_act, he] at hm
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hfix] using hm

/-- The critical commutator is nonzero in the natural summand, hence is not fixed. -/
theorem critical_commutator_not_le_fixed [Finite M]
    (common : CommonFacts R source geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') : ¬ ⁅Z R a, Z R a'⁆ ≤ fixedCore R a := by
  have hU : ⁅Z R a, Z R a'⁆ ≤ U R a := by
    rw [(naturalStructure common).critical_commutator_eq geometry a p.start_color a' p.critical]
    exact le_normalizer_iff_commutator_le_left.mp
      (source.critical_U_mutually_normalize geometry a p.start_color a' p.critical).2
  intro h
  apply common.critical_noncommutation a p.start_color a' p.critical
  apply le_bot_iff.mp
  rw [← Escape.EdgeTransfer.U_fixed_eq_bot (moduleFacts common) a p.start_color]
  exact le_inf hU (h.trans inf_le_right)

private theorem path_distance {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.walk.length) :
    (cosetGraph R).dist (p.walk.getVert i) (p.walk.getVert j) = j - i := by
  have hh := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk p.shortest (p.walk.isSubwalk_drop i))
    ((p.walk.drop i).isSubwalk_take (j - i))
  have hmin : j - i ≤ p.walk.length - i := Nat.sub_le_sub_right hj i
  simpa only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
    inf_eq_left.mpr hmin, SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij] using hh.symm

private theorem six_commutator_le_second_fixed
    (hlocal : LocalCommutatorControl R) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    (hsix : geometry.b R = 6) : ⁅Z R a, Z R a'⁆ ≤ fixedCore R (p.walk.getVert 2) := by
  have hlen : p.walk.length = 6 := p.length_eq_b.trans hsix
  have hc2 : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hc4 : color R (p.walk.getVert 4) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph R).dist (p.walk.getVert 4) (p.walk.getVert 2) = 2 := by
    rw [SimpleGraph.dist_comm, path_distance p (by decide) (by omega)]
  obtain ⟨g, hg, hturn⟩ := hp 2 (by decide) (by decide) (by omega)
  have hturn' : Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 4) = a := by
    simpa only [Nat.reduceAdd, Nat.reduceSub, SimpleGraph.Walk.getVert_zero] using hturn
  have hspan : Z R a ≤ localZSpan R (p.walk.getVert 4) (p.walk.getVert 2) := by
    have hh := le_iSup (fun g : stabilizer R (p.walk.getVert 2) =>
      Z R (Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 4))) ⟨g, hg⟩
    simpa only [hturn', localZSpan] using hh
  have hQ (i : ℕ) (hi : i = 2 ∨ i = 4) : Z R a' ≤ Q R (p.walk.getVert i) := by
    apply Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' p.end_color)
    rw [geometry.distance_constant a' p.end_color, SimpleGraph.dist_comm, p.dist_end i]
    change p.walk.length - i < geometry.b R
    rcases hi with rfl | rfl <;> omega
  exact (commutator_mono hspan (le_inf (hQ 4 (Or.inr rfl)) (hQ 2 (Or.inl rfl)))).trans
    (span_kernel_intersection_le_fixed (by rw [hsix]; decide) hlocal hc4 hc2 hd)

/-- MS93 (4.4.3): the critical distance of a regular path is greater than six. -/
theorem six_lt [Finite M] (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (hlocal : LocalCommutatorControl R)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (hp : HasTurnConjugators R p) : 6 < geometry.b R := by
  by_contra! hsmall
  have heven : Even (geometry.b R) := by
    exact geometry.even (alpha R) rfl
  have hsix : geometry.b R = 6 := by
    rw [Nat.even_iff] at heven
    omega
  have hlen : p.walk.length = 6 := p.length_eq_b.trans hsix
  have hfirst := six_commutator_le_second_fixed hlocal p hp hsix
  have hr : HasTurnConjugators R (p.reverse common) :=
    HasTurnConjugators.reverse (R := R) (geometry := geometry) (p := p) common hp
  have hsecond := six_commutator_le_second_fixed (R := R) (geometry := geometry)
    hlocal (p.reverse common) hr hsix
  have hsecond' : ⁅Z R a, Z R a'⁆ ≤ fixedCore R (p.walk.getVert 4) := by
    change ⁅Z R a', Z R a⁆ ≤ fixedCore R (p.walk.reverse.getVert 2) at hsecond
    simpa only [SimpleGraph.Walk.getVert_reverse, hlen, Nat.reduceSub,
      commutator_comm (Z R a') (Z R a)] using hsecond
  obtain ⟨g, hg, hturn⟩ := hp 2 (by decide) (by decide) (by omega)
  have hturn' : Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 4) = a := by
    simpa only [Nat.reduceAdd, Nat.reduceSub, SimpleGraph.Walk.getVert_zero] using hturn
  apply critical_commutator_not_le_fixed common p
  exact (le_inf hfirst hsecond').trans (fixedCore_intersection_le_of_turn source
    ((p.vertex_color (by omega)).mpr (by decide))
    (by rw [SimpleGraph.dist_comm, p.dist_start (by omega)]) hg hturn')

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation
