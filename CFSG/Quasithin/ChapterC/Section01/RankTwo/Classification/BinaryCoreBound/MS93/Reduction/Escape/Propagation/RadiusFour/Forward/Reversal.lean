module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Stages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Bound.Commutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Basic

/-!
# Local algebra for the reversed critical configuration

The radius commutator intersects the starting local center trivially. Every
member of this intersection has square one and centralizes the starting kernel,
hence lies in its Z-layer. The established identity R₀ ∩ Z_alpha = R puts it
in the starting natural summand, which has no local central fixed points.

For any critical pair, its endpoint moves at the second predecessor. If its
Z-layer lay in the genuine quotient-fixed B, the join with the predecessor's
Z-layer would be normalized by the local stabilizer. Conjugating the last
edge towards the start puts both generators strictly inside the critical
distance, contradicting the reversed critical pair. The previously proved
geodesic calculation identifies the selected sixth predecessor with this
second predecessor, for the exact supplied orbit witness.

These arguments construct both fields of Forward.ReversalFacts from the
preceding source and module inputs. The movement proof extends the argument
in Backward.Radius.endpoint_moving to a critical pair without imposing
its contrary radius containment. No forward commutation is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.3.8), first paragraph of printed p.889; the preceding
R₀ ∩ Z_alpha calculation is used in (4.3.6), printed p.887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward.Reversal
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The local center meets R₀ trivially, by the actual omega-center and
critical-commutator intersections. -/
theorem radius_disjoint (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (initial : InitialFacts p) :
    radiusCommutator p.a p.a' ⊓ localCenter p.a = ⊥ := by
  have hZ : radiusCommutator p.a p.a' ⊓ localCenter p.a ≤ Z R p.a := by
    rintro x ⟨hx, hc⟩
    have hxω : x ∈ omegaCenter (Q R p.a') := by
      change x ∈ X R p.a'
      rw [modules.X_eq_Z p.a' p.end_color]
      exact p.radius_le_end hx
    rw [localCenter_eq] at hc
    rw [← modules.X_eq_Z p.a p.color_a]
    exact mem_omegaCenter_iff.mpr ⟨Initial.radius_le_start_kernel p hb hx,
      (mem_omegaCenter_iff.mp hxω).2.1, fun y hy => hc.2 y hy.1⟩
  have hR : radiusCommutator p.a p.a' ⊓ localCenter p.a ≤
      criticalCommutator p.a p.a' := by
    rw [← Backward.radius_inf_start_Z source p initial]
    exact le_inf inf_le_left hZ
  have hU : criticalCommutator p.a p.a' ≤ U R p.a :=
    (commutator_mono le_rfl p.end_Z_le_start_stabilizer).trans
      (Initial.Z_commutator_stabilizer source p.a p.color_a).le
  apply le_bot_iff.mp
  rw [← Rigidity.U_inf_localCenter_eq_bot modules p.a p.color_a]
  exact le_inf (hR.trans hU) inf_le_right

/-- A critical endpoint is moving at its second predecessor:
nonmovement would give a locally invariant Z-join inside the starting kernel. -/
theorem critical_endpoint_moving (source : LocalSource L R) (hb : 2 < geometry.b R)
    {a l s : Vertex R} (ha : color R a = false)
    (hcrit : CriticalPair R a l (geometry.exists_critical a ha))
    (hs : Before a l s 2) : l ∈ movingNeighbors geometry s := by
  by_contra hn
  have hl : color R l = false := critical_endpoint_color R a ha _ hcrit
  have hsc : color R s = false := (hs.color (by decide)).trans hl
  have hal : (cosetGraph R).dist a l = geometry.b R :=
    hcrit.1.trans (geometry.distance_constant a ha)
  have hsa : (cosetGraph R).dist s a + 2 = geometry.b R := by
    rw [SimpleGraph.dist_comm]
    exact hs.2.trans hal
  have hnorm := Backward.Moving.nonmoving_Z_join_normalized source hb hsc hs.1 hn
  obtain ⟨t, hst, hlt⟩ := exists_common_neighbor_of_dist_two R s l hs.1
  obtain ⟨u, hsu, hua⟩ := exists_adjacent_dist_sub_one R s a (by omega)
  obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R s hst hsu
  have hlu : Adjacent R (act R g l) u := by
    rw [← hgt]
    exact (adjacent_act_iff R g l t).mpr hlt
  have hgs : act R g s = s := hg
  have hmap := mem_normalizer_iff_map_conj_eq.mp (hnorm ((stabilizer R s).inv_mem hg))
  change (Z R s ⊔ Z R l).map (MulAut.conj g⁻¹).toMonoidHom = Z R s ⊔ Z R l at hmap
  rw [Subgroup.map_sup, ← Z_act, ← Z_act, hgs] at hmap
  have hZs : Z R s ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R s (geometry.exists_critical s hsc)
    rw [geometry.distance_constant s hsc]
    change (cosetGraph R).dist s a < geometry.b R
    omega
  have hZg : Z R (act R g l) ≤ Q R a := by
    have hcol : color R (act R g l) = false :=
      (action_preserves_color R g l).trans hl
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hcol)
    rw [geometry.distance_constant _ hcol]
    change (cosetGraph R).dist (act R g l) a < geometry.b R
    have htri := (cosetGraph_connected R).dist_triangle (u := act R g l) (v := u) (w := a)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hlu)] at htri
    omega
  have hjoin : Z R s ⊔ Z R l ≤ Q R a := hmap ▸ sup_le hZs hZg
  exact (source.critical_reverse geometry a ha l hl hcrit).2 (le_sup_right.trans hjoin)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward.Reversal

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Both local-algebra conclusions of the reversal stage, with all earlier
inputs discharged except the explicitly supplied source, module and initial
facts. The selected movement retains the exact orbit witness and critical pair. -/
theorem reversalFacts (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p)) :
    ReversalFacts geometry where
  radius_disjoint p := by
    obtain ⟨hi⟩ := initial p
    exact Reversal.radius_disjoint source hb modules p hi
  selected_moving p _d _t₃ _t₅ _s _hd _h₃ h₅ hs w x hx hcrit hxa hal :=
    Reversal.critical_endpoint_moving source hb hx hcrit
      (selected_six_before p h₅ hs w hx hcrit hxa hal)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward
