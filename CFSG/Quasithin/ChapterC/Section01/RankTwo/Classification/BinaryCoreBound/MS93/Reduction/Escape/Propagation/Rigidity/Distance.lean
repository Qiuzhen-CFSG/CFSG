module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Centrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FaithfulSection

/-!
# Excluding critical distance six using neighboring rigidity

Under the contrary escape configuration, the natural section is faithful
modulo the actual two-core. Hence R₀ cannot lie in Zα: that would make Zα′
centralize the moving natural section and put it in Qα, contradicting the
reversed critical pair. The omega-center description of Zα then excludes
centrality of R₀ at every vertex at distance two from α.

If b = 6, take α+2 and α+3 on the critical geodesic. Centrality of R₀ at
α′−2, independently proved from local control and edge transfer, preserves
R₀ under an actual local conjugator taking α′ to a neighbor δ of α+3.
The assumed neighboring equality gives Zδ = Zα+2. Thus R₀ lies in Uα+2,
whereas the nontrivial critical commutator R lies in the fixed core there.
Their intersection is trivial, a contradiction.

This proves (4.3.5) conditionally on the preceding inputs and the explicit
neighboring equality from (4.3.4). No later propagation or radius-four
conclusion is assumed.

Source: Meierfrankenfeld--Stellmacher, “Pushing up weak BN-pairs of rank two”
(1993), (4.3.5), printed p.886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
namespace Distance
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

include source in
/-- Faithfulness of the natural section excludes R₀ ≤ Zα. -/
theorem radius_not_le_start_Z (p : Counterexample geometry) (initial : InitialFacts p) :
    ¬ radiusCommutator p.a p.a' ≤ Z R p.a := by
  intro h
  apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
  have hcirc : Vcirc R p.a ≤ V R p.a :=
    le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer p.a).trans (V_normalized p.a))
  exact PairingControl.actor_le_Q source p.color_a initial.natural_section _
    p.end_Z_le_start_stabilizer ((commutator_mono hcirc le_rfl).trans h)

/-- Centrality two steps from α would place R₀ in Ω₁(Z(Qα)) = Zα. -/
theorem radius_not_le_localCenter (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (initial : InitialFacts p) (d : Vertex R)
    (hd : (cosetGraph R).dist p.a d = 2) :
    ¬ radiusCommutator p.a p.a' ≤ localCenter d := by
  intro h
  apply radius_not_le_start_Z (source := source) p initial
  rw [← modules.X_eq_Z p.a p.color_a]
  intro x hx
  have hxω : x ∈ omegaCenter (Q R p.a') := by
    change x ∈ X R p.a'
    rw [modules.X_eq_Z p.a' p.end_color]
    exact p.radius_le_end hx
  have hcentral := h hx
  rw [localCenter_eq] at hcentral
  exact mem_omegaCenter_iff.mpr
    ⟨(p.radius_le_start.trans (geometry.V_le_Q hb p.a p.color_a)) hx,
      (mem_omegaCenter_iff.mp hxω).2.1,
      fun y hy => hcentral.2 y (Q_le_stabilizer_of_dist_two R p.a d p.color_a hd hy)⟩

include source in
/-- A genuine Gα′−2-conjugate of α′ over α′−3 has edge displacement R₀. -/
theorem exists_conjugate_displacement (hb : 2 < geometry.b R)
    (p : Counterexample geometry) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (t : Vertex R) (ht : Before p.a p.a' t 3) :
    ∃ g ∈ stabilizer R p.c, Adjacent R (act R g p.a') t ∧
      radiusCommutator p.a p.a' = edgeDisplacement (act R g p.a') t := by
  obtain ⟨s, hs⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hcs := p.before.adjacent (geometry := geometry) hs
  have hct := adjacent_symm R (ht.adjacent (geometry := geometry) p.before)
  obtain ⟨g, hg, hgs⟩ := stabilizer_transitive_neighbors R p.c hcs hct
  refine ⟨g, hg, ?_, ?_⟩
  · rw [← hgs]
    exact (adjacent_act_iff R g _ _).mpr hs.endpoint_adjacent
  · have hmap := RadiusFour.map_eq_of_le_localCenter _ p.c
      (RadiusFour.radius_central_at_two source hb control edge p) g hg
    have heq : ⁅Z R p.a', Q R s⁆ = radiusCommutator p.a p.a' :=
      (initial.radius_eq_edge s hs).symm
    rw [← hgs, edgeDisplacement, Z_act, Q_act, ← map_commutator, heq, hmap]

end Distance

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

open Distance in
/-- MS93 (4.3.5), using the explicitly supplied neighboring equality (4.3.4). -/
theorem six_lt_of_equal_Z (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (_transfer : NormalizationTransfer R)
    (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (equal_Z : ∀ a t d : Vertex R, color R a = false → Adjacent R a t → Adjacent R d t →
      ¬ U R d ⊓ Z R a ≤ localCenter a → Z R d = Z R a) :
    6 < geometry.b R := by
  obtain ⟨hi⟩ := initial p
  by_contra! hle
  have h6 : geometry.b R = 6 := Nat.le_antisymm hle hi.six_le
  obtain ⟨d, hd⟩ := p.exists_before (show 4 ≤ geometry.b R by omega)
  obtain ⟨t, ht⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  have had : (cosetGraph R).dist p.a d = 2 := by
    have hh := hd.2
    rw [p.distance_eq_b, h6] at hh
    omega
  have hdcol : color R d = false := (hd.color (by decide)).trans p.end_color
  have hdt : Adjacent R d t := hd.adjacent (geometry := geometry) ht
  obtain ⟨g, hg, hδt, hRδ⟩ := exists_conjugate_displacement (source := source) hb p hi control edge t ht
  have hδcol : color R (act R g p.a') = false :=
    (action_preserves_color R g p.a').trans p.end_color
  have hRU : radiusCommutator p.a p.a' ≤ U R (act R g p.a') := by
    rw [hRδ]
    exact EdgeTransfer.edge_commutator_le_natural hb modules _ t hδcol hδt
  have hRZ : radiusCommutator p.a p.a' ≤ Z R d := by
    rw [hRδ]
    exact (edge_le_Z p hb control edge _ t hδcol hδt).trans
      (EdgeTransfer.edge_Z_le d t hdcol hdt)
  have hZδ : Z R (act R g p.a') = Z R d :=
    equal_Z d t _ hdcol hdt hδt (fun h =>
      radius_not_le_localCenter hb modules p hi d had ((le_inf hRU hRZ).trans h))
  have hRd : radiusCommutator p.a p.a' = edgeDisplacement d t := by
    simpa only [edgeDisplacement, hZδ] using hRδ
  have hUd : radiusCommutator p.a p.a' ≤ U R d := by
    rw [hRd]
    exact EdgeTransfer.edge_commutator_le_natural hb modules d t hdcol hdt
  have haV : Z R p.a ≤ V R d :=
    le_iSup_of_le p.a (le_iSup_of_le had.le le_rfl)
  have ha'Q : Z R p.a' ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R p.a' (geometry.exists_critical p.a' p.end_color)
    rw [geometry.distance_constant p.a' p.end_color, SimpleGraph.dist_comm, hd.1]
    change 4 < geometry.b R
    omega
  have hfixed : criticalCommutator p.a p.a' ≤ fixedCore R d :=
    (commutator_mono haV ha'Q).trans
      (commutator_le_fixed_at p (by omega) control d hdcol)
  apply source.critical_noncommutation geometry p.a p.color_a p.critical
  apply le_bot_iff.mp
  rw [← EdgeTransfer.U_fixed_eq_bot modules d hdcol]
  exact le_inf (p.critical_le_radius_inf_start.trans (inf_le_left.trans hUd))
    (hfixed.trans inf_le_right)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
