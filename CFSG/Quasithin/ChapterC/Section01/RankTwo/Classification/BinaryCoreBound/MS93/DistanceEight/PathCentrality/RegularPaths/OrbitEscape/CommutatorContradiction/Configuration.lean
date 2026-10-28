module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.BackwardChain
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Bounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inequality

/-!
# The actual subgroups in the second MS93 orbit-escape argument

Reuse the constructed backward critical chain and its neighbor conjugator.
Critical minimality places Vδ inside Gₐ, while source (4.3) makes its image
modulo Qₐ nontrivial. The backward kernel bound puts R₁ in Uδ. Both R₁ and
R₂ centralize the abelian Vδ. The critical commutator of order two lies in
R₂, and its actual distance-two displacement bounds R₂ by four.

These are inputs to the printed R₁/R₂ calculation. In particular neither
R₁'s nontriviality, the binary index, nor R₂'s noncontainment in ZδDδ is
asserted here. The order-four helper leaves its noncontainment premise explicit.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, second subgroup argument.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- The already constructed backward chain, neighbor conjugator, and reverse-span bound.
No index or commutator identity is a field of this configuration. -/
structure Configuration {a a' : Vertex R} (p : CriticalPath R geometry a a') where
  chain : BackwardChain p ((p.walk.length - 2) / 2)
  g : FreeAmalgam R
  mem_stabilizer : g ∈ stabilizer R a
  turn : act R g (p.walk.getVert 1) = chain.path.walk.getVert (p.walk.length - 3)
  reverseSpan_le : localZSpan R a (p.walk.getVert 2) ≤ Q R (chain.path.walk.getVert 2)

/-- Joint normality supplies this configuration through the existing backward construction. -/
theorem exists_configuration [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) : Nonempty (Configuration p) := by
  obtain ⟨c, g, hg, ht, hQ⟩ := exists_backward_configuration common p hb hnorm
  exact ⟨⟨c, g, hg, ht, hQ⟩⟩

namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}
  (s : Configuration p) (hb : 4 < geometry.b R)

/-- The printed delta is the first vertex of the retained critical path. -/
def delta : Vertex R := s.chain.first
/-- The actual right-action conjugate of a+2. -/
def conjugateSecond : Vertex R := act R s.g (p.walk.getVert 2)
/-- The literal subgroup R₁ = [V₁ᵍ,Zδ], using inverse conjugation for the right action. -/
noncomputable def firstCommutator : Subgroup (FreeAmalgam R) :=
  ⁅(localZSpan R a (p.walk.getVert 2)).map (MulAut.conj s.g⁻¹).toMonoidHom, Z R s.delta⁆
/-- The literal subgroup R₂ = [Z_(a+2),Vδ intersect Qₐ]. -/
noncomputable def secondCommutator : Subgroup (FreeAmalgam R) :=
  ⁅Z R (p.walk.getVert 2), V R s.delta ⊓ Q R a⁆

theorem delta_color : color R s.delta = false := s.chain.path.start_color

include hb

theorem start_vertex : s.chain.path.walk.getVert (p.walk.length - 2) = a := by
  have h := s.chain.start_vertex
  rwa [terminal_length p (by omega)] at h

theorem end_vertex : s.chain.last = p.walk.getVert 2 := by
  rw [s.chain.endpoint_eq, terminal_length p (by omega)]
  congr 1
  have hl := p.length_eq_b
  omega

theorem distance_start : (cosetGraph R).dist s.delta a = geometry.b R - 2 := by
  have h := s.chain.path.dist_start
    (i := p.walk.length - 2) (by rw [s.chain.path.length_eq_b, p.length_eq_b]; omega)
  rw [s.start_vertex hb] at h
  exact h.trans (congrArg (fun n => n - 2) p.length_eq_b)

theorem distance_second : (cosetGraph R).dist s.delta (p.walk.getVert 2) = geometry.b R := by
  rw [← s.end_vertex hb]
  exact s.chain.path.shortest.symm.trans s.chain.path.length_eq_b

theorem backward_critical : CriticalPair R s.delta (p.walk.getVert 2)
    (geometry.exists_critical _ s.delta_color) := by
  rw [← s.end_vertex hb]
  exact s.chain.path.critical

/-- Source (4.3) at the backward critical pair gives the nontrivial image at a. -/
theorem radius_not_le_start_kernel {source : LocalSource L R}
    (common : CommonFacts R source geometry) : ¬ V R s.delta ≤ Q R a := by
  apply common.escape s.delta s.delta_color (p.walk.getVert 2) (s.backward_critical hb) a
  · exact p.dist_start (by have hl := p.length_eq_b; omega)
  · rw [s.distance_start hb, s.distance_second hb]
    omega

theorem radius_le_start_stabilizer : V R s.delta ≤ stabilizer R a := by
  apply (V_le_iff R s.delta_color _).mpr
  intro d hd hdist
  apply Z_le_stabilizer_of_dist_le d (geometry.exists_critical d hd)
  rw [geometry.distance_constant d hd]
  change (cosetGraph R).dist d a ≤ geometry.b R
  have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := s.delta) (w := a)
  rw [s.distance_start hb] at ht
  omega

theorem radius_elementary : IsElementaryAbelian 2 (V R s.delta) :=
  V_elementary_of_four_lt R s.delta_color hb

theorem start_commutator_ne_bot [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) : ⁅Z R a, V R s.delta⁆ ≠ ⊥ := by
  intro h
  apply s.radius_not_le_start_kernel hb common
  rw [← common.natural.centralizer a p.start_color]
  apply le_inf (s.radius_le_start_stabilizer hb)
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)).trans
    (centralizer_le (MS93.U_le_Z a))

theorem delta_Z_le_start_kernel : Z R s.delta ≤ Q R a := by
  apply Z_le_Q_of_dist_lt R s.delta (geometry.exists_critical _ s.delta_color)
  rw [geometry.distance_constant _ s.delta_color, s.distance_start hb]
  change geometry.b R - 2 < geometry.b R
  omega

theorem conjugate_span_le_backward_kernel :
    (localZSpan R a (p.walk.getVert 2)).map (MulAut.conj s.g⁻¹).toMonoidHom ≤
      Q R (s.chain.path.walk.getVert 2) := by
  have hspan := localZSpan_le_V R (p.dist_start
    (by have hl := p.length_eq_b; omega)).le
  have hm := map_mono (f := (MulAut.conj s.g⁻¹).toMonoidHom) hspan
  rw [← V_act] at hm
  exact hm.trans (le_sup_right.trans (s.chain.radius_bound hb s.turn))

theorem conjugate_span_le_delta_stabilizer [Finite M] :
    (localZSpan R a (p.walk.getVert 2)).map (MulAut.conj s.g⁻¹).toMonoidHom ≤
      stabilizer R s.delta := by
  have hd : (cosetGraph R).dist s.delta (s.chain.path.walk.getVert 2) = 2 :=
    s.chain.path.dist_start (by have hl := s.chain.path.length_eq_b; omega)
  have hc : color R (s.chain.path.walk.getVert 2) = false :=
    (s.chain.path.vertex_color (by have hl := s.chain.path.length_eq_b; omega)).mpr
      (by decide)
  exact (s.conjugate_span_le_backward_kernel hb).trans
    (Q_le_stabilizer_of_dist_two R _ _ hc (by rw [SimpleGraph.dist_comm, hd]))

/-- Locality at delta puts R₁ in its genuine natural summand. -/
theorem firstCommutator_le_delta_natural [Finite M] (source : LocalSource L R) :
    s.firstCommutator ≤ U R s.delta := by
  unfold firstCommutator
  rw [commutator_comm]
  exact (commutator_mono le_rfl (s.conjugate_span_le_delta_stabilizer hb)).trans_eq
    (Escape.Initial.Z_commutator_stabilizer source s.delta s.delta_color)

theorem firstCommutator_centralizes_radius [Finite M] (source : LocalSource L R) :
    ⁅s.firstCommutator, V R s.delta⁆ = ⊥ := by
  let := s.radius_elementary hb
  apply commutator_eq_bot_iff_le_centralizer.mpr
  have hv : V R s.delta ≤ centralizer (V R s.delta : Set (FreeAmalgam R)) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact ((s.firstCommutator_le_delta_natural hb source).trans
    ((MS93.U_le_Z _).trans (Z_le_VBall R _ 2))).trans hv

theorem second_Z_le_delta_stabilizer [Finite M] :
    Z R (p.walk.getVert 2) ≤ stabilizer R s.delta := by
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hl := p.length_eq_b; omega)).mpr (by decide)
  apply Z_le_stabilizer_of_dist_le _ (geometry.exists_critical _ hc)
  rw [geometry.distance_constant _ hc, SimpleGraph.dist_comm, s.distance_second hb]
  exact le_rfl

theorem secondCommutator_le_radius [Finite M] : s.secondCommutator ≤ V R s.delta := by
  exact (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp
      ((s.second_Z_le_delta_stabilizer hb).trans (MS93.V_normalized s.delta)))

theorem secondCommutator_centralizes_radius [Finite M] :
    ⁅s.secondCommutator, V R s.delta⁆ = ⊥ := by
  let := s.radius_elementary hb
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((s.secondCommutator_le_radius hb).trans
      (le_centralizer_iff_isMulCommutative.mpr inferInstance))

theorem critical_commutator_le_secondCommutator :
    ⁅Z R (p.walk.getVert 2), Z R s.delta⁆ ≤ s.secondCommutator :=
  commutator_mono le_rfl (le_inf (Z_le_VBall R _ 2) (s.delta_Z_le_start_kernel hb))

theorem critical_commutator_card [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) :
    Nat.card (⁅Z R (p.walk.getVert 2), Z R s.delta⁆ : Subgroup (FreeAmalgam R)) = 2 := by
  have h := LocalCommutator.CriticalCase.critical_commutator_card common s.chain.path
  rw [s.end_vertex hb, commutator_comm] at h
  exact h

theorem secondCommutator_ne_bot {source : LocalSource L R}
    (common : CommonFacts R source geometry) : s.secondCommutator ≠ ⊥ := by
  intro h
  have hz := le_bot_iff.mp (h ▸ s.critical_commutator_le_secondCommutator hb)
  rw [commutator_comm] at hz
  exact common.critical_noncommutation s.delta s.delta_color _ (s.backward_critical hb) hz

theorem secondCommutator_le_second_natural [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) : s.secondCommutator ≤ U R (p.walk.getVert 2) := by
  apply (commutator_mono le_rfl inf_le_right).trans
  apply LocalCommutator.displacement_le_U common
  · exact (p.vertex_color (by have hl := p.length_eq_b; omega)).mpr (by decide)
  · rw [SimpleGraph.dist_comm, p.dist_start (by have hl := p.length_eq_b; omega)]

theorem secondCommutator_card_le_four [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) : Nat.card s.secondCommutator ≤ 4 := by
  have hc : color R (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hl := p.length_eq_b; omega)).mpr (by decide)
  have hd : (cosetGraph R).dist (p.walk.getVert 2) a = 2 := by
    rw [SimpleGraph.dist_comm, p.dist_start (by have hl := p.length_eq_b; omega)]
  have he := LocalCommutator.displacement_le_U common hc hd
  let := finite_stabilizer R (p.walk.getVert 2)
  let : Finite (⁅Z R (p.walk.getVert 2), Q R a⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (he.trans ((MS93.U_le_Z _).trans (Z_le_stabilizer R _))))
      (inclusion_injective _)
  exact (Nat.card_le_card_of_injective (inclusion (commutator_mono le_rfl
    (show V R s.delta ⊓ Q R a ≤ Q R a from inf_le_right)))
      (inclusion_injective _)).trans (LocalCommutator.displacement_card_le_four common hc hd)

theorem critical_commutator_le_delta_Z [Finite M] :
    ⁅Z R (p.walk.getVert 2), Z R s.delta⁆ ≤ Z R s.delta :=
  le_normalizer_iff_commutator_le_right.mp
    ((s.second_Z_le_delta_stabilizer hb).trans (Z_normalized R _))

/-- If R₂ escapes Zδ, its critical line and the displacement bound force order four.
The source noncontainment is still an explicit premise of this helper. -/
theorem secondCommutator_card_four_of_not_le_delta_Z [Finite M]
    {source : LocalSource L R} (common : CommonFacts R source geometry)
    (hn : ¬ s.secondCommutator ≤ Z R s.delta) : Nat.card s.secondCommutator = 4 := by
  let := finite_stabilizer R s.delta
  let : Finite s.secondCommutator := Finite.of_injective
    (inclusion ((s.secondCommutator_le_radius hb).trans
      (geometry.V_local s.delta s.delta_color (by
        rw [geometry.distance_constant _ s.delta_color]; exact common.large_distance))))
    (inclusion_injective _)
  have hc := s.critical_commutator_card hb common
  have hle := s.critical_commutator_le_secondCommutator hb
  have hdvd : 2 ∣ Nat.card s.secondCommutator := hc ▸ card_dvd_of_le hle
  have hpos : 0 < Nat.card s.secondCommutator := Nat.card_pos
  have hsmall := s.secondCommutator_card_le_four hb common
  have hne : Nat.card s.secondCommutator ≠ 2 := by
    intro htwo
    have heq := eq_of_le_of_card_ge hle (by rw [hc, htwo])
    exact hn (heq ▸ s.critical_commutator_le_delta_Z hb)
  omega

end Configuration

/-- Failed forward escape makes the forward span proper, by the supplied source (4.3). -/
theorem forwardSpan_lt_radius {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 4 < geometry.b R)
    (hforward : localZSpan R (p.walk.getVert 2) a ≤
      Q R (p.walk.getVert (p.walk.length - 2))) :
    localZSpan R (p.walk.getVert 2) a < V R a := by
  have hl := p.length_eq_b
  refine lt_of_le_of_ne (localZSpan_le_V R ?_) ?_
  · rw [SimpleGraph.dist_comm, p.dist_start (by omega)]
  · intro heq
    have hne := common.escape a p.start_color a' p.critical
      (p.walk.getVert (p.walk.length - 2))
      (by rw [p.dist_end]; omega)
      (by rw [p.dist_start (Nat.sub_le _ _), ← p.shortest]; omega)
    exact hne (heq ▸ hforward)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
