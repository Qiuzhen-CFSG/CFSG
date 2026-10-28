module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.Backward
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Propagating the retained central intersection along chosen source shifts

If a subgroup of an edge omega-center centralizes the other generator of
a local stabilizer, it centralizes that stabilizer and belongs to every
adjacent edge omega-center. A second chosen generation transports this
centrality across the next vertex. The source conjugator then carries it
back to the initial vertex.

The conclusion deliberately retains the intersection with the full vertex
center. This is the central propagation used in MS93 (5.10), p.922, and
(5.11), pp.923--924. The nonbinary symplectic argument must control that
intersection; it may not replace it by the trivial group as in a split
binary moved layer.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
variable {M : Type*} [Group M] {R : Subgroup M}

private theorem central_fixed_map {G : Type*} [Group G] (H K : Subgroup G)
    (hHK : H ≤ centralizer (K : Set G)) {x : G} (hx : x ∈ K) :
    H.map (MulAut.conj x).toMonoidHom = H := by
  apply mem_normalizer_iff_map_conj_eq.mp
  exact Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hHK hx)

/-- The holomorph-colored seed is central in its literal neighborhood kernel. -/
theorem edge_seed_central {t : Vertex R} (ht : color R t = true) :
    Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
  intro z hz
  rw [Z,if_neg (by simp [ht])] at hz
  exact (mem_omegaCenter_iff.mp hz).2.2

/-- The actual generation clause turns edge-seed centrality into local
stabilizer centrality. -/
theorem centralizes_vertex_of_edge_seed_generation
    {a t e : Vertex R} (ht : color R t = true)
    (H : Subgroup (FreeAmalgam R)) (hHt : H ≤ Z R t)
    (hHe : H ≤ centralizer (Z R e : Set (FreeAmalgam R)))
    (hgen : stabilizer R a ≤ Q R t ⊔ Z R e) :
    H ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
  apply le_centralizer_iff.mp
  exact hgen.trans (sup_le
    (le_centralizer_iff.mp (hHt.trans (edge_seed_central ht)))
    (le_centralizer_iff.mp hHe))

variable [Finite M]

/-- A subgroup fixed by the whole local stabilizer lies in every neighboring
seed once it lies in one of them. -/
theorem central_seed_le_neighbor_seed {a t v : Vertex R}
    (hat : Adjacent R a t) (hav : Adjacent R a v)
    (H : Subgroup (FreeAmalgam R)) (hHt : H ≤ Z R t)
    (hHa : H ≤ centralizer (stabilizer R a : Set (FreeAmalgam R))) :
    H ≤ Z R v := by
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors R a hat hav
  rw [←hxt,Z_act,←central_fixed_map H (stabilizer R a) hHa
    ((stabilizer R a).inv_mem hx)]
  exact map_mono hHt

/-- Two successive source generating pairs and the literal chosen conjugator
put the retained edge intersection in the starting vertex center. -/
theorem central_intersection_propagates
    (H : Subgroup (FreeAmalgam R)) {a c d t v f g : Vertex R}
    (ht : color R t = true) (hct : Adjacent R c t) (hcv : Adjacent R c v)
    (hHt : H ≤ Z R t)
    (hHf : H ≤ centralizer (Z R f : Set (FreeAmalgam R)))
    (hHg : H ≤ centralizer (Z R g : Set (FreeAmalgam R)))
    (hgenC : stabilizer R c ≤ Q R t ⊔ Z R f)
    (hgenD : stabilizer R d ≤ Q R v ⊔ Z R g)
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R c) (hxa : act R x d = a) :
    H ≤ centralizer (stabilizer R c : Set (FreeAmalgam R)) ∧
    H ≤ centralizer (stabilizer R d : Set (FreeAmalgam R)) ∧
    H ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
  have hHC := centralizes_vertex_of_edge_seed_generation ht H hHt hHf hgenC
  have hHv := central_seed_le_neighbor_seed hct hcv H hHt hHC
  have hc : color R c = false := by
    have hn := adjacent_color_ne R hct
    cases he : color R c <;> simp_all
  have hv : color R v = true := by
    have hn := adjacent_color_ne R hcv
    cases he : color R v <;> simp_all
  have hHD := centralizes_vertex_of_edge_seed_generation hv H hHv hHg hgenD
  refine ⟨hHC,hHD,?_⟩
  rw [←hxa,stabilizer_act]
  have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hHD).trans
    (map_centralizer_le_centralizer_image _ _)
  rwa [central_fixed_map H (stabilizer R c) hHC ((stabilizer R c).inv_mem hx)] at hh

variable (geometry : Geometry R)

/-- At distance greater than four, every subgroup of a critical endpoint
seed centralizes the two nearby endpoint seeds needed for propagation. -/
theorem endpoint_seed_centralizes_nearby
    (hb : 4 < geometry.b R) {e f : Vertex R}
    (he : color R e = false) (hf : color R f = false)
    (hd : (cosetGraph R).dist e f ≤ 4) :
    Z R e ≤ centralizer (Z R f : Set (FreeAmalgam R)) := by
  have hQ : Z R e ≤ Q R f := Z_le_Q_of_dist_lt R e (geometry.exists_critical e he)
    (by rw [geometry.distance_constant e he]; exact lt_of_le_of_lt hd hb)
  exact hQ.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R f hf)))

/-- Actual source consumer: the critical commutator's first-edge intersection
propagates into all three full centers, without discarding its central part. -/
theorem critical_intersection_le_three_centers
    (hb : 4 < geometry.b R) {a e c d t v f g : Vertex R}
    (p : CriticalPath R geometry a e)
    (hct : Adjacent R c t) (hcv : Adjacent R c v)
    (ht : color R t = true)
    (hf : color R f = false) (hg : color R g = false)
    (hef : (cosetGraph R).dist e f ≤ 4) (heg : (cosetGraph R).dist e g ≤ 4)
    (hgenC : stabilizer R c ≤ Q R t ⊔ Z R f)
    (hgenD : stabilizer R d ≤ Q R v ⊔ Z R g)
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R c) (hxa : act R x d = a) :
    ⁅Z R a,Z R e⁆ ⊓ Z R t ≤
      centralizer (stabilizer R c : Set (FreeAmalgam R)) ⊓
      centralizer (stabilizer R d : Set (FreeAmalgam R)) ⊓
      centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
  have hZa : Z R a ≤ stabilizer R e := by
    have ha := p.start_color
    exact Z_le_stabilizer_of_dist_le a (geometry.exists_critical a ha)
      (by rw [p.critical.1])
  have hcomm : ⁅Z R a,Z R e⁆ ≤ Z R e :=
    le_normalizer_iff_commutator_le_right.mp (hZa.trans (Z_normalized R e))
  obtain ⟨hC,hD,hA⟩ := central_intersection_propagates
    (⁅Z R a,Z R e⁆ ⊓ Z R t) ht hct hcv inf_le_right
    ((inf_le_left.trans hcomm).trans
      (endpoint_seed_centralizes_nearby geometry hb p.end_color hf hef))
    ((inf_le_left.trans hcomm).trans
      (endpoint_seed_centralizes_nearby geometry hb p.end_color hg heg))
    hgenC hgenD x hx hxa
  exact le_inf (le_inf hC hD) hA

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
