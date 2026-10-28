module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Basic

/-!
# Local commutators in the binary distance-two argument

A critical pair at distance two has a common edge vertex. Its commutator
[Q_alpha,Z_alpha'] lies in the elementary abelian endpoint layer Z_alpha',
so all its elements square to one. Consequently the source identity saying
that its M-conjugates generate the core implies involution generation of the
core, without assuming that the core itself is abelian.

The edge group contains the core. A relative centralizer index in that edge
group therefore bounds the centralizer in the core of any element in the
controlled commutator subgroup. Conjugate generation and the non-Frattini
hypothesis supply such an element outside U, once the edge index bound is
known. Every index uses the actual subgroup carrier in the free amalgam;
the ambient amalgam is never assumed finite.

These are reductions for the local estimates: the conjugate-generation
identity and the binary edge index bound remain explicit hypotheses.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the natural SL3 branch of (3.6), printed pp.870--871.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore

variable {M : Type*} [Group M] {R : Subgroup M}

/-- Choose a genuine critical endpoint and its common edge vertex at distance two. -/
theorem critical_edge_exists [Finite M] (geometry : Geometry R)
    (hb : geometry.b R = 2) :
    ∃ a' t, CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl) ∧
      Adjacent R (alpha R) t ∧ Adjacent R a' t := by
  obtain ⟨a', hc⟩ := criticalPair_exists R (alpha R)
    (geometry.exists_critical (alpha R) rfl)
  have hd : (cosetGraph R).dist (alpha R) a' = 2 := hc.1.trans hb
  obtain ⟨t, hat, ha't⟩ := exists_common_neighbor_of_dist_two R (alpha R) a' hd
  exact ⟨a', t, hc, hat, ha't⟩

/-- The neighbor of the distinguished M-vertex is a holomorph vertex. -/
theorem edge_color {t : Vertex R} (hat : Adjacent R (alpha R) t) :
    color R t = true := by
  have hn := adjacent_color_ne R hat
  change false ≠ color R t at hn
  cases ht : color R t <;> simp_all

/-- The commutator core lies in the actual kernel at every adjacent edge vertex. -/
theorem core_le_edge [Finite M] {t : Vertex R}
    (hat : Adjacent R (alpha R) t) : core R (alpha R) ≤ Q R t :=
  (core_le_Q (alpha R)).trans (Q_le_adjacent_h R (edge_color hat) hat)

/-- Along a two-edge path, Q_alpha fixes the other endpoint. -/
theorem Q_le_endpoint_stabilizer [Finite M] {a' t : Vertex R}
    (hat : Adjacent R (alpha R) t) (ha't : Adjacent R a' t) :
    Q R (alpha R) ≤ stabilizer R a' := by
  intro q hq
  exact (Q_le_adjacent_h R (edge_color hat) hat hq).2 a' (adjacent_symm R ha't)

/-- The local commutator lies in Z_alpha', since Q_alpha normalizes that layer. -/
theorem local_commutator_le_endpoint [Finite M] {a' t : Vertex R}
    (hat : Adjacent R (alpha R) t) (ha't : Adjacent R a' t) :
    ⁅Q R (alpha R), Z R a'⁆ ≤ Z R a' :=
  le_normalizer_iff_commutator_le_right.mp
    ((Q_le_endpoint_stabilizer hat ha't).trans (Z_normalized R a'))

/-- The reverse normalization puts the same commutator in Q_alpha. -/
theorem local_commutator_le_Q [Finite M] (geometry : Geometry R)
    (hb : geometry.b R = 2) {a' : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl)) :
    ⁅Q R (alpha R), Z R a'⁆ ≤ Q R (alpha R) := by
  have ha' := critical_endpoint_color R (alpha R) rfl _ hc
  have hb' : 0 < criticalDistance R a' (geometry.exists_critical a' ha') := by
    rw [geometry.distance_constant a' ha']
    change 0 < geometry.b R
    omega
  have hd : (cosetGraph R).dist a' (alpha R) = 2 := by
    rw [SimpleGraph.dist_comm]
    exact hc.1.trans hb
  exact le_normalizer_iff_commutator_le_left.mp
    ((Z_le_stabilizer_of_dist_two R geometry a' ha' hb' (alpha R) hd).trans
      (Q_normalized R (alpha R)))

/-- Local commutator elements square to one, even before core commutativity is known. -/
theorem local_commutator_pow_two [Finite M] (geometry : Geometry R)
    (hb : geometry.b R = 2) {a' t : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (ha't : Adjacent R a' t)
    {x : FreeAmalgam R} (hx : x ∈ ⁅Q R (alpha R), Z R a'⁆) : x ^ 2 = 1 := by
  have ha' := critical_endpoint_color R (alpha R) rfl _ hc
  have hb' : 0 < criticalDistance R a' (geometry.exists_critical a' ha') := by
    rw [geometry.distance_constant a' ha']
    change 0 < geometry.b R
    omega
  exact (mem_omegaCenter_iff.mp
    (geometry.omega_bound a' ha' hb' (local_commutator_le_endpoint hat ha't hx))).2.1

private theorem centralizer_index_restrict {G : Type*} [Group G]
    (K T D : Subgroup G) [Finite T] (hKT : K ≤ T)
    (y : K) (hyD : (y : G) ∈ D) :
    (centralizer ({y} : Set K)).index ≤ (centralizer (D : Set G)).relIndex T := by
  let : Finite K := Finite.of_injective (inclusion hKT) (inclusion_injective hKT)
  have hle : (centralizer (D : Set G)).subgroupOf K ≤ centralizer ({y} : Set K) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (hx y hyD).symm
  exact (index_antitone hle).trans (relIndex_le_of_le_right hKT
    ((centralizer (D : Set G)).subgroupOf T).index_ne_zero_of_finite)

/-- Restrict the edge centralizer bound to an element of the actual core. -/
theorem core_centralizer_index_le_edge [Finite M] {a' t : Vertex R}
    (hat : Adjacent R (alpha R) t) (y : core R (alpha R))
    (hy : (y : FreeAmalgam R) ∈ ⁅Z R a', Q R t⁆) :
    (centralizer ({y} : Set (core R (alpha R)))).index ≤
      (centralizer ((⁅Z R a', Q R t⁆ : Subgroup (FreeAmalgam R)) :
        Set (FreeAmalgam R))).relIndex (Q R t) := by
  let : Finite (stabilizer R t) := finite_stabilizer R t
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R t from fun _ hx => hx.1))
    (inclusion_injective _)
  exact centralizer_index_restrict _ _ _ (core_le_edge hat) y hy

/-- The critical endpoint layer also lies in the common edge group. -/
theorem endpoint_Z_le_edge [Finite M] (geometry : Geometry R)
    (hb : geometry.b R = 2) {a' t : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl))
    (ha't : Adjacent R a' t) : Z R a' ≤ Q R t := by
  have ha' := critical_endpoint_color R (alpha R) rfl _ hc
  apply Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' ha')
  rw [geometry.distance_constant a' ha']
  change (cosetGraph R).dist a' t < geometry.b R
  rw [hb, SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr ha't)]
  decide

/-- The generating commutator lies in the subgroup controlled by the edge estimate. -/
theorem local_commutator_le_edge_commutator [Finite M] {a' t : Vertex R}
    (hat : Adjacent R (alpha R) t) :
    ⁅Q R (alpha R), Z R a'⁆ ≤ ⁅Z R a', Q R t⁆ := by
  rw [commutator_comm (Q R (alpha R))]
  exact commutator_mono le_rfl (Q_le_adjacent_h R (edge_color hat) hat)

private theorem involution_generation_of_iSup {G : Type*} [Group G]
    (K : Subgroup G) {ι : Sort*} (D : ι → Subgroup G)
    (hpow : ∀ i x, x ∈ D i → x ^ 2 = 1) (hgen : K = ⨆ i, D i) :
    closure {x : K | x ^ 2 = 1} = ⊤ := by
  let I := closure {x : K | x ^ 2 = 1}
  have hle : K ≤ I.map K.subtype := by
    apply hgen.le.trans
    apply iSup_le
    intro i x hx
    have hxK : x ∈ K := by
      rw [hgen]
      exact (le_iSup D i) hx
    refine ⟨⟨x, hxK⟩, subset_closure ?_, rfl⟩
    exact Subtype.ext (hpow i x hx)
  apply top_unique
  intro x _
  obtain ⟨y, hy, hxy⟩ := hle x.property
  have he : y = x := Subtype.ext hxy
  exact he ▸ hy

/-- The source conjugate-generation identity suffices for involution generation. -/
theorem involution_generation_of_local_conjugates [Finite M]
    (geometry : Geometry R) (hb : geometry.b R = 2) {a' t : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (ha't : Adjacent R a' t)
    (hgen : core R (alpha R) = ⨆ m : M,
      (⁅Q R (alpha R), Z R a'⁆).map (MulAut.conj (embedM R m)).toMonoidHom) :
    closure {x : core R (alpha R) | x ^ 2 = 1} = ⊤ := by
  apply involution_generation_of_iSup _ _ ?_ hgen
  intro m x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← map_pow, local_commutator_pow_two geometry hb hc hat ha't hy, map_one]

/-- An escaping element of the controlled intersection gives the required core centralizer. -/
theorem small_centralizer_of_edge_estimate [Finite M] {a' t : Vertex R}
    (hat : Adjacent R (alpha R) t)
    (hindex : (centralizer ((⁅Z R a', Q R t⁆ : Subgroup (FreeAmalgam R)) :
      Set (FreeAmalgam R))).relIndex (Q R t) ≤ 2)
    (hescape : ¬ core R (alpha R) ⊓ ⁅Z R a', Q R t⁆ ≤ U R (alpha R)) :
    ∃ y : core R (alpha R), (y : FreeAmalgam R) ∉ U R (alpha R) ∧
      (centralizer ({y} : Set (core R (alpha R)))).index ≤ 2 := by
  obtain ⟨y, ⟨hyK, hyD⟩, hyU⟩ := Set.not_subset.mp hescape
  exact ⟨⟨y, hyK⟩, hyU, (core_centralizer_index_le_edge hat ⟨y, hyK⟩ hyD).trans hindex⟩

/-- Conjugate generation and the non-Frattini premise provide the escaping element.
The remaining numerical premise is precisely the edge-group centralizer bound. -/
theorem small_centralizer_of_local_conjugates [Finite M]
    {L : Subgroup M} (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {a' t : Vertex R} (hat : Adjacent R (alpha R) t)
    (hgen : core R (alpha R) = ⨆ m : M,
      (⁅Q R (alpha R), Z R a'⁆).map (MulAut.conj (embedM R m)).toMonoidHom)
    (hindex : (centralizer ((⁅Z R a', Q R t⁆ : Subgroup (FreeAmalgam R)) :
      Set (FreeAmalgam R))).relIndex (Q R t) ≤ 2) :
    ∃ y : core R (alpha R), (y : FreeAmalgam R) ∉ U R (alpha R) ∧
      (centralizer ({y} : Set (core R (alpha R)))).index ≤ 2 := by
  apply small_centralizer_of_edge_estimate hat hindex
  intro hcontained
  have hDK : ⁅Q R (alpha R), Z R a'⁆ ≤ core R (alpha R) := by
    intro x hx
    rw [hgen]
    exact (le_iSup (fun m : M => (⁅Q R (alpha R), Z R a'⁆).map
      (MulAut.conj (embedM R m)).toMonoidHom) (1 : M)) ⟨x, hx, by simp⟩
  have hDU : ⁅Q R (alpha R), Z R a'⁆ ≤ U R (alpha R) :=
    (le_inf hDK (local_commutator_le_edge_commutator hat)).trans hcontained
  have hKU : core R (alpha R) ≤ U R (alpha R) := by
    rw [hgen]
    apply iSup_le
    intro m x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact le_normalizer_iff.mp natural.normalized (embedM R m) ⟨m, rfl⟩ z (hDU hz)
  have hUZ : U R (alpha R) ≤ Z R (alpha R) :=
    le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le (pResidual 2 (stabilizer R (alpha R)))).trans
        (Z_normalized R (alpha R)))
  have hbpos : 0 < criticalDistance R (alpha R)
      (geometry.exists_critical (alpha R) rfl) := by
    change 0 < geometry.b R
    omega
  exact hlarge (hKU.trans (hUZ.trans
    ((geometry.omega_bound (alpha R) rfl hbpos).trans le_sup_right)))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
