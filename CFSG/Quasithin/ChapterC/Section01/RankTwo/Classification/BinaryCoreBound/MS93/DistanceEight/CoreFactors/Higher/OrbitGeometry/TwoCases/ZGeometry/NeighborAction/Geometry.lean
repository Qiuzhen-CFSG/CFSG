module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Decomposition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Intersections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.IndexTwo

/-!
# The actual seed and actor in the neighboring second-layer quotient

The local turn identifies the second orbit layer at c with the G_c-span
of the first layer at a. Centrality identifies [Z_c,Q_a] with H_a and
puts [hat V_a,Q_a] in the neighboring first layer. The source cardinal
|H_a|=4 and the index-two fixed edge layer then give [Q_a:Q_a ∩ Q_c]=4.
The edge index implies Q_a joined with Q_c equals the common edge kernel.

The (4.5.3)(i) identities and the (4.5.1)(v) cardinal remain literal
preceding-source inputs. No higher quotient model, (4.5.5), conjugate-pair
bound or final core shape is used. Forward-choice independence is proved
only for choices related by the stated actual local turns.

These are geometric inputs to the remaining marked quotient calculation;
they do not themselves assert the neighboring-action estimate.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)--(4.5.5), pp.896--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem path_color {a : Vertex R} (p : Higher.SourcePath a)
    {i : ℕ} (hi : Even i) (hi14 : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (RegularPaths.walk_vertex_color p.start_color p.walk (by rw [p.length_eq]; exact hi14)).mpr hi

private theorem path_adjacent {a : Vertex R} (p : Higher.SourcePath a) {i : ℕ} (hi : i < 14) :
    Adjacent R (p.walk.getVert i) (p.walk.getVert (i + 1)) :=
  (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by rw [p.length_eq]; exact hi))

private theorem span_le {G : Type*} [Group G] {A P N : Subgroup G}
    (hA : A ≤ N) (hN : P ≤ normalizer N) : conjugatesIn A P ≤ N := by
  apply iSup_le
  intro g
  exact (map_mono hA).trans
    (mem_normalizer_iff_map_conj_eq.mp (hN (P.inv_mem g.property))).le

private theorem seed_le_span {G : Type*} [Group G] (A P : Subgroup G) :
    A ≤ conjugatesIn A P := by
  intro x hx
  apply le_iSup (fun g : P => rightConjugate A g) 1
  exact ⟨x, hx, by simp⟩

/-- The turn at c gives exact generation by the backward first layer. -/
theorem second_eq_backward_span {a c d e : Vertex R}
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a)
    (hVd : hatV R d e = Vcirc R d ⊔ Z R d)
    (hturn : ∃ g ∈ stabilizer R c, act R g d = a) :
    hatW R c d e = conjugatesIn (hatV R a c) (stabilizer R c) := by
  obtain ⟨g, hg, ht⟩ := hturn
  have hm : rightConjugate (hatV R d e) g = hatV R a c := by
    rw [rightConjugate, hVd, Subgroup.map_sup, ← Vcirc_act, ← Z_act, ht, ← hVa]
  apply le_antisymm
  · apply span_le ?_ (conjugatesIn_normalized _ _)
    have hn : (conjugatesIn (hatV R a c) (stabilizer R c)).map
        (MulAut.conj g).toMonoidHom = conjugatesIn (hatV R a c) (stabilizer R c) :=
      mem_normalizer_iff_map_conj_eq.mp (conjugatesIn_normalized _ _ hg)
    have hh : (rightConjugate (hatV R d e) g).map (MulAut.conj g).toMonoidHom =
        hatV R d e := by
      rw [rightConjugate, map_map]
      have hf : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
          MonoidHom.id (FreeAmalgam R) := by
        apply MonoidHom.ext
        intro x
        simp [mul_assoc]
      rw [hf, map_id]
    rw [← hh, hm]
    exact (map_mono (seed_le_span (hatV R a c) (stabilizer R c))).trans hn.le
  · exact span_le (hatV_le_next_hatW hVa hVd ⟨g,hg,ht⟩) (hatW_normalized R c d e)

/-- Two forward choices give the same second layer when their actual local
turns take them to the same backward center. The third vertices are retained
until the two literal (4.5.3)(i) identities identify their first layers. -/
theorem second_eq_of_turns {a c d e d' e' : Vertex R}
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a)
    (hVd : hatV R d e = Vcirc R d ⊔ Z R d)
    (hVd' : hatV R d' e' = Vcirc R d' ⊔ Z R d')
    (hturn : ∃ g ∈ stabilizer R c, act R g d = a)
    (hturn' : ∃ g ∈ stabilizer R c, act R g d' = a) :
    hatW R c d e = hatW R c d' e' :=
  (second_eq_backward_span hVa hVd hturn).trans
    (second_eq_backward_span hVa hVd' hturn').symm

/-- The local first-layer kernel action is precisely the preceding H. -/
theorem first_kernel_commutator (common : CommonFacts R source geometry) {a c : Vertex R}
    (ha : color R a = false)
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a) :
    ⁅hatV R a c, Q R a⁆ = H R a := by
  rw [commutator_comm]
  have he := commutator_eq_of_centralizing_sup
    (show Z R a ⊔ Vcirc R a = hatV R a c by rw [hVa, sup_comm])
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha))
    (((DistanceEight.Vcirc_le_V R a).trans (geometry.V_local a ha (by rw [geometry.distance_constant a ha]; exact common.large_distance))).trans (Q_normalized R a))
  rw [← he, commutator_comm]
  rfl

/-- Centrality identifies the actual neighboring Z-displacement with H. -/
theorem neighbor_Z_commutator (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c : Vertex R} (ha : color R a = false)
    (hca : (cosetGraph R).dist c a = 2)
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a) :
    ⁅Z R c, Q R a⁆ = H R a := by
  have hcent : ⁅Z R c, Q R a⁆ ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
    intro x hx y hy
    obtain ⟨z,hz,rfl⟩ := earlier.centrality a ha
      (commutator_mono ((Z_le_localZSpan R c a).trans (localZSpan_le_V R hca.le)) le_rfl hx)
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
  have he : ⁅hatV R a c, Q R a⁆ = ⁅Z R c, Q R a⁆ := by
    rw [hatV, LocalCommutator.span_commutator_eq_conjugates ha hca.le common.large_distance]
    exact Escape.PairingControl.conjugatesIn_eq_of_normalized _ _
      ((le_centralizer_iff.mp hcent).trans (Subgroup.centralizer_le_normalizer _))
  exact he.symm.trans (first_kernel_commutator common ha hVa)

/-- The source first-layer seed is fixed modulo the actual neighboring denominator. -/
theorem first_action_le_neighbor_first [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : Higher.SourcePath a)
    (hVa : hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a) :
    ⁅hatV R a (p.walk.getVert 6), Q R a⁆ ≤
      hatV R (p.walk.getVert 6) (p.walk.getVert 8) := by
  have ha : color R a = false := p.center_eq ▸ path_color p (i := 4) (by decide) (by decide)
  have hc := path_color p (i := 6) (by decide) (by decide)
  have hat : Adjacent R a (p.walk.getVert 5) := by
    simpa only [p.center_eq] using path_adjacent p (i := 4) (by decide)
  have hct := adjacent_symm R (path_adjacent p (i := 5) (by decide))
  rw [first_kernel_commutator common ha hVa]
  exact (Early.H_le_edge_Z common earlier ha hat).trans
    ((Escape.EdgeTransfer.edge_Z_le _ _ hc hct).trans
      (Early.Z_le_hatV hc (p.dist (i := 6) (j := 8) (by decide) (by decide))))

/-- An index-two intermediate subgroup is either endpoint. -/
private theorem eq_of_index_two {G : Type*} [Group G] {N F U : Subgroup G}
    (hNF : N ≤ F) (hFU : F ≤ U) (hi : N.relIndex U = 2) (hne : F ≠ U) : F = N := by
  have hm := relIndex_mul_relIndex N F U hNF hFU
  rw [hi] at hm
  have hd : F.relIndex U ∣ 2 := ⟨N.relIndex F, by simpa only [Nat.mul_comm] using hm.symm⟩
  have hidx : F.relIndex U = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    (fun h => hne (le_antisymm hFU (relIndex_eq_one.mp h)))
  rw [hidx] at hm
  exact le_antisymm (relIndex_eq_one.mp (by omega)) hNF

/-- The literal Q_a action at c has order four; no quotient dimension is assumed. -/
theorem neighbor_kernel_index [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a c t : Vertex R} (ha : color R a = false)
    (hca : (cosetGraph R).dist c a = 2)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a)
    (hH : Nat.card (H R a) = 4) : (Q R c).relIndex (Q R a) = 4 := by
  have hc := (color_eq_of_dist_even R c a (by rw [hca]; decide)).trans ha
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hQaQt := Q_le_adjacent_h R ht hat
  have hQtGc : Q R t ≤ stabilizer R c := fun _ hx => hx.2 c (adjacent_symm R hct)
  have hfix : Z R c ⊓ centralizer (Q R a : Set (FreeAmalgam R)) = Z R t := by
    refine eq_of_index_two ?_ inf_le_left (earlier.edge_Z_index c t hc hct) ?_
    · rw [Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
        (LocalCommutator.moduleFacts common) c t hc hct]
      exact inf_le_inf_left _ (centralizer_le hQaQt)
    · intro he
      have hzero : ⁅Z R c,Q R a⁆ = ⊥ :=
        commutator_eq_bot_iff_le_centralizer.mpr (he.ge.trans inf_le_right)
      rw [neighbor_Z_commutator common earlier ha hca hVa] at hzero
      rw [hzero, Subgroup.card_bot] at hH
      omega
  let := geometry.Z_elementary (by rw [earlier.distance]; decide) c hc
  have hcomm : ⁅Z R c,Q R a⁆ ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
    rw [neighbor_Z_commutator common earlier ha hca hVa]
    intro x hx q hq
    obtain ⟨z,hz,rfl⟩ := H_le_localCenter_of_central R a (earlier.centrality a ha) hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨q,hq.1⟩)
  have hi := DistanceFour.Early.actor_index_eq_displacement_card_of_fixed_index_two
    (Z R c) (Q R a) ((hQaQt.trans hQtGc).trans (Z_normalized R c)) hcomm
    (by rw [hfix]; exact earlier.edge_Z_index c t hc hct)
  have hker : (centralizer (Z R c : Set (FreeAmalgam R))).subgroupOf (Q R a) =
      (Q R c).subgroupOf (Q R a) := by
    ext x
    change (x : FreeAmalgam R) ∈ centralizer (Z R c : Set (FreeAmalgam R)) ↔
      (x : FreeAmalgam R) ∈ Q R c
    constructor
    · intro hx
      rw [← common.centralizer c t hc hct]
      exact ⟨hQaQt x.property, hx⟩
    · intro hx
      exact le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c hc)) hx
  change ((Q R c).subgroupOf (Q R a)).index = 4
  rw [← hker]
  change (centralizer (Z R c : Set (FreeAmalgam R))).relIndex (Q R a) = 4
  rw [hi, neighbor_Z_commutator common earlier ha hca hVa, hH]

/-- The two actual neighboring kernels cover their common edge kernel. -/
theorem neighbor_kernel_join [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a c t : Vertex R} (ha : color R a = false)
    (hca : (cosetGraph R).dist c a = 2)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a)
    (hH : Nat.card (H R a) = 4) : Q R a ⊔ Q R c = Q R t := by
  have hc := (color_eq_of_dist_even R c a (by rw [hca]; decide)).trans ha
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hS : Q R a ⊔ Q R c ≤ Q R t :=
    sup_le (Q_le_adjacent_h R ht hat) (Q_le_adjacent_h R ht hct)
  let := finite_stabilizer R t
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R t from fun _ hx => hx.1)) (inclusion_injective _)
  let : Finite (Q R a ⊔ Q R c : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hS) (inclusion_injective _)
  have hlo := relIndex_le_of_le_right
    (show Q R a ≤ Q R a ⊔ Q R c from le_sup_left)
    (show (Q R c).relIndex (Q R a ⊔ Q R c) ≠ 0 from Subgroup.index_ne_zero_of_finite)
  rw [neighbor_kernel_index common earlier ha hca hat hct hVa hH] at hlo
  have hmul := relIndex_mul_relIndex (Q R c) (Q R a ⊔ Q R c) (Q R t) le_sup_right hS
  rw [earlier.edge_Q_index c t hc hct] at hmul
  have hpos : (Q R a ⊔ Q R c).relIndex (Q R t) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hone : (Q R a ⊔ Q R c).relIndex (Q R t) = 1 := by nlinarith
  exact le_antisymm hS (relIndex_eq_one.mp hone)

/-- The neighboring kernel normalizes the actual second orbit layer. -/
theorem second_normalized_by_neighbor [Finite M] {a : Vertex R} (p : Higher.SourcePath a) :
    Q R a ≤ normalizer (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) := by
  have ha : color R a = false := p.center_eq ▸ path_color p (i := 4) (by decide) (by decide)
  exact (Q_le_stabilizer_of_dist_two R a (p.walk.getVert 6) ha
    (by rw [SimpleGraph.dist_comm]; exact p.two_step_distances.1)).trans
      (hatW_normalized R _ _ _)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction
