module

public import CFSG.Quasithin.ChapterF.Section07.Track

/-!
# Conjugate modules and the geometry of critical pairs

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), F.7.10 and the geometric parts of F.7.11, printed
pp.313--314 (PDF pp.324--325).

The first-orbit module is the conjugate of V at that vertex; normality in the
base stabilizer proves independence of its representative. Second-orbit
modules are joins over the actual neighbors. The construction is equivariant,
is normal relative to the vertex stabilizer, and at the second base vertex
is exactly the conjugate span under G₂. Right cosets retain the source's
inverse-conjugation convention.

Core propagation gives commutation below the track and edge-core containments
along geodesics. Those containments record the internal segment length as
`dist s v + 2 = b`: this entails b ≥ 2 and is the ordering required by the
printed proof of F.7.11(5). No assertion about that bound at b = 1 is made.
The even-pair containments are also proved; nontriviality, quadratic actions,
Frattini triviality and the FF-module parity conclusions are separate algebraic
assembly obligations, not assumptions of the construction.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base exists_smul_base incident_base translationGraphIso)
open CFSG.Quasithin.ChapterF.Section07.Track
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- All representatives of a first-type vertex give the same conjugate when
its base stabilizer normalizes V. The join makes the definition choice-free. -/
def firstModule (V : Subgroup G) (v : Vertex F) : Subgroup G :=
  ⨆ g : G, ⨆ (_ : g • base F false = v), V.map (MulAut.conj g).toMonoidHom

private theorem conj_map_mul (V : Subgroup G) (g h : G) :
    (V.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      V.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem conjugate_eq_of_same_vertex (V : Subgroup G)
    (hn : F false ≤ normalizer (V : Set G)) (g h : G)
    (he : g • base F false = h • base F false) :
    V.map (MulAut.conj h).toMonoidHom = V.map (MulAut.conj g).toMonoidHom := by
  have hk : g⁻¹ * h ∈ F false := by
    rw [← show stabilizer F (base F false) = F false from stabilizer_base F false]
    change (g⁻¹ * h) • base F false = base F false
    rw [mul_smul, ← he, inv_smul_smul]
  have hmap := mem_normalizer_iff_map_conj_eq.mp (hn hk)
  change V.map (MulAut.conj (g⁻¹ * h)).toMonoidHom = V at hmap
  have hm := conj_map_mul V g (g⁻¹ * h)
  rw [hmap] at hm
  simpa only [mul_inv_cancel_left] using hm.symm

theorem firstModule_translate_base (V : Subgroup G)
    (hn : F false ≤ normalizer (V : Set G)) (g : G) :
    firstModule F V (g • base F false) = V.map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · exact iSup_le fun h => iSup_le fun hh =>
      (conjugate_eq_of_same_vertex F V hn g h hh.symm).le
  · exact le_iSup_of_le g (le_iSup_of_le rfl le_rfl)

private theorem conj_map_one (V : Subgroup G) :
    V.map (MulAut.conj (1 : G)).toMonoidHom = V := by
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, map_id]

theorem firstModule_base (V : Subgroup G) (hn : F false ≤ normalizer (V : Set G)) :
    firstModule F V (base F false) = V := by
  have h := firstModule_translate_base F V hn 1
  simpa only [one_smul, conj_map_one] using h

theorem firstModule_eq_bot_of_type {V : Subgroup G} {v : Vertex F} (hv : v.type = true) :
    firstModule F V v = ⊥ := by
  apply eq_bot_iff.mpr
  refine iSup_le fun g => iSup_le fun hg => ?_
  have ht := congrArg Subgroup.CosetGeometry.Vertex.type hg
  change false = v.type at ht
  rw [hv] at ht
  exact Bool.false_ne_true ht |>.elim

theorem firstModule_translate (V : Subgroup G) (hn : F false ≤ normalizer (V : Set G))
    (g : G) (v : Vertex F) :
    firstModule F V (g • v) = (firstModule F V v).map (MulAut.conj g).toMonoidHom := by
  cases hv : v.type with
  | false =>
    obtain ⟨h, hh⟩ := exists_smul_base F v
    rw [hv] at hh
    rw [← hh, ← mul_smul, firstModule_translate_base F V hn,
      firstModule_translate_base F V hn, conj_map_mul]
  | true =>
    rw [firstModule_eq_bot_of_type F hv,
      firstModule_eq_bot_of_type F (show (g • v).type = true from hv), Subgroup.map_bot]

/-- F.7.10: first-type conjugates and second-type joins over actual neighbors. -/
def vertexModule (V : Subgroup G) (v : Vertex F) : Subgroup G :=
  if v.type = false then firstModule F V v
  else ⨆ w : Vertex F, ⨆ (_ : (graph F).Adj v w), firstModule F V w

theorem vertexModule_first (V : Subgroup G) {v : Vertex F} (hv : v.type = false) :
    vertexModule F V v = firstModule F V v := if_pos hv

theorem vertexModule_second (V : Subgroup G) {v : Vertex F} (hv : v.type = true) :
    vertexModule F V v = ⨆ w : Vertex F, ⨆ (_ : (graph F).Adj v w), firstModule F V w :=
  if_neg (by rw [hv]; decide)

theorem vertexModule_translate_base (V : Subgroup G)
    (hn : F false ≤ normalizer (V : Set G)) (g : G) :
    vertexModule F V (g • base F false) = V.map (MulAut.conj g).toMonoidHom := by
  rw [vertexModule_first F V rfl, firstModule_translate_base F V hn]

theorem firstModule_le_vertexModule_of_adj (V : Subgroup G) {v w : Vertex F}
    (hv : v.type = true) (hvw : (graph F).Adj v w) :
    firstModule F V w ≤ vertexModule F V v := by
  rw [vertexModule_second F V hv]
  exact le_iSup_of_le w (le_iSup_of_le hvw le_rfl)

private theorem map_neighborJoin_le (V : Subgroup G)
    (hn : F false ≤ normalizer (V : Set G)) (g : G) (v : Vertex F) :
    (⨆ w : Vertex F, ⨆ (_ : (graph F).Adj v w), firstModule F V w).map
        (MulAut.conj g).toMonoidHom ≤
      ⨆ w : Vertex F, ⨆ (_ : (graph F).Adj (g • v) w), firstModule F V w := by
  rw [Subgroup.map_iSup]
  refine iSup_le fun w => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hw => ?_
  rw [← firstModule_translate F V hn g w]
  exact le_iSup_of_le (g • w) (le_iSup_of_le ((translationGraphIso F g).map_rel_iff.mpr hw)
    le_rfl)

theorem vertexModule_translate (V : Subgroup G)
    (hn : F false ≤ normalizer (V : Set G)) (g : G) (v : Vertex F) :
    vertexModule F V (g • v) = (vertexModule F V v).map (MulAut.conj g).toMonoidHom := by
  cases hv : v.type with
  | false =>
    rw [vertexModule_first F V hv, vertexModule_first F V (show (g • v).type = false from hv)]
    exact firstModule_translate F V hn g v
  | true =>
    rw [vertexModule_second F V hv, vertexModule_second F V (show (g • v).type = true from hv)]
    apply le_antisymm _ (map_neighborJoin_le F V hn g v)
    have h := map_mono (f := (MulAut.conj g).toMonoidHom)
      (map_neighborJoin_le F V hn g⁻¹ (g • v))
    simpa only [inv_smul_smul, conj_map_mul, mul_inv_cancel, conj_map_one] using h

theorem stabilizer_normalizes_vertexModule (V : Subgroup G)
    (hn : F false ≤ normalizer (V : Set G)) (v : Vertex F) :
    stabilizer F v ≤ normalizer (vertexModule F V v : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (vertexModule F V v).map (MulAut.conj g).toMonoidHom = _
  rw [← vertexModule_translate F V hn, (show g • v = v from hg)]

/-- The radius fixed by V transports to every first-type vertex. -/
theorem firstModule_le_ballKernel (V : Subgroup G)
    (hn : F false ≤ normalizer (V : Set G)) {b : ℕ}
    (hb : V ≤ ballKernel F (base F false) b) {v : Vertex F} (hv : v.type = false) :
    firstModule F V v ≤ ballKernel F v b := by
  obtain ⟨g, hg⟩ := exists_smul_base F v
  rw [hv] at hg
  rw [← hg, firstModule_translate_base F V hn, ballKernel_translate]
  exact map_mono hb

/-- The seed's embedded prime-core containment transports with its vertex. -/
theorem firstModule_le_vertex_core (V : Subgroup G)
    (hn : F false ≤ normalizer (V : Set G)) (p : ℕ)
    (hc : V ≤ (F false).pCoreIn p) {v : Vertex F} (hv : v.type = false) :
    firstModule F V v ≤ (stabilizer F v).pCoreIn p := by
  obtain ⟨g, hg⟩ := exists_smul_base F v
  rw [hv] at hg
  rw [← hg, firstModule_translate_base F V hn, stabilizer_translate,
    show stabilizer F (base F false) = F false from stabilizer_base F false,
    Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective p _ (MulAut.conj g).injective]
  exact map_mono hc

/-- F.7.9(1) transported to any first-type center, for use along geodesics. -/
theorem firstModule_le_edge_core (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {a v w : Vertex F} (ha : a.type = false)
    (hd : (graph F).dist a v < D.track hne) (hvw : (graph F).Adj v w) :
    firstModule F D.seed a ≤ (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 := by
  exact le_edge_core_below_track F D.generates
    (firstModule_le_vertex_core F D.seed D.seed_normalized 2
      (show D.seed ≤ (F false).pCoreIn 2 from map_mono D.reduced.le_pCore) ha)
    (firstModule_le_ballKernel F D.seed D.seed_normalized (D.track_spec hne).2.1 ha)
    hd hvw

/-- F.7.9(1), local-kernel form at an arbitrary first-type center. -/
theorem firstModule_le_local_core (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {a v : Vertex F} (ha : a.type = false)
    (hd : (graph F).dist a v < D.track hne) :
    firstModule F D.seed a ≤ (ballKernel F v 1).pCoreIn 2 := by
  exact le_local_core_below_track F D.generates
    (firstModule_le_vertex_core F D.seed D.seed_normalized 2
      (show D.seed ≤ (F false).pCoreIn 2 from map_mono D.reduced.le_pCore) ha)
    (firstModule_le_ballKernel F D.seed D.seed_normalized (D.track_spec hne).2.1 ha) hd

/-- The source neighbor join at the second base vertex is exactly the
normal closure of V under that vertex stabilizer. -/
theorem second_base_module_eq_conjugate_join (V : Subgroup G)
    (hn : F false ≤ normalizer (V : Set G)) :
    vertexModule F V (base F true) =
      ⨆ g : F true, V.map (MulAut.conj (g : G)).toMonoidHom := by
  rw [vertexModule_second F V rfl]
  have hedge : (graph F).Adj (base F true) (base F false) :=
    ⟨by change true ≠ false; decide, incident_base F true false⟩
  apply le_antisymm
  · refine iSup_le fun w => iSup_le fun hw => ?_
    obtain ⟨g, hg, rfl⟩ := locally_transitive F hedge hw
    have hg' : g ∈ F true := by
      simpa only [stabilizer, base, stabilizer_base] using hg
    rw [firstModule_translate_base F V hn]
    exact le_iSup_of_le (⟨g, hg'⟩ : F true) le_rfl
  · refine iSup_le fun g => ?_
    have hg : (g : G) • base F true = base F true := by
      have hs : (g : G) ∈ stabilizer F (base F true) := by
        rw [show stabilizer F (base F true) = F true from stabilizer_base F true]
        exact g.property
      exact hs
    have he : (graph F).Adj (base F true) ((g : G) • base F false) := by
      simpa only [Subgroup.CosetGeometry.translationGraphIso_apply, hg] using (translationGraphIso F (g : G)).map_rel_iff.mpr hedge
    rw [← firstModule_translate_base F V hn (g : G)]
    exact le_iSup_of_le ((g : G) • base F false) (le_iSup_of_le he le_rfl)

/-- A neighbor join lies in an edge core whenever all its generators are
strictly closer than the track to the first endpoint of that edge. -/
theorem neighbor_join_le_edge_core (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {s v w : Vertex F} (hs : s.type = true)
    (hd : (graph F).dist s v + 1 < D.track hne) (hvw : (graph F).Adj v w) :
    vertexModule F D.seed s ≤ (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 := by
  rw [vertexModule_second F D.seed hs]
  refine iSup_le fun a => iSup_le fun ha => ?_
  have hat : a.type = false := by
    have h := ha.1
    cases ht : a.type <;> simp_all
  apply firstModule_le_edge_core F D hne hat _ hvw
  have ht := (connected F D.generates).dist_triangle (u := a) (v := s) (w := v)
  have he : (graph F).dist a s = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr ha.symm
  rw [he] at ht
  omega

/-- F.7.11(5) with the required ordering of the two internal positions made
explicit. The equation records b-2 intervening edges and entails b ≥ 2. -/
theorem geodesic_edge_core (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {s v w : Vertex F} (hs : s.type = true)
    (hsegment : (graph F).dist s v + 2 = D.track hne) (hvw : (graph F).Adj v w) :
    vertexModule F D.seed s ≤ (stabilizer F v ⊓ stabilizer F w).pCoreIn 2 :=
  neighbor_join_le_edge_core F D hne hs (by omega) hvw

/-- The first assertion of F.7.11(6), for an odd-type endpoint and a vertex
two positions along the geodesic. The orientation of the edge is preserved. -/
theorem opposite_geodesic_edge_core (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {s v w : Vertex F} (hs : s.type = true)
    (hsegment : (graph F).dist s v + 2 = D.track hne) (hwv : (graph F).Adj w v) :
    vertexModule F D.seed s ≤ (stabilizer F w ⊓ stabilizer F v).pCoreIn 2 := by
  rw [inf_comm]
  exact geodesic_edge_core F D hne hs hsegment hwv.symm

/-- Reducedness centralizes the actual embedded two-core at the first base. -/
theorem seed_commutes_vertex_core (D : SourceSetup F) :
    ⁅D.seed, (stabilizer F (base F false)).pCoreIn 2⁆ = ⊥ := by
  have hc : ⁅D.V, pCore 2 (F false)⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr D.reduced.le_centralizer_pCore
  have hm := congrArg (fun H : Subgroup (F false) => H.map (F false).subtype) hc
  rw [map_commutator, Subgroup.map_bot] at hm
  rw [show stabilizer F (base F false) = F false from stabilizer_base F false]
  exact hm

/-- F.7.11(3): all first-type modules strictly below the track commute with V. -/
theorem seed_commutes_below_track (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v : Vertex F} (hv : v.type = false)
    (hd : (graph F).dist (base F false) v < D.track hne) :
    ⁅D.seed, firstModule F D.seed v⁆ = ⊥ := by
  have h := firstModule_le_local_core F D hne hv
    (show (graph F).dist v (base F false) < D.track hne by
      rwa [SimpleGraph.dist_comm])
  have hle := h.trans (ballKernel_core_le_vertex_core F 2 (base F false) 1)
  exact eq_bot_iff.mpr ((commutator_mono le_rfl hle).trans (seed_commutes_vertex_core F D).le)

/-- The commutation bound is equivariant and applies between any two first-type vertices. -/
theorem firstModules_commute_below_track (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {a v : Vertex F} (ha : a.type = false) (hv : v.type = false)
    (hd : (graph F).dist a v < D.track hne) :
    ⁅firstModule F D.seed a, firstModule F D.seed v⁆ = ⊥ := by
  obtain ⟨g, hg⟩ := exists_smul_base F a
  rw [ha] at hg
  have hd' : (graph F).dist (base F false) (g⁻¹ • v) < D.track hne := by
    have he := dist_smul F g (base F false) (g⁻¹ • v)
    rw [smul_inv_smul, hg] at he
    rwa [← he]
  have h := seed_commutes_below_track F D hne
    (show (g⁻¹ • v).type = false from hv) hd'
  have hm := congrArg (fun H : Subgroup G => H.map (MulAut.conj g).toMonoidHom) h
  rw [map_commutator, ← firstModule_translate_base F D.seed D.seed_normalized,
    ← firstModule_translate F D.seed D.seed_normalized, smul_inv_smul, hg,
    Subgroup.map_bot] at hm
  exact hm

/-- The right-coset convention of the book corresponds to conjugation by g⁻¹. -/
theorem vertexModule_rightVertex (V : Subgroup G)
    (hn : F false ≤ normalizer (V : Set G)) (g : G) :
    vertexModule F V (rightVertex F false g) = V.map (MulAut.conj g⁻¹).toMonoidHom :=
  vertexModule_translate_base F V hn g⁻¹

/-- The first-orbit modules are the actual elementary abelian conjugates of V. -/
theorem firstModule_elementary (D : SourceSetup F) {v : Vertex F} (hv : v.type = false) :
    IsElementaryAbelian 2 (firstModule F D.seed v) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := D.reduced.elementary
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  obtain ⟨g, hg⟩ := exists_smul_base F v
  rw [hv] at hg
  rw [← hg, firstModule_translate_base F D.seed D.seed_normalized]
  exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom

/-- Every source module is a subgroup of its own vertex stabilizer, including
second-type neighbor joins when the track is only one. -/
theorem vertexModule_le_stabilizer (D : SourceSetup F) (v : Vertex F) :
    vertexModule F D.seed v ≤ stabilizer F v := by
  cases hv : v.type with
  | false =>
    rw [vertexModule_first F D.seed hv]
    exact (firstModule_le_vertex_core F D.seed D.seed_normalized 2
      (show D.seed ≤ (F false).pCoreIn 2 from map_mono D.reduced.le_pCore) hv).trans
      (pCoreIn_le 2 _)
  | true =>
    rw [vertexModule_second F D.seed hv]
    refine iSup_le fun w => iSup_le fun hw => ?_
    have hwt : w.type = false := by
      have h := hw.1
      cases ht : w.type <;> simp_all
    exact (firstModule_le_ballKernel F D.seed D.seed_normalized D.seed_le_first_kernel hwt).trans
      ((ballKernel_one_le_edge F hw.symm).trans inf_le_right)

/-- F.7.10's modules are normal relative to their own vertex groups. -/
theorem vertexModule_normal (D : SourceSetup F) (v : Vertex F) :
    ((vertexModule F D.seed v).subgroupOf (stabilizer F v)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (stabilizer_normalizes_vertexModule F D.seed D.seed_normalized v)

/-- A first-type module fixes every vertex at distance at most the track. -/
theorem firstModule_le_stabilizer_at_dist_le (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {a v : Vertex F} (ha : a.type = false)
    (hd : (graph F).dist a v ≤ D.track hne) :
    firstModule F D.seed a ≤ stabilizer F v := by
  intro g hg
  exact firstModule_le_ballKernel F D.seed D.seed_normalized
    (D.track_spec hne).2.1 ha hg v ((mem_ball_iff F D.generates a v _).mpr hd)

/-- Two first-type modules at distance at most b normalize one another. -/
theorem firstModules_commutator_le_inf (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {a v : Vertex F} (ha : a.type = false) (hv : v.type = false)
    (hd : (graph F).dist a v ≤ D.track hne) :
    ⁅firstModule F D.seed a, firstModule F D.seed v⁆ ≤
      firstModule F D.seed a ⊓ firstModule F D.seed v := by
  have hav := (firstModule_le_stabilizer_at_dist_le F D hne ha hd).trans
    (stabilizer_normalizes_vertexModule F D.seed D.seed_normalized v)
  have hva := (firstModule_le_stabilizer_at_dist_le F D hne hv
      (show (graph F).dist v a ≤ D.track hne by rwa [SimpleGraph.dist_comm])).trans
    (stabilizer_normalizes_vertexModule F D.seed D.seed_normalized a)
  rw [vertexModule_first F D.seed hv] at hav
  rw [vertexModule_first F D.seed ha] at hva
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hva)
    (le_normalizer_iff_commutator_le_right.mp hav)

/-- An even critical distance puts the endpoint in the first vertex orbit. -/
theorem even_endpoint_type (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v : Vertex F} (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : Even (D.track hne)) : v.type = false := by
  have ht := (even_dist_iff F D.generates (base F false) v).mp (hd ▸ hb)
  exact ht.symm

/-- An odd critical distance puts the endpoint in the second vertex orbit. -/
theorem odd_endpoint_type (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v : Vertex F} (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : Odd (D.track hne)) : v.type = true := by
  have ht := (odd_dist_iff F D.generates (base F false) v).mp (hd ▸ hb)
  change false ≠ v.type at ht
  cases hv : v.type <;> simp_all

/-- The containment assertions of F.7.11(2), without its still separate
nontriviality and quotient-action assertions. -/
theorem even_pair_containments (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v : Vertex F} (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : Even (D.track hne)) :
    vertexModule F D.seed v ≤ F false ∧
      ⁅D.seed, vertexModule F D.seed v⁆ ≤ D.seed ⊓ vertexModule F D.seed v := by
  have hv := even_endpoint_type F D hne hd hb
  rw [vertexModule_first F D.seed hv]
  constructor
  · have h := firstModule_le_stabilizer_at_dist_le F D hne hv
      (show (graph F).dist v (base F false) ≤ D.track hne by
        rw [SimpleGraph.dist_comm, hd])
    simpa only [stabilizer, base, stabilizer_base] using h
  · have h := firstModules_commutator_le_inf F D hne (a := base F false) rfl hv hd.le
    rwa [firstModule_base F D.seed D.seed_normalized] at h

end CFSG.Quasithin.ChapterF.Section07.CriticalPairs
