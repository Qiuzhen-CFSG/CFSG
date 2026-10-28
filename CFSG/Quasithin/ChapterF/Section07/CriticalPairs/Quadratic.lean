module

public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs
public import Theory.ElementaryAbelian.CommutingFamily
public import Theory.Frattini.PGroup

/-!
# Critical quadratic actions and elementary neighbor modules

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), F.7.11(2), (4), and (6), printed pp.313--314
(PDF pp.324--325).

For an even critical pair, the transported F.7.7(1) prime-to-two residual
identity rules out centralization. The endpoint therefore has nontrivial
image in the literal centralizer quotient. Mutual normalization and elementary
abelianness give the two nested commutator identities for quadratic action.
The linear representation and offender translation are separate consumers.

When the track exceeds two, neighboring first-type modules commute, making
their join elementary abelian with trivial intrinsic Frattini subgroup.
For an odd geodesic, shortest-walk subsegments give the exact internal distances
required by the two edge-core estimates. These imply mutual normalization and
both quadratic commutator identities. We use the elementary property directly;
no claim about the second module lying in the first vertex core is needed.

The ambient group may be infinite throughout. Finiteness is inherited only
from the given finite vertex stabilizers.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Section07.CriticalPairs
open Subgroup
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base exists_smul_base incident_base)
open CFSG.Quasithin.ChapterF.Section07.Track
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- F.7.11(4): every second-type module is elementary abelian when b > 2.
Any two neighboring first-type vertices have distance at most two, so their
modules commute by F.7.11(3). -/
theorem secondModule_elementary (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hb : 2 < D.track hne) {v : Vertex F} (hv : v.type = true) :
    IsElementaryAbelian 2 (vertexModule F D.seed v) := by
  let E (w : {w : Vertex F // (graph F).Adj v w}) := firstModule F D.seed w.val
  have ht (w : {w : Vertex F // (graph F).Adj v w}) : w.val.type = false := by
    have h := w.property.1
    cases hh : w.val.type <;> simp_all
  let : ∀ w, IsElementaryAbelian 2 (E w) := fun w => firstModule_elementary F D (ht w)
  have he : vertexModule F D.seed v = ⨆ w, E w := by
    rw [vertexModule_second F D.seed hv]
    apply le_antisymm
    · exact iSup_le fun w => iSup_le fun hw =>
        le_iSup_of_le (⟨w, hw⟩ : {w : Vertex F // (graph F).Adj v w}) le_rfl
    · exact iSup_le fun w => le_iSup_of_le w.val (le_iSup_of_le w.property le_rfl)
  rw [he]
  apply IsElementaryAbelian.iSup_of_le_centralizer
  intro x y
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply firstModules_commute_below_track F D hne (ht x) (ht y)
  have hd := (connected F D.generates).dist_triangle (u := x.val) (v := v) (w := y.val)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr x.property.symm,
    SimpleGraph.dist_eq_one_iff_adj.mpr y.property] at hd
  omega

/-- F.7.11(4), with the Frattini subgroup intrinsic to the actual module.
Only the vertex stabilizer, not the ambient group, is assumed finite. -/
theorem secondModule_frattini (D : SourceSetup F) (hne : D.V ≠ ⊥)
    (hb : 2 < D.track hne) {v : Vertex F} (hv : v.type = true) :
    frattini (vertexModule F D.seed v) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : ∀ i, Finite (F i) := D.finite
  let : Finite (vertexModule F D.seed v) :=
    Finite.of_injective (inclusion (vertexModule_le_stabilizer F D v))
      (inclusion_injective _)
  let := secondModule_elementary F D hne hb hv
  let : Fact (IsPGroup 2 (vertexModule F D.seed v)) := ⟨IsElementaryAbelian.isPGroup _ _⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

/-- F.7.7(1) puts every elementary two-subgroup of the seed centralizer
inside the first local kernel: its elements lie in the prime-to-two residual. -/
private theorem base_centralizing_elementary_le_kernel (D : SourceSetup F)
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hW : W ≤ F false) (hc : ⁅W, D.seed⁆ = ⊥) :
    W ≤ ballKernel F (base F false) 1 := by
  let : Finite (F false) := D.finite false
  have hT : (D.sylow false : Subgroup (F false)).map (F false).subtype ≤ F true := by
    rw [D.same_sylow]
    exact map_subtype_le _
  have hr := (CFSG.Quasithin.ChapterF.LocalCores.lemma_F_7_7_one
    (F false) (F true) D.V D.reduced (D.sylow false) hT D.centralizer_eq).1
  have hedge : (graph F).Adj (base F false) (base F true) :=
    ⟨Bool.false_ne_true, incident_base F false true⟩
  have hk := ballKernel_one_eq_map_normalCore F hedge
  rw [show stabilizer F (base F false) = F false from stabilizer_base F false,
    show stabilizer F (base F true) = F true from stabilizer_base F true] at hk
  intro x hx
  let y : F false := ⟨x, hW hx⟩
  have hy : y ∈ centralizer (D.V : Set (F false)) := by
    rw [mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc hx))
      (z : G) (mem_map_of_mem (F false).subtype hz)
  let z : centralizer (D.V : Set (F false)) := ⟨y, hy⟩
  have hz : z ∈ primeToResidual 2 (centralizer (D.V : Set (F false))) := by
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian x hx
  have hm := mem_map_of_mem ((F false).subtype.comp
    (centralizer (D.V : Set (F false))).subtype) hz
  rw [hr] at hm
  exact hk ▸ pCoreIn_le 2 _ hm

/-- Transport the F.7.7(1) centralizer escape criterion to any first-type
vertex. The conjugation maps and ball kernels are those of the actual geometry. -/
theorem centralizing_firstModule_le_kernel (D : SourceSetup F)
    {v : Vertex F} (hv : v.type = false) (W : Subgroup G)
    [IsElementaryAbelian 2 W] (hW : W ≤ stabilizer F v)
    (hc : ⁅W, firstModule F D.seed v⁆ = ⊥) : W ≤ ballKernel F v 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_smul_base F v
  rw [hv] at hg
  let f := (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 (W.map f) := IsElementaryAbelian.map f
  have hbase : W.map f ≤ F false := by
    have h := map_mono (f := f) hW
    rw [← stabilizer_translate] at h
    rw [← hg, inv_smul_smul] at h
    simpa only [stabilizer, base, stabilizer_base] using h
  have hcbase : ⁅W.map f, D.seed⁆ = ⊥ := by
    have h := congrArg (fun H : Subgroup G => H.map f) hc
    rw [map_commutator, ← firstModule_translate F D.seed D.seed_normalized,
      ← hg, inv_smul_smul, firstModule_base F D.seed D.seed_normalized, Subgroup.map_bot] at h
    exact h
  have h := base_centralizing_elementary_le_kernel F D (W.map f) hbase hcbase
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom) h
  rw [← ballKernel_translate, hg, map_map] at hm
  have hid : (MulAut.conj g).toMonoidHom.comp f = MonoidHom.id G := by
    ext x
    simp [f, MulAut.conj_apply, mul_assoc]
  rwa [hid, map_id] at hm

/-- The nontrivial commutator assertion of F.7.11(2). Centralization would
put the seed inside the endpoint local kernel, contradicting criticality. -/
theorem even_pair_commutator_ne_bot (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v : Vertex F} (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : Even (D.track hne)) (hcritical : ¬ D.seed ≤ ballKernel F v 1) :
    ⁅D.seed, vertexModule F D.seed v⁆ ≠ ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := D.reduced.elementary
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  have hv := even_endpoint_type F D hne hd hb
  rw [vertexModule_first F D.seed hv]
  intro hc
  apply hcritical
  apply centralizing_firstModule_le_kernel F D hv D.seed _ hc
  have h := firstModule_le_stabilizer_at_dist_le F D hne (a := base F false) rfl hd.le
  rwa [firstModule_base F D.seed D.seed_normalized] at h

/-- The actual shortest walk supplies both internal segment equations used
in F.7.11(5--6). The explicit lower bound excludes the b = 1 boundary. -/
theorem geodesic_internal_segments (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v : Vertex F} (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : 3 ≤ D.track hne) (p : (graph F).Walk (base F false) v)
    (hp : p.length = (graph F).dist (base F false) v)
    (hs : p.getVert 1 = base F true) :
    (graph F).Adj (p.getVert (p.length - 1)) v ∧
      (graph F).dist (base F true) (p.getVert (p.length - 1)) + 2 = D.track hne ∧
      (graph F).Adj (base F true) (p.getVert 2) ∧
      (graph F).dist v (p.getVert 2) + 2 = D.track hne := by
  have hlen : p.length = D.track hne := hp.trans hd
  have hpen := p.adj_getVert_succ (i := p.length - 1) (by omega)
  have hlast : p.length - 1 + 1 = p.length := by omega
  rw [hlast, p.getVert_length] at hpen
  have hseg := SimpleGraph.length_eq_dist_of_subwalk
    (SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take (p.length - 1)))
    ((p.take (p.length - 1)).isSubwalk_drop 1)
  have hstart : (p.take (p.length - 1)).getVert 1 = base F true := by
    rw [SimpleGraph.Walk.take_getVert, min_eq_right (by omega), hs]
  rw [SimpleGraph.Walk.drop_length, SimpleGraph.Walk.take_length,
    min_eq_left (Nat.sub_le _ _), hstart] at hseg
  have htwo := p.adj_getVert_succ (i := 1) (by omega)
  rw [hs] at htwo
  have hend := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_drop 2)
  rw [SimpleGraph.Walk.drop_length, SimpleGraph.dist_comm] at hend
  exact ⟨hpen, by omega, htwo, by omega⟩

/-- The first assertion of F.7.11(6), for every second-step candidate w
adjacent to the second base vertex and at distance b - 2 from the endpoint. -/
theorem odd_endpoint_edge_core (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v w : Vertex F} (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : Odd (D.track hne)) (hw : (graph F).Adj (base F true) w)
    (hsegment : (graph F).dist v w + 2 = D.track hne) :
    vertexModule F D.seed v ≤ (stabilizer F (base F true) ⊓ stabilizer F w).pCoreIn 2 :=
  opposite_geodesic_edge_core F D hne (odd_endpoint_type F D hne hd hb) hsegment hw

private theorem mutual_nested_commutators (A B : Subgroup G)
    [IsMulCommutative A] [IsMulCommutative B] (h : ⁅A, B⁆ ≤ A ⊓ B) :
    ⁅⁅A, B⁆, B⁆ = ⊥ ∧ ⁅⁅B, A⁆, A⁆ = ⊥ := by
  constructor
  · exact eq_bot_iff.mpr ((commutator_mono (h.trans inf_le_right) le_rfl).trans
      (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative B)).le)
  · rw [commutator_comm B A]
    exact eq_bot_iff.mpr ((commutator_mono (h.trans inf_le_left) le_rfl).trans
      (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative A)).le)

/-- F.7.11(2): the two group commutators expressing mutually quadratic
actions vanish, since the commutator lies in the intersection of two abelian groups. -/
theorem even_pair_nested_commutators (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v : Vertex F} (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : Even (D.track hne)) :
    ⁅⁅D.seed, vertexModule F D.seed v⁆, vertexModule F D.seed v⁆ = ⊥ ∧
      ⁅⁅vertexModule F D.seed v, D.seed⁆, D.seed⁆ = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := D.reduced.elementary
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  let : IsElementaryAbelian 2 (vertexModule F D.seed v) := by
    rw [vertexModule_first F D.seed (even_endpoint_type F D hne hd hb)]
    exact firstModule_elementary F D (even_endpoint_type F D hne hd hb)
  exact mutual_nested_commutators _ _ (even_pair_containments F D hne hd hb).2

/-- F.7.11(2): the endpoint has nontrivial image in the literal quotient
G₁/C_{G₁}(V). By `even_pair_containments`, restricting the endpoint to G₁
retains the whole subgroup. No representation or noncommutation premise is assumed. -/
theorem even_pair_quotient_image_ne_bot (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v : Vertex F} (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : Even (D.track hne)) (hcritical : ¬ D.seed ≤ ballKernel F v 1) :
    letI : D.V.Normal := D.reduced.normal
    ((vertexModule F D.seed v).subgroupOf (F false)).map
      (QuotientGroup.mk' (centralizer (D.V : Set (F false)))) ≠ ⊥ := by
  let : D.V.Normal := D.reduced.normal
  change ((vertexModule F D.seed v).subgroupOf (F false)).map
    (QuotientGroup.mk' (centralizer (D.V : Set (F false)))) ≠ ⊥
  intro h
  have hle := (Subgroup.map_eq_bot_iff _).mp h
  rw [QuotientGroup.ker_mk'] at hle
  apply even_pair_commutator_ne_bot F D hne hd hb hcritical
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  intro x hx
  have hxF := (even_pair_containments F D hne hd hb).1 hx
  have hc := hle (show (⟨x, hxF⟩ : F false) ∈
    (vertexModule F D.seed v).subgroupOf (F false) from hx)
  rw [mem_centralizer_iff] at hc ⊢
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_map.mp hy
  exact congrArg Subtype.val (hc z hz)

/-- F.7.11(6) along an actual geodesic through the second base vertex.
The penultimate edge bounds its module, and the second edge bounds the endpoint
module. Thus the two modules normalize each other; their elementary abelianness
gives both nested commutator identities. -/
theorem odd_geodesic_commutators (D : SourceSetup F) (hne : D.V ≠ ⊥)
    {v : Vertex F} (hd : (graph F).dist (base F false) v = D.track hne)
    (hodd : Odd (D.track hne)) (hb : 3 ≤ D.track hne)
    (p : (graph F).Walk (base F false) v)
    (hp : p.length = (graph F).dist (base F false) v)
    (hs : p.getVert 1 = base F true) :
    ⁅vertexModule F D.seed (base F true), vertexModule F D.seed v⁆ ≤
        vertexModule F D.seed (base F true) ⊓ vertexModule F D.seed v ∧
      ⁅⁅vertexModule F D.seed (base F true), vertexModule F D.seed v⁆,
        vertexModule F D.seed v⁆ = ⊥ ∧
      ⁅⁅vertexModule F D.seed v, vertexModule F D.seed (base F true)⁆,
        vertexModule F D.seed (base F true)⁆ = ⊥ := by
  obtain ⟨hpen, hseg, htwo, hend⟩ := geodesic_internal_segments F D hne hd hb p hp hs
  have hleft := geodesic_edge_core F D hne (s := base F true) rfl hseg hpen
  have hright := odd_endpoint_edge_core F D hne hd hodd htwo hend
  have hnormleft := (hleft.trans ((pCoreIn_le 2 _).trans inf_le_right)).trans
    (stabilizer_normalizes_vertexModule F D.seed D.seed_normalized v)
  have hnormright := (hright.trans ((pCoreIn_le 2 _).trans inf_le_left)).trans
    (stabilizer_normalizes_vertexModule F D.seed D.seed_normalized (base F true))
  have hc := le_inf (le_normalizer_iff_commutator_le_left.mp hnormright)
    (le_normalizer_iff_commutator_le_right.mp hnormleft)
  refine ⟨hc, ?_⟩
  let := secondModule_elementary F D hne (by omega) (v := base F true) rfl
  let := secondModule_elementary F D hne (by omega) (odd_endpoint_type F D hne hd hodd)
  exact mutual_nested_commutators _ _ hc

end CFSG.Quasithin.ChapterF.Section07.CriticalPairs
