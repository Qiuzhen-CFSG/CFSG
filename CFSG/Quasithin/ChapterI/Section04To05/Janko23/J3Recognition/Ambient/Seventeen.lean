module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen

/-!
# Baumeister's graph on the literal subgroup ⟨L₁,L₂⟩

Set L₂ = N_G(L₁₂), L₃ = ⟨C_{L₁}(f), C_{L₂}(f)⟩, and L = ⟨L₁,L₂⟩,
as on Baumeister pp.496–497. All three local groups are restricted to L
using their actual inclusions. Pairwise intersections, two-cores and their
centralizers are transported through those inclusions. The graph on L/L₁
is connected, and the later graph conclusions use this same action.

`OriginalMarking` retains the genuine preceding source obligations:
L₁₂ = L₁ ∩ N_G(L₁₂), the involution f, the three group identifications,
and their literal intersections. In particular Lemmas 2.5–2.6 are not
inferred from plane data. The parent ambient-recognition task must
construct these markings. Lemma 2.7 and the universal-completion
Corollary 2.8 are proved for that literal subgroup below. The simultaneous embedding
uniqueness of Lemma 2.9 and the resulting marked completion comparison are
proved below. The constructed PSL₂(16):2 model is applied to this original
completion in the `Seventeen.Recognition` extension.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), pp.496–498.
-/

@[expose] public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.Seventeen
open Sporadic.Janko3.SourceRecognition.Seventeen
variable {G : Type*} [Group G]

def second (L12 : Subgroup G) : Subgroup G := normalizer (L12 : Set G)

def third (L1 L12 : Subgroup G) (f : G) : Subgroup G :=
  (L1 ⊓ centralizer ({f} : Set G)) ⊔ (second L12 ⊓ centralizer ({f} : Set G))

def completion (L1 L12 : Subgroup G) : Subgroup G := L1 ⊔ second L12

theorem third_le (L1 L12 : Subgroup G) (f : G) :
    third L1 L12 f ≤ completion L1 L12 :=
  sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

private theorem self_centralizing_core_transport {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (hc : centralizer (pCore 2 K : Set K) = pCore 2 K) :
    centralizer (pCore 2 H : Set H) = pCore 2 H := by
  have he (x : H) : e x ∈ pCore 2 K ↔ x ∈ pCore 2 H := by
    rw [← pCore_map_iso 2 e, mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply]
  ext x
  constructor
  · intro hx
    apply (he x).mp
    rw [← hc]
    intro y hy
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (hx y ((he y).mp hy))
  · intro hx y hy
    have hx' : e x ∈ centralizer (pCore 2 K : Set K) := hc.symm ▸ (he x).mpr hx
    apply e.injective
    rw [map_mul, map_mul]
    exact hx' (e y) ((he y).mpr hy)

structure OriginalMarking (L1 L12 : Subgroup G) (f : G) where
  overlap_le : L12 ≤ L1
  involution_mem : f ∈ L12
  involution_order : orderOf f = 2
  intersection12 : L1 ⊓ second L12 = L12
  action : Complement →* MulAut Plane
  pointEquiv : L1 ≃* Plane ⋊[action] Complement
  core_centralizer : centralizer (pCore 2 L1 : Set L1) = pCore 2 L1
  pairEquiv : second L12 ≃* PairGroup
  triangleEquiv : third L1 L12 f ≃* TriangleGroup
  overlap12 : L12 ≃* Complement
  overlap13 : (L1 ⊓ third L1 L12 f : Subgroup G) ≃*
    (alternatingGroup (Fin 4) × Multiplicative (ZMod 2))
  overlap23 : (second L12 ⊓ third L1 L12 f : Subgroup G) ≃*
    (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))

def intersectionEquiv (L A B : Subgroup G) (hA : A ≤ L) (_hB : B ≤ L) :
    (A.subgroupOf L ⊓ B.subgroupOf L : Subgroup L) ≃* (A ⊓ B : Subgroup G) :=
  (MulEquiv.subgroupCongr (Subgroup.comap_inf A B L.subtype).symm).trans
    (subgroupOfEquivOfLe (inf_le_left.trans hA))

def OriginalMarking.localSource {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) : SourceData (completion L1 L12) where
  H1 := L1.subgroupOf (completion L1 L12)
  H2 := (second L12).subgroupOf (completion L1 L12)
  H3 := (third L1 L12 f).subgroupOf (completion L1 L12)
  generated := by
    change L1.subgroupOf (L1 ⊔ second L12) ⊔ (second L12).subgroupOf (L1 ⊔ second L12) = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  action := M.action
  pointEquiv := (subgroupOfEquivOfLe le_sup_left).trans M.pointEquiv
  core_centralizer := by
    exact self_centralizing_core_transport (subgroupOfEquivOfLe le_sup_left) M.core_centralizer
  pairEquiv := (subgroupOfEquivOfLe le_sup_right).trans M.pairEquiv
  triangleEquiv := (subgroupOfEquivOfLe (third_le L1 L12 f)).trans M.triangleEquiv
  overlap12 := (intersectionEquiv (completion L1 L12) L1 (second L12)
    le_sup_left le_sup_right).trans ((MulEquiv.subgroupCongr M.intersection12).trans M.overlap12)
  overlap13 := (intersectionEquiv (completion L1 L12) L1 (third L1 L12 f)
    le_sup_left (third_le L1 L12 f)).trans M.overlap13
  overlap23 := (intersectionEquiv (completion L1 L12) (second L12) (third L1 L12 f)
    le_sup_right (third_le L1 L12 f)).trans M.overlap23

def OriginalMarking.swapInCompletion {L1 L12 : Subgroup G} {f : G}
    (_M : OriginalMarking L1 L12 f) (b : G) (hb2 : b ∈ second L12) : completion L1 L12 :=
  ⟨b, (show second L12 ≤ completion L1 L12 from le_sup_right) hb2⟩

abbrev OriginalMarking.cosetData {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) (b : G) (hb2 : b ∈ second L12)
    (hb : b * b = 1) (hbout : b ∉ L1) : CosetGraph.Data (completion L1 L12) :=
  M.localSource.cosetData (M.swapInCompletion b hb2) (Subtype.ext hb) hbout

theorem OriginalMarking.connected {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) (b : G) (hb2 : b ∈ second L12)
    (hb : b * b = 1) (hbout : b ∉ L1) :
    (CosetGraph.graph (M.cosetData b hb2 hb hbout)).Connected :=
  M.localSource.connected (M.swapInCompletion b hb2) (Subtype.ext hb) hbout hb2

theorem OriginalMarking.geometric_consequences {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) (b : G) (hb2 : b ∈ second L12)
    (hb : b * b = 1) (hbout : b ∉ L1)
    (h : G) (hh : h ∈ L1) (hcube : (b * h)^3 ∈ L1) :
    let D := M.cosetData b hb2 hb hbout
    FaithfulSMul (completion L1 L12) (CosetGraph.Vertex D) ∧
      (CosetGraph.graph D).Connected ∧ CosetGraph.graph D = ⊤ ∧
      (∀ x : CosetGraph.Vertex D, Nat.card ((CosetGraph.graph D).neighborSet x) = 16) ∧
      Nat.card (CosetGraph.Vertex D) = 17 ∧
      IsMultiplyPretransitive (completion L1 L12) (CosetGraph.Vertex D) 3 ∧
      Nat.card (completion L1 L12) = 8160 := by
  let hL : completion L1 L12 := ⟨h, (show L1 ≤ completion L1 L12 from le_sup_left) hh⟩
  exact M.localSource.consequences_of_cube (M.swapInCompletion b hb2)
    (Subtype.ext hb) hbout hb2 hL hh hcube

/-- The original L contains an outside involution from L₂ ∩ L₃ giving a connected graph. -/
theorem OriginalMarking.exists_connected_graph {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) :
    ∃ (b : completion L1 L12) (hb : b * b = 1) (hbout : (b : G) ∉ L1),
      (b : G) ∈ second L12 ∧ (b : G) ∈ third L1 L12 f ∧
      (CosetGraph.graph (M.localSource.cosetData b hb hbout)).Connected :=
  M.localSource.exists_connected_graph

theorem OriginalMarking.faithful_of_edge {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) (b : G) (hb2 : b ∈ second L12)
    (hb : b * b = 1) (hbout : b ∉ L1)
    (hedge : CosetGraph.edgeStabilizer (M.cosetData b hb2 hb hbout) =
      M.localSource.H2.subgroupOf M.localSource.H1) :
    FaithfulSMul (completion L1 L12) (CosetGraph.Vertex (M.cosetData b hb2 hb hbout)) :=
  M.localSource.faithful_of_edge (M.swapInCompletion b hb2) (Subtype.ext hb) hbout hedge

/-- The connected faithful valency-sixteen graph, on the original completion. -/
theorem OriginalMarking.exists_graph_properties {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) :
    ∃ (b : completion L1 L12) (hb : b * b = 1) (hbout : (b : G) ∉ L1),
      (b : G) ∈ second L12 ∧ (b : G) ∈ third L1 L12 f ∧
      let D := M.localSource.cosetData b hb hbout
      (CosetGraph.graph D).Connected ∧ FaithfulSMul (completion L1 L12) (CosetGraph.Vertex D) ∧
        (∀ x : CosetGraph.Vertex D, Nat.card ((CosetGraph.graph D).neighborSet x) = 16) ∧
        CosetGraph.NeighborTwoTransitive D :=
  M.localSource.exists_graph_properties

/-- Lemma 2.7 on the original L = ⟨L₁,L₂⟩, including both literal stabilizers. -/
theorem OriginalMarking.exists_seventeen_action {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) :
    ∃ (b : completion L1 L12) (hb : b * b = 1) (hbout : (b : G) ∉ L1),
      (b : G) ∈ second L12 ∧ (b : G) ∈ third L1 L12 f ∧
      let D := M.localSource.cosetData b hb hbout
      FaithfulSMul (completion L1 L12) (CosetGraph.Vertex D) ∧
        (CosetGraph.graph D).Connected ∧ CosetGraph.graph D = ⊤ ∧
        (∀ x : CosetGraph.Vertex D, Nat.card ((CosetGraph.graph D).neighborSet x) = 16) ∧
        Nat.card (CosetGraph.Vertex D) = 17 ∧
        IsMultiplyPretransitive (completion L1 L12) (CosetGraph.Vertex D) 3 ∧
        Nat.card (completion L1 L12) = 8160 ∧
        stabilizer (completion L1 L12) (CosetGraph.base D) =
          L1.subgroupOf (completion L1 L12) ∧
        stabilizer (completion L1 L12)
          ({CosetGraph.base D, CosetGraph.other D} : Set (CosetGraph.Vertex D)) =
          (second L12).subgroupOf (completion L1 L12) := by
  obtain ⟨b, hb, hbout, hb2, hb3, hf, hconn, hcomp, hval, hcard, ht, hG⟩ :=
    M.localSource.exists_complete_graph
  exact ⟨b, hb, hbout, hb2, hb3, hf, hconn, hcomp, hval, hcard, ht, hG,
    CosetGraph.point_stabilizer _, M.localSource.setwise_pair_stabilizer b hb hbout hb2⟩

/-- Corollary 2.8 on the original L: its literal local maps extend uniquely. -/
theorem OriginalMarking.universal_completion {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) {K : Type*} [Group K]
    (maps : CompatibleMaps M.localSource K) :
    Nat.card (completion L1 L12) = 8160 ∧
      ∃! j : completion L1 L12 →* K,
        ∀ (i : Fin 3) (x : M.localSource.family i), j x = maps.map i x :=
  M.localSource.corollary_2_8 maps

/-- Completion uniqueness from Lemma 2.9 on the original L = ⟨L₁,L₂⟩,
preserving both literal local subgroups. -/
theorem OriginalMarking.completion_equiv {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) {J : Type*} [Group J] (N : SourceData J) :
    ∃ e : completion L1 L12 ≃* J,
      (L1.subgroupOf (completion L1 L12)).map e.toMonoidHom = N.H1 ∧
      ((second L12).subgroupOf (completion L1 L12)).map e.toMonoidHom = N.H2 :=
  M.localSource.completions_marked_equiv N

/-- The original marked involution as an element of the actual completion. -/
def OriginalMarking.involutionInCompletion {L1 L12 : Subgroup G} {f : G}
    (M : OriginalMarking L1 L12 f) : completion L1 L12 :=
  ⟨f, (show L1 ≤ completion L1 L12 from le_sup_left) (M.overlap_le M.involution_mem)⟩

/-- The original f can be preserved when comparing with a second source
completion. The `Seventeen.Recognition` extension applies this theorem to
the constructed fourth-power-Frobenius model amalgam. -/
theorem OriginalMarking.completion_equiv_preserving_involution
    {L1 L12 : Subgroup G} {f : G} (M : OriginalMarking L1 L12 f)
    {J : Type*} [Group J] (N : SourceData J)
    (t : J) (ht : t ∈ N.H1 ⊓ N.H2) (hot : orderOf t = 2) :
    ∃ e : completion L1 L12 ≃* J,
      (L1.subgroupOf (completion L1 L12)).map e.toMonoidHom = N.H1 ∧
      ((second L12).subgroupOf (completion L1 L12)).map e.toMonoidHom = N.H2 ∧
      e M.involutionInCompletion = t := by
  have hf : f ∈ L1 ⊓ second L12 := by
    rw [M.intersection12]
    exact M.involution_mem
  have ho : orderOf M.involutionInCompletion = 2 := by
    rw [OriginalMarking.involutionInCompletion, Subgroup.orderOf_mk]
    exact M.involution_order
  exact M.localSource.completions_equiv_preserving_involution N
    M.involutionInCompletion hf ho t ht hot

end CFSG.Quasithin.Janko23.J3Recognition.Ambient.Seventeen
