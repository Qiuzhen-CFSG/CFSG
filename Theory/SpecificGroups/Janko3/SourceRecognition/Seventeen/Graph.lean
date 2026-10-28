module
public import Theory.GroupAction.SwappedOrbital
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Index

/-!
# The coset-graph steps in Baumeister's seventeen-point argument

Generation by a point stabilizer and an element swapping an edge implies
connectedness. A doubly transitive neighbor action propagates one triangle
to a clique at every vertex, and connectedness then gives the complete graph.
The original action is triply transitive. Orbit-stabilizer computes the
valency, and a self-centralizing normal subgroup disjoint from the edge
stabilizer proves faithfulness.

The coset specialization uses left cosets internally. Inversion identifies
the source right coset Hx with x⁻¹H, and `adj_iff_source_edge` proves the
literal source edge formula. The word (bh)³ ∈ H constructs an actual triangle.
No finiteness of the ambient group is assumed in these arguments.

These are supporting implications for Baumeister, *A geometry for groups of
J₃-type* (2007), Lemma 2.7, p.497. The local subgroup calculations providing
their hypotheses and the subsequent embedding uniqueness remain separate
obligations; this module does not assert Lemmas 2.7–2.10 from subgroup types.
-/

@[expose] public section
open MulAction Subgroup
namespace Sporadic.Janko3.SourceRecognition.Seventeen

namespace Orbital
variable {G Ω : Type*} [Group G] [MulAction G Ω]
variable (a b : Ω) (hab : a ≠ b) (t : G) (hta : t • a = b) (htb : t • b = a)
local notation "Γ" => SwappedOrbital.graph a b hab t hta htb

theorem connected [IsPretransitive G Ω]
    (hgen : stabilizer G a ⊔ zpowers t = ⊤) : (Γ).Connected := by
  let R : Subgroup G :=
    { carrier := {g | (Γ).Reachable a (g • a)}
      one_mem' := by change (Γ).Reachable a (1 • a); rw [one_smul]
      mul_mem' := by
        intro g h hg hh
        have hm := hh.map (SwappedOrbital.automorphism a b hab t hta htb g).toHom
        change (Γ).Reachable (g • a) (g • (h • a)) at hm
        exact hg.trans (by simpa only [mul_smul] using hm)
      inv_mem' := by
        intro g hg
        have hm := hg.symm.map
          (SwappedOrbital.automorphism a b hab t hta htb g⁻¹).toHom
        change (Γ).Reachable (g⁻¹ • (g • a)) (g⁻¹ • a) at hm
        change (Γ).Reachable a (g⁻¹ • a)
        simpa only [inv_smul_smul] using hm }
  have hs : stabilizer G a ≤ R := by
    intro g hg
    change (Γ).Reachable a (g • a)
    rw [show g • a = a from hg]
  have ht : zpowers t ≤ R := by
    apply zpowers_le.mpr
    change (Γ).Reachable a (t • a)
    rw [hta]
    exact SimpleGraph.Adj.reachable ⟨1, one_smul _ _, one_smul _ _⟩
  have hR : R = ⊤ := top_unique (hgen ▸ sup_le hs ht)
  have ha (x : Ω) : (Γ).Reachable a x := by
    obtain ⟨g, rfl⟩ := exists_smul_eq G a x
    exact show g ∈ R from hR ▸ mem_top g
  let : Nonempty Ω := ⟨a⟩
  exact ⟨fun x y => (ha x).symm.trans (ha y)⟩

def NeighborTwoTransitive : Prop :=
  ∀ x y u v : Ω, (Γ).Adj a x → (Γ).Adj a y → (Γ).Adj a u → (Γ).Adj a v →
    x ≠ y → u ≠ v → ∃ g : stabilizer G a, (g : G) • x = u ∧ (g : G) • y = v

theorem complete_of_triangle [IsPretransitive G Ω]
    (hgen : stabilizer G a ⊔ zpowers t = ⊤)
    (htwo : NeighborTwoTransitive a b hab t hta htb)
    (c : Ω) (hac : (Γ).Adj a c) (hbc : (Γ).Adj b c) : Γ = ⊤ := by
  have hab' : (Γ).Adj a b := ⟨1, one_smul _ _, one_smul _ _⟩
  have hbase : ∀ x y, (Γ).Adj a x → (Γ).Adj a y → x ≠ y → (Γ).Adj x y := by
    intro x y hx hy hxy
    obtain ⟨g, hgx, hgy⟩ := htwo b c x y hab' hac hx hy hbc.ne hxy
    rw [← hgx, ← hgy]
    exact (SwappedOrbital.adj_smul_iff a b hab t hta htb g b c).mpr hbc
  have hclique : ∀ x y z, (Γ).Adj x y → (Γ).Adj x z → y ≠ z → (Γ).Adj y z := by
    intro x y z hxy hxz hyz
    obtain ⟨g, rfl⟩ := exists_smul_eq G a x
    have hy := (SwappedOrbital.adj_smul_iff a b hab t hta htb g⁻¹ (g • a) y).mpr hxy
    have hz := (SwappedOrbital.adj_smul_iff a b hab t hta htb g⁻¹ (g • a) z).mpr hxz
    simp only [inv_smul_smul] at hy hz
    have he := hbase _ _ hy hz ((MulAction.injective g⁻¹).ne hyz)
    have hf := (SwappedOrbital.adj_smul_iff a b hab t hta htb g _ _).mpr he
    simpa only [smul_inv_smul] using hf
  have hwalk : ∀ {x y}, (Γ).Walk x y → x = y ∨ (Γ).Adj x y := by
    intro x y p
    induction p with
    | nil => exact Or.inl rfl
    | @cons x u y hxu p ih =>
      rcases ih with rfl | huy
      · exact Or.inr hxu
      · by_cases hxy : x = y
        · exact Or.inl hxy
        · exact Or.inr (hclique u x y hxu.symm huy hxy)
  ext x y
  change (Γ).Adj x y ↔ x ≠ y
  refine ⟨fun h => h.ne, fun h => ?_⟩
  obtain ⟨p⟩ := connected a b hab t hta htb hgen x y
  exact (hwalk p).resolve_left h

theorem triply_transitive [IsPretransitive G Ω]
    (hgen : stabilizer G a ⊔ zpowers t = ⊤)
    (htwo : NeighborTwoTransitive a b hab t hta htb)
    (c : Ω) (hac : (Γ).Adj a c) (hbc : (Γ).Adj b c) :
    IsMultiplyPretransitive G Ω 3 := by
  have hc := complete_of_triangle a b hab t hta htb hgen htwo c hac hbc
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive (a := a) (n := 2)).mpr
  apply is_two_pretransitive_iff.mpr
  intro x y u v hxy huv
  have hn (x : SubMulAction.ofStabilizer G a) : (Γ).Adj a x := by
    rw [hc]
    exact (show (x : Ω) ≠ a from x.property).symm
  obtain ⟨g, hgx, hgy⟩ := htwo x y u v (hn x) (hn y) (hn u) (hn v)
    (fun h => hxy (Subtype.ext h)) (fun h => huv (Subtype.ext h))
  exact ⟨g, Subtype.ext hgx, Subtype.ext hgy⟩

theorem card_of_complete (hc : Γ = ⊤) (n : ℕ)
    (hcard : Nat.card ((Γ).neighborSet a) = n) (hn : n ≠ 0) : Nat.card Ω = n + 1 := by
  classical
  have he : ((Γ).neighborSet a) ≃ {x : Ω // x ≠ a} :=
    Equiv.subtypeEquivRight (fun x => by simp only [hc, SimpleGraph.mem_neighborSet,
      SimpleGraph.top_adj, ne_comm])
  have hfin : Finite {x : Ω // x ≠ a} := Nat.finite_of_card_ne_zero (by
    rw [← Nat.card_congr he, hcard]
    exact hn)
  let : Fintype {x : Ω // x ≠ a} := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.optionSubtypeNe a), Nat.card_eq_fintype_card,
    Fintype.card_option, ← Nat.card_eq_fintype_card, ← Nat.card_congr he, hcard]

end Orbital

namespace CosetGraph
variable {G : Type*} [Group G]

/-- A subgroup and an outside involution determine the source coset graph. -/
structure Data (G : Type*) [Group G] where
  point : Subgroup G
  swap : G
  square : swap * swap = 1
  outside : swap ∉ point

variable (D : Data G)

abbrev Vertex := G ⧸ D.point
def base : Vertex D := (1 : G)
def other : Vertex D := D.swap

theorem base_ne_other : base D ≠ other D := by
  intro h
  exact D.outside (by simpa [base, other, QuotientGroup.eq] using h)

theorem swap_base : D.swap • base D = other D := by
  change ((D.swap * 1 : G) : Vertex D) = _
  rw [mul_one]
  rfl

theorem swap_other : D.swap • other D = base D := by
  change ((D.swap * D.swap : G) : Vertex D) = _
  rw [D.square]
  rfl

def graph : SimpleGraph (Vertex D) := SwappedOrbital.graph (base D) (other D)
  (base_ne_other D) D.swap (swap_base D) (swap_other D)

def rightVertex (x : G) : Vertex D := (x⁻¹ : G)

theorem rightVertex_eq_iff (x y : G) :
    rightVertex D x = rightVertex D y ↔ x * y⁻¹ ∈ D.point := by
  simp only [rightVertex, QuotientGroup.eq, inv_inv]

theorem source_edge (x : G) : (graph D).Adj (rightVertex D x) (rightVertex D (D.swap * x)) := by
  refine ⟨x⁻¹, ?_, ?_⟩
  · change ((x⁻¹ * 1 : G) : Vertex D) = _
    rw [mul_one]
    rfl
  · have hi : D.swap⁻¹ = D.swap := inv_eq_of_mul_eq_one_right D.square
    change ((x⁻¹ * D.swap : G) : Vertex D) = (((D.swap * x)⁻¹ : G) : Vertex D)
    rw [mul_inv_rev, hi]

theorem adj_iff_source_edge (v w : Vertex D) :
    (graph D).Adj v w ↔ ∃ x : G, rightVertex D x = v ∧ rightVertex D (D.swap * x) = w := by
  constructor
  · rintro ⟨g, rfl, rfl⟩
    refine ⟨g⁻¹, ?_, ?_⟩
    · change (((g⁻¹)⁻¹ : G) : Vertex D) = ((g * 1 : G) : Vertex D)
      rw [inv_inv, mul_one]
    · have hi : D.swap⁻¹ = D.swap := inv_eq_of_mul_eq_one_right D.square
      change (((D.swap * g⁻¹)⁻¹ : G) : Vertex D) = ((g * D.swap : G) : Vertex D)
      rw [mul_inv_rev, inv_inv, hi]
  · rintro ⟨x, rfl, rfl⟩
    exact source_edge D x

theorem connected (hgen : D.point ⊔ zpowers D.swap = ⊤) : (graph D).Connected := by
  apply Orbital.connected
  simpa only [base, stabilizer_quotient] using hgen

theorem generation_of_index_two (K : Subgroup G) (hb : D.swap ∈ K)
    (hi : (D.point.subgroupOf K).index = 2) (hgen : D.point ⊔ K = ⊤) :
    D.point ⊔ zpowers D.swap = ⊤ := by
  apply top_unique
  rw [← hgen]
  refine sup_le le_sup_left ?_
  intro x hx
  by_cases hp : x ∈ D.point
  · exact (show D.point ≤ D.point ⊔ zpowers D.swap from le_sup_left) hp
  · have hm : (⟨D.swap, hb⟩ : K) * ⟨x, hx⟩ ∈ D.point.subgroupOf K := by
      rw [mul_mem_iff_of_index_two hi]
      exact iff_of_false D.outside hp
    have hh : D.swap * x ∈ D.point := hm
    have hb' : D.swap ∈ D.point ⊔ zpowers D.swap  := (show zpowers D.swap ≤ D.point ⊔ zpowers D.swap from le_sup_right) (mem_zpowers _)
    simpa only [← mul_assoc, D.square, one_mul] using
      (D.point ⊔ zpowers D.swap).mul_mem hb' ((show D.point ≤ D.point ⊔ zpowers D.swap from le_sup_left) hh)

def edgeStabilizer : Subgroup D.point := stabilizer D.point (other D)

theorem point_stabilizer : stabilizer G (base D) = D.point := stabilizer_quotient _

theorem neighbor_card_mul_edge :
    Nat.card ((graph D).neighborSet (base D)) * Nat.card (edgeStabilizer D) =
      Nat.card D.point := by
  rw [graph, SwappedOrbital.neighbor_base, point_stabilizer]
  exact (Nat.card_prod _ _).symm.trans
    (Nat.card_congr (orbitProdStabilizerEquivGroup D.point (other D)))

theorem valency_sixteen (hp : Nat.card D.point = 480)
    (he : Nat.card (edgeStabilizer D) = 30) :
    ∀ x : Vertex D, Nat.card ((graph D).neighborSet x) = 16 := by
  have hb := neighbor_card_mul_edge D
  rw [hp, he] at hb
  have hb' : Nat.card ((graph D).neighborSet (base D)) = 16 := by omega
  intro x
  obtain ⟨g, rfl⟩ := exists_smul_eq G (base D) x
  exact (Nat.card_congr (SwappedOrbital.neighborsEquiv (base D) (other D)
    (base_ne_other D) D.swap (swap_base D) (swap_other D) g (base D))).symm.trans hb'

theorem faithful_of_self_centralizing (V : Subgroup D.point) [V.Normal]
    (hcent : centralizer (V : Set D.point) ≤ V)
    (hdis : Disjoint (edgeStabilizer D) V) : FaithfulSMul G (Vertex D) := by
  let N := D.point.normalCore.subgroupOf D.point
  have hNE : N ≤ edgeStabilizer D := by
    intro x hx
    have hk : (x : G) ∈ (toPermHom G (Vertex D)).ker := by
      rw [← D.point.normalCore_eq_ker]
      exact hx
    exact Equiv.Perm.ext_iff.mp hk (other D)
  have hd : Disjoint N V := hdis.mono_left hNE
  have hc : N ≤ centralizer (V : Set D.point) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
  have hn : N = ⊥ := by
    apply bot_unique
    intro x hx
    exact hd.le_bot ⟨hx, hcent (hc hx)⟩
  rw [faithfulSMul_iff]
  intro g hg
  have hk : g ∈ D.point.normalCore := by
    rw [D.point.normalCore_eq_ker]
    exact Equiv.Perm.ext hg
  have hx : (⟨g, D.point.normalCore_le hk⟩ : D.point) ∈ N := hk
  rw [hn] at hx
  exact congrArg Subtype.val hx

theorem triangle_of_cube (h : G) (hh : h ∈ D.point) (hcube : (D.swap * h)^3 ∈ D.point) :
    ∃ c : Vertex D, (graph D).Adj (base D) c ∧ (graph D).Adj (other D) c := by
  let c : Vertex D := (D.swap * h * D.swap : G)
  have he : ((h⁻¹ * D.swap : G) : Vertex D) = c := by
    apply QuotientGroup.eq.mpr
    have hi : D.swap⁻¹ = D.swap := inv_eq_of_mul_eq_one_right D.square
    have hw : (h⁻¹ * D.swap)⁻¹ * (D.swap * h * D.swap) = (D.swap * h)^3 * h⁻¹ := by
      rw [mul_inv_rev, inv_inv, hi]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [hw]
    exact D.point.mul_mem hcube (D.point.inv_mem hh)
  refine ⟨c, ⟨h⁻¹, ?_, ?_⟩, ⟨D.swap * h, ?_, ?_⟩⟩
  · change ((h⁻¹ * 1 : G) : Vertex D) = ((1 : G) : Vertex D)
    rw [mul_one, QuotientGroup.eq]
    simpa only [inv_inv, mul_one] using hh
  · exact he
  · change ((D.swap * h * 1 : G) : Vertex D) = (D.swap : Vertex D)
    rw [mul_one, QuotientGroup.eq]
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using D.point.inv_mem hh
  · rfl

def NeighborTwoTransitive : Prop :=
  Orbital.NeighborTwoTransitive (base D) (other D) (base_ne_other D)
    D.swap (swap_base D) (swap_other D)

theorem consequences (hgen : D.point ⊔ zpowers D.swap = ⊤)
    (htwo : NeighborTwoTransitive D)
    (h : G) (hh : h ∈ D.point) (hcube : (D.swap * h)^3 ∈ D.point)
    (hp : Nat.card D.point = 480) (he : Nat.card (edgeStabilizer D) = 30) :
    (graph D).Connected ∧ (graph D) = ⊤ ∧
      (∀ x : Vertex D, Nat.card ((graph D).neighborSet x) = 16) ∧
      Nat.card (Vertex D) = 17 ∧ IsMultiplyPretransitive G (Vertex D) 3 ∧
      Nat.card G = 8160 := by
  obtain ⟨c, hac, hbc⟩ := triangle_of_cube D h hh hcube
  have hg : stabilizer G (base D) ⊔ zpowers D.swap = ⊤ := by
    rw [point_stabilizer]
    exact hgen
  have hcomplete := Orbital.complete_of_triangle (base D) (other D) (base_ne_other D)
    D.swap (swap_base D) (swap_other D) hg htwo c hac hbc
  have hval := valency_sixteen D hp he
  have hcard : Nat.card (Vertex D) = 17 := Orbital.card_of_complete
    (base D) (other D) (base_ne_other D) D.swap (swap_base D) (swap_other D)
    hcomplete 16 (hval _) (by decide)
  refine ⟨connected D hgen, hcomplete, hval, hcard,
    Orbital.triply_transitive (base D) (other D) (base_ne_other D)
      D.swap (swap_base D) (swap_other D) hg htwo c hac hbc, ?_⟩
  have horder := D.point.card_mul_index
  rw [hp, index_eq_card, hcard] at horder
  exact horder.symm

end CosetGraph

end Sporadic.Janko3.SourceRecognition.Seventeen
