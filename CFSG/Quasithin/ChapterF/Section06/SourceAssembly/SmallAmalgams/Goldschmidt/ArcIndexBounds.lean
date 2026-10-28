module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralIntervals

/-!
# Cubic edge stabilizer index bounds

Each one-edge extension has at most two possible images under its preceding
arc stabilizer. A relative-index triangle inequality then bounds the index
between edge stabilizers separated by `n` steps by `2^n`, without regularity.
This is the edge-level estimate needed for the normal two-core centralizer
bound in Goldschmidt (6.3), printed p.397.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem relIndex_triangle (A B C : Subgroup G) [Finite B] [Finite C] :
    A.relIndex C ≤ A.relIndex B * B.relIndex C := by
  calc
    A.relIndex C ≤ (A ⊓ B).relIndex C :=
      Subgroup.relIndex_le_of_le_left inf_le_left ((A ⊓ B).subgroupOf C).index_ne_zero_of_finite
    _ = A.relIndex (B ⊓ C) * B.relIndex C :=
      (Subgroup.relIndex_inf_mul_relIndex A B C).symm
    _ ≤ A.relIndex B * B.relIndex C :=
      Nat.mul_le_mul_right _
        (Subgroup.relIndex_le_of_le_right inf_le_left (A.subgroupOf B).index_ne_zero_of_finite)

theorem CubicTreeAction.pathStabilizer_snoc_index_le_two (h : CubicTreeAction F)
    {n : ℕ} {v z : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) (n + 1) v)
    (hz : Theory.GroupAction.CubicTree.Forward p z) :
    (RankTwo.pathStabilizer F (p.snoc (forward_adj p hz))).relIndex
      (RankTwo.pathStabilizer F p) ≤ 2 := by
  have he : (RankTwo.pathStabilizer F (p.snoc (forward_adj p hz))).subgroupOf
      (RankTwo.pathStabilizer F p) =
      MulAction.stabilizer (RankTwo.pathStabilizer F p) z := by
    ext a
    rw [pathStabilizer_snoc]
    change ((a : G) ∈ RankTwo.pathStabilizer F p ∧ (a : G) • z = z) ↔
      (a : G) • z = z
    exact and_iff_right a.property
  rw [Subgroup.relIndex, he, MulAction.index_stabilizer]
  have hc := card_forward_of_cubic p (h.card_neighbor p.endpoint)
  have hf : Finite {w | Theory.GroupAction.CubicTree.Forward p w} :=
    Nat.finite_of_card_ne_zero (hc ▸ by decide)
  have hi : MulAction.orbit (RankTwo.pathStabilizer F p) z ⊆
      {w | Theory.GroupAction.CubicTree.Forward p w} := by
    rintro w ⟨a, rfl⟩
    exact forward_smul_of_fixes trackGraphAction p a a.property hz
  exact (Set.ncard_le_ncard hi (Set.toFinite _)).trans_eq
    ((Nat.card_coe_set_eq _).symm.trans hc)

theorem CubicTreeAction.edgeStabilizer_next_index_le_two (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (i : ℤ) :
    (t.edgeStabilizer i).relIndex (t.edgeStabilizer (i + 1)) ≤ 2 := by
  have hcb := (t.adjacent (i + 1)).symm
  let p : BasedWalk (RankTwo.graph F) 1 (t.vertex (i + 1 + 1)) :=
    ⟨⟨t.vertex (i + 1), hcb⟩, PUnit.unit⟩
  have hz : Theory.GroupAction.CubicTree.Forward p (t.vertex i) := by
    refine ⟨(t.adjacent i).symm, ?_⟩
    intro he
    have hi := t.injective he
    omega
  have hi := h.pathStabilizer_snoc_index_le_two p hz
  have he : RankTwo.pathStabilizer F p = t.edgeStabilizer (i + 1) := by
    ext a
    change (∀ y ∈ [t.vertex (i + 1 + 1), t.vertex (i + 1)], a • y = y) ↔
      a • t.vertex (i + 1) = t.vertex (i + 1) ∧
        a • t.vertex (i + 1 + 1) = t.vertex (i + 1 + 1)
    simp [and_comm]
  rw [pathStabilizer_snoc, he] at hi
  have he' : t.edgeStabilizer (i + 1) ⊓ RankTwo.stabilizer F (t.vertex i) =
      t.edgeStabilizer i ⊓ t.edgeStabilizer (i + 1) := by
    ext a
    change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
    aesop
  rw [he', Subgroup.inf_relIndex_right] at hi
  exact hi

theorem CubicTreeAction.edgeStabilizer_index_le_pow (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) (i : ℤ) (n : ℕ) :
    (t.edgeStabilizer i).relIndex (t.edgeStabilizer (i + n)) ≤ 2 ^ n := by
  let : ∀ j, Finite (F j) := h.finite
  have hf (j : ℤ) : Finite (t.edgeStabilizer j) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero, Subgroup.relIndex_self, pow_zero, le_refl]
  | succ n ih =>
    have he : i + ((n + 1 : ℕ) : ℤ) = (i + n) + 1 := by omega
    rw [he, pow_succ]
    exact (relIndex_triangle _ (t.edgeStabilizer (i + n)) _).trans
      (Nat.mul_le_mul ih (h.edgeStabilizer_next_index_le_two t (i + n)))

/-- Centrality on the initial edge bounds the centralizer index in every
subgroup of the final edge stabilizer. -/
theorem CubicTreeAction.centralizer_relIndex_le_pow_of_edge (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {z : G} {i : ℤ}
    (hz : t.CentralEdge z i) (n : ℕ) (Q : Subgroup G)
    (hQ : Q ≤ t.edgeStabilizer (i + n)) :
    (centralizer ({z} : Set G)).relIndex Q ≤ 2 ^ n := by
  let : ∀ j, Finite (F j) := h.finite
  have hf : Finite (t.edgeStabilizer (i + n)) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hfQ : Finite Q :=
    Finite.of_injective (Subgroup.inclusion hQ) (Subgroup.inclusion_injective _)
  have hc : t.edgeStabilizer i ≤ centralizer ({z} : Set G) := by
    intro x hx y hy
    have he : y = z := Set.mem_singleton_iff.mp hy
    subst y
    exact (hz.2 x hx).eq
  exact (Subgroup.relIndex_le_of_le_left hc
      ((t.edgeStabilizer i).subgroupOf Q).index_ne_zero_of_finite).trans
    ((Subgroup.relIndex_le_of_le_right hQ
      ((t.edgeStabilizer i).subgroupOf (t.edgeStabilizer (i + n))).index_ne_zero_of_finite).trans
        (h.edgeStabilizer_index_le_pow t i n))

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
