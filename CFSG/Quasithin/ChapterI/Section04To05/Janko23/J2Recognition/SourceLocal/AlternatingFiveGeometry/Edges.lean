module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.AlternatingFiveGeometry.Vertices
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Completion
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdges

/-!
# Marked local edges and both triangle types for J₂ recognition

The intrinsic cubic-pair geometry of A₅ is restricted to the literal
subgroups of K and mapped back into G. This proves trivial pointwise-edge
overlap, a cyclic setwise overlap with its embedded reversing generator,
and transitivity on the ordered edges of the induced local graph.

The two constructed third vertices carry actual K-conjugating witnesses.
Their ambient joins are respectively the edge A₄ and K itself, so even
the ambient setwise edge stabilizer cannot fuse them. The final adapters
apply these facts to `EdgeFrame.K = C_G(B)` using `endpoints_le`, and to the
literal `LocalData.toSystem.localEdge` relation. The frame's A₅ model
identification remains the explicit, independent prime-local input.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6 and 47.10,
pp.264, 266–267. This supplies the finite A₅ inputs to the source local
assembly; it does not assert the full ambient two-orbit theorem of 47.6.
-/

@[expose] public section

open scoped Pointwise
open Subgroup Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
open alternatingGroup.FiveLocalGeometry
namespace AlternatingFiveGeometry
variable {G : Type*} [Group G] [Finite G]
variable (D : Seed G) (K : Subgroup G)

omit [Finite G] in
private theorem card_subgroupOf (A : Subgroup G) (hA : Nat.card A = 3) (hAK : A ≤ K) :
    Nat.card (A.subgroupOf K) = 3 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv, hA]

/-- Restriction preserves the actual join and its embedding into G. -/
noncomputable def joinSubgroupOfEquiv (A B : Subgroup G) (hA : A ≤ K) (hB : B ≤ K) :
    ↥(A.subgroupOf K ⊔ B.subgroupOf K) ≃* ↥(A ⊔ B) :=
  ((A.subgroupOf K ⊔ B.subgroupOf K).equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB]))

omit [Finite G] in
private theorem conj_subgroupOf_iff (A B : Subgroup G) (hA : A ≤ K) (hB : B ≤ K)
    (g : K) :
    (A.subgroupOf K).map (MulAut.conj g).toMonoidHom = B.subgroupOf K ↔
      A.map (MulAut.conj (g : G)).toMonoidHom = B := by
  change MulAut.conj g • A.subgroupOf K = B.subgroupOf K ↔ _
  rw [conj_smul_subgroupOf hA g]
  constructor
  · intro h
    have hm := congrArg (fun P : Subgroup K => P.map K.subtype) h
    rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le hA g), map_subgroupOf_eq_of_le hB] at hm
    exact hm
  · intro h
    change (A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf K = _
    rw [h]

private theorem vertex_smul_iff (A B : D.Vertex) (hA : A.val ≤ K) (hB : B.val ≤ K)
    (g : K) :
    (g : G) • A = B ↔ (A.val.subgroupOf K).map (MulAut.conj g).toMonoidHom =
      B.val.subgroupOf K := by
  rw [Subtype.ext_iff, D.smul_val, conj_subgroupOf_iff K A.val B.val hA hB g]

/-- This discharges the trivial local pointwise-edge overlap in 47.10. -/
theorem edgeFixer_eq_bot (eK : K ≃* alternatingGroup (Fin 5))
    (Y : D.Vertex) (hXY : D.graph.Adj D.base Y) (hX : D.X ≤ K) (hY : Y.val ≤ K) :
    K ⊓ edgeFixer G D.base Y = ⊥ := by
  obtain ⟨eJ⟩ := (D.graph_adj_iff D.base Y).mp hXY
  rw [edgeFixer_overlap D K Y hX hY,
    CubicEdges.normalizer_inf_eq_bot eK _ _
      (card_subgroupOf K D.X D.card_X hX) (card_subgroupOf K Y.val (D.vertex_card Y) hY)
      ((joinSubgroupOfEquiv K D.X Y.val hX hY).trans eJ), Subgroup.map_bot]

/-- Every contained ordered edge has an actual K transporter from the marked edge. -/
theorem ordered_edge_transitive (eK : K ≃* alternatingGroup (Fin 5))
    (Y : D.Vertex) (hXY : D.graph.Adj D.base Y) (hX : D.X ≤ K) (hY : Y.val ≤ K)
    (A B : D.Vertex) (hAB : D.graph.Adj A B) (hA : A.val ≤ K) (hB : B.val ≤ K) :
    ∃ g : K, (g : G) • D.base = A ∧ (g : G) • Y = B := by
  obtain ⟨eXY⟩ := (D.graph_adj_iff D.base Y).mp hXY
  obtain ⟨eAB⟩ := (D.graph_adj_iff A B).mp hAB
  obtain ⟨g, hg, hg'⟩ := CubicEdges.ordered_edge_transitive eK
    (D.X.subgroupOf K) (Y.val.subgroupOf K) (A.val.subgroupOf K) (B.val.subgroupOf K)
    (card_subgroupOf K D.X D.card_X hX) (card_subgroupOf K Y.val (D.vertex_card Y) hY)
    (card_subgroupOf K A.val (D.vertex_card A) hA) (card_subgroupOf K B.val (D.vertex_card B) hB)
    ((joinSubgroupOfEquiv K D.X Y.val hX hY).trans eXY)
    ((joinSubgroupOfEquiv K A.val B.val hA hB).trans eAB)
  exact ⟨g, (vertex_smul_iff D K D.base A hX hA g).mpr hg,
    (vertex_smul_iff D K Y B hY hB g).mpr hg'⟩

/-- A reversing involution lies in the actual K. -/
theorem exists_edge_reversal (eK : K ≃* alternatingGroup (Fin 5))
    (Y : D.Vertex) (hXY : D.graph.Adj D.base Y) (hX : D.X ≤ K) (hY : Y.val ≤ K) :
    ∃ t : K, orderOf t = 2 ∧ (t : G) • D.base = Y ∧ (t : G) • Y = D.base := by
  obtain ⟨eJ⟩ := (D.graph_adj_iff D.base Y).mp hXY
  obtain ⟨t, ht, hx, hy⟩ := CubicEdges.exists_reversal eK
    (D.X.subgroupOf K) (Y.val.subgroupOf K)
    (card_subgroupOf K D.X D.card_X hX) (card_subgroupOf K Y.val (D.vertex_card Y) hY)
    ((joinSubgroupOfEquiv K D.X Y.val hX hY).trans eJ)
  exact ⟨t, ht, (vertex_smul_iff D K D.base Y hX hY t).mpr hx,
    (vertex_smul_iff D K Y D.base hY hX t).mpr hy⟩

/-- The unordered K-edge orbit is exactly the induced edge relation inside K. -/
theorem edge_orbit_iff (eK : K ≃* alternatingGroup (Fin 5))
    (Y : D.Vertex) (hXY : D.graph.Adj D.base Y) (hX : D.X ≤ K) (hY : Y.val ≤ K)
    (A B : D.Vertex) :
    (∃ g : K, ((g : G) • D.base = A ∧ (g : G) • Y = B) ∨
      ((g : G) • D.base = B ∧ (g : G) • Y = A)) ↔
      D.graph.Adj A B ∧ A.val ≤ K ∧ B.val ≤ K := by
  constructor
  · rintro ⟨g, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨D.preserves g hXY, conj_smul_le_of_le hX g, conj_smul_le_of_le hY g⟩
    · exact ⟨(D.preserves g hXY).symm, conj_smul_le_of_le hY g, conj_smul_le_of_le hX g⟩
  · rintro ⟨hAB, hA, hB⟩
    obtain ⟨g, hx, hy⟩ := ordered_edge_transitive D K eK Y hXY hX hY A B hAB hA hB
    exact ⟨g, Or.inl ⟨hx, hy⟩⟩

private theorem mem_edgeStabilizer_iff (Y : D.Vertex) (hX : D.X ≤ K) (hY : Y.val ≤ K)
    (g : K) :
    (g : G) ∈ edgeStabilizer G D.base Y ↔
      g ∈ CubicEdges.pairStabilizer (D.X.subgroupOf K) (Y.val.subgroupOf K) := by
  change (((g : G) • D.base = D.base ∧ (g : G) • Y = Y) ∨
    ((g : G) • D.base = Y ∧ (g : G) • Y = D.base)) ↔ _
  rw [vertex_smul_iff D K D.base D.base hX hX g, vertex_smul_iff D K Y Y hY hY g,
    vertex_smul_iff D K D.base Y hX hY g, vertex_smul_iff D K Y D.base hY hX g]
  rfl

/-- The restriction equivalence preserves the literal ambient embedding. -/
def edgeOverlapEquiv (Y : D.Vertex) (hX : D.X ≤ K) (hY : Y.val ≤ K) :
    ↥(K ⊓ edgeStabilizer G D.base Y) ≃*
      CubicEdges.pairStabilizer (D.X.subgroupOf K) (Y.val.subgroupOf K) where
  toFun g := ⟨⟨g, g.property.1⟩, by
    exact (mem_edgeStabilizer_iff D K Y hX hY _).mp g.property.2⟩
  invFun g := ⟨g, ⟨g.val.property, by
    exact (mem_edgeStabilizer_iff D K Y hX hY _).mpr g.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem edgeOverlapEquiv_coe (Y : D.Vertex) (hX : D.X ≤ K) (hY : Y.val ≤ K)
    (g : ↥(K ⊓ edgeStabilizer G D.base Y)) :
    (((edgeOverlapEquiv D K Y hX hY g :
      CubicEdges.pairStabilizer (D.X.subgroupOf K) (Y.val.subgroupOf K)) : K) : G) = g := rfl

/-- The actual overlap is C₂ and is generated by its reversing element. -/
theorem exists_edgeStabilizer_equiv (eK : K ≃* alternatingGroup (Fin 5))
    (Y : D.Vertex) (hXY : D.graph.Adj D.base Y) (hX : D.X ≤ K) (hY : Y.val ≤ K) :
    ∃ t : K, ∃ d : Multiplicative (ZMod 2) ≃* ↥(K ⊓ edgeStabilizer G D.base Y),
      (d (Multiplicative.ofAdd 1) : G) = t ∧ orderOf t = 2 ∧
      (t : G) • D.base = Y ∧ (t : G) • Y = D.base ∧
      K ⊓ edgeStabilizer G D.base Y = zpowers (t : G) := by
  obtain ⟨eJ⟩ := (D.graph_adj_iff D.base Y).mp hXY
  obtain ⟨t, d, hd, ht, hp, hq, he⟩ := CubicEdges.exists_pairStabilizer_equiv eK
    (D.X.subgroupOf K) (Y.val.subgroupOf K)
    (card_subgroupOf K D.X D.card_X hX) (card_subgroupOf K Y.val (D.vertex_card Y) hY)
    ((joinSubgroupOfEquiv K D.X Y.val hX hY).trans eJ)
  refine ⟨t, d.trans (edgeOverlapEquiv D K Y hX hY).symm,
    congrArg Subtype.val hd, ht, (vertex_smul_iff D K D.base Y hX hY t).mpr hp,
    (vertex_smul_iff D K Y D.base hY hX t).mpr hq, ?_⟩
  have hm : (CubicEdges.pairStabilizer (D.X.subgroupOf K) (Y.val.subgroupOf K)).map
      K.subtype = K ⊓ edgeStabilizer G D.base Y := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, (mem_edgeStabilizer_iff D K Y hX hY a).mpr ha⟩
    · rintro ⟨hg, hs⟩
      exact ⟨⟨g, hg⟩, (mem_edgeStabilizer_iff D K Y hX hY _).mp hs, rfl⟩
  rw [← hm, he, MonoidHom.map_zpowers]
  rfl

/-- Actual K-elements witnessing the two remaining ordered edges of a triangle. -/
def TriangleWitnesses (Y T : D.Vertex) : Prop :=
  (∃ g : K, (g : G) • D.base = Y ∧ (g : G) • Y = T) ∧
  (∃ g : K, (g : G) • D.base = T ∧ (g : G) • Y = D.base)

/-- Both triangle types lie in the literal local group; their ambient joins differ. -/
theorem exists_two_triangles (eK : K ≃* alternatingGroup (Fin 5))
    (Y : D.Vertex) (hXY : D.graph.Adj D.base Y) (hX : D.X ≤ K) (hY : Y.val ≤ K) :
    ∃ T₁ T₂ : D.Vertex, T₁.val ≤ K ∧ T₂.val ≤ K ∧
      TriangleWitnesses D K Y T₁ ∧ TriangleWitnesses D K Y T₂ ∧
      (D.X ⊔ Y.val) ⊔ T₁.val = D.X ⊔ Y.val ∧
      (D.X ⊔ Y.val) ⊔ T₂.val = K ∧ T₁ ≠ T₂ := by
  obtain ⟨eJ⟩ := (D.graph_adj_iff D.base Y).mp hXY
  obtain ⟨U, V, hU, hV, hu, hv, hs, hl, hne⟩ := CubicEdges.exists_two_triangles eK
    (D.X.subgroupOf K) (Y.val.subgroupOf K)
    (card_subgroupOf K D.X D.card_X hX) (card_subgroupOf K Y.val (D.vertex_card Y) hY)
    ((joinSubgroupOfEquiv K D.X Y.val hX hY).trans eJ)
  have cubic (W : Subgroup K) (hW : Nat.card W = 3) : Nat.card (W.map K.subtype) = 3 := by
    rw [card_map_of_injective K.subtype_injective, hW]
  let T₁ : D.Vertex := ⟨U.map K.subtype, mem_vertex_of_card_three D K eK hX _
    (cubic U hU) (map_subtype_le U)⟩
  let T₂ : D.Vertex := ⟨V.map K.subtype, mem_vertex_of_card_three D K eK hX _
    (cubic V hV) (map_subtype_le V)⟩
  have hT₁ : T₁.val.subgroupOf K = U := comap_map_eq_self_of_injective K.subtype_injective U
  have hT₂ : T₂.val.subgroupOf K = V := comap_map_eq_self_of_injective K.subtype_injective V
  have lift (W : Subgroup K) (T : D.Vertex) (hT : T.val ≤ K)
      (he : T.val.subgroupOf K = W) (hw : CubicEdges.TriangleEdges (D.X.subgroupOf K)
        (Y.val.subgroupOf K) W) : TriangleWitnesses D K Y T := by
    obtain ⟨⟨g, hg, hg'⟩, ⟨k, hk, hk'⟩⟩ := hw
    refine ⟨⟨g, (vertex_smul_iff D K D.base Y hX hY g).mpr hg, ?_⟩,
      ⟨k, ?_, (vertex_smul_iff D K Y D.base hY hX k).mpr hk'⟩⟩
    · apply (vertex_smul_iff D K Y T hY hT g).mpr
      rwa [he]
    · apply (vertex_smul_iff D K D.base T hX hT k).mpr
      rwa [he]
  refine ⟨T₁, T₂, map_subtype_le U, map_subtype_le V,
    lift U T₁ (map_subtype_le U) hT₁ hu, lift V T₂ (map_subtype_le V) hT₂ hv, ?_, ?_, ?_⟩
  · have hm := congrArg (fun W : Subgroup K => W.map K.subtype) hs
    simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hX,
      map_subgroupOf_eq_of_le hY] using hm
  · have hm := congrArg (fun W : Subgroup K => W.map K.subtype) hl
    simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hX,
      map_subgroupOf_eq_of_le hY, ← MonoidHom.range_eq_map, range_subtype] using hm
  · intro he
    apply hne
    have hm := congrArg (fun T : D.Vertex => T.val.subgroupOf K) he
    simpa only [hT₁, hT₂] using hm

/-- The constructed triangle types remain distinct even under the ambient edge stabilizer. -/
theorem exists_two_triangle_types (eK : K ≃* alternatingGroup (Fin 5))
    (Y : D.Vertex) (hXY : D.graph.Adj D.base Y) (hX : D.X ≤ K) (hY : Y.val ≤ K) :
    ∃ T₁ T₂ : D.Vertex, T₁.val ≤ K ∧ T₂.val ≤ K ∧
      TriangleWitnesses D K Y T₁ ∧ TriangleWitnesses D K Y T₂ ∧
      (D.X ⊔ Y.val) ⊔ T₁.val = D.X ⊔ Y.val ∧
      (D.X ⊔ Y.val) ⊔ T₂.val = K ∧
      ¬ ∃ g : edgeStabilizer G D.base Y, (g : G) • T₁ = T₂ := by
  obtain ⟨T₁, T₂, hT₁, hT₂, hw₁, hw₂, hs, hl, _⟩ :=
    exists_two_triangles D K eK Y hXY hX hY
  refine ⟨T₁, T₂, hT₁, hT₂, hw₁, hw₂, hs, hl, ?_⟩
  exact triangle_types_not_conjugate_of_a5_triple D D.base Y T₁ T₂ hXY
    (sup_eq_left.mp hs) ⟨(MulEquiv.subgroupCongr hl).trans eK⟩

end AlternatingFiveGeometry
namespace EdgeFrame
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (F : EdgeFrame D)

theorem edgeFixer_eq_bot
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) :
    F.K ⊓ edgeFixer G D.base F.y = ⊥ :=
  AlternatingFiveGeometry.edgeFixer_eq_bot D F.K eK F.y F.adjacent
    (le_sup_left.trans (F.endpoints_le he)) (le_sup_right.trans (F.endpoints_le he))

theorem exists_edge_reversal
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) :
    ∃ t : F.K, orderOf t = 2 ∧ (t : G) • D.base = F.y ∧ (t : G) • F.y = D.base :=
  AlternatingFiveGeometry.exists_edge_reversal D F.K eK F.y F.adjacent
    (le_sup_left.trans (F.endpoints_le he)) (le_sup_right.trans (F.endpoints_le he))

theorem exists_edgeStabilizer_equiv
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) :
    ∃ t : F.K, ∃ d : Multiplicative (ZMod 2) ≃* ↥(F.K ⊓ edgeStabilizer G D.base F.y),
      (d (Multiplicative.ofAdd 1) : G) = t ∧ orderOf t = 2 ∧
      (t : G) • D.base = F.y ∧ (t : G) • F.y = D.base ∧
      F.K ⊓ edgeStabilizer G D.base F.y = zpowers (t : G) :=
  AlternatingFiveGeometry.exists_edgeStabilizer_equiv D F.K eK F.y F.adjacent
    (le_sup_left.trans (F.endpoints_le he)) (le_sup_right.trans (F.endpoints_le he))

theorem edge_orbit_iff
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) (A B : D.Vertex) :
    (∃ g : F.K, ((g : G) • D.base = A ∧ (g : G) • F.y = B) ∨
      ((g : G) • D.base = B ∧ (g : G) • F.y = A)) ↔
      D.graph.Adj A B ∧ A.val ≤ F.K ∧ B.val ≤ F.K :=
  AlternatingFiveGeometry.edge_orbit_iff D F.K eK F.y F.adjacent
    (le_sup_left.trans (F.endpoints_le he)) (le_sup_right.trans (F.endpoints_le he)) A B

theorem exists_two_triangle_types
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) :
    ∃ T₁ T₂ : D.Vertex, T₁.val ≤ F.K ∧ T₂.val ≤ F.K ∧
      AlternatingFiveGeometry.TriangleWitnesses D F.K F.y T₁ ∧
      AlternatingFiveGeometry.TriangleWitnesses D F.K F.y T₂ ∧
      (D.X ⊔ F.y.val) ⊔ T₁.val = D.X ⊔ F.y.val ∧
      (D.X ⊔ F.y.val) ⊔ T₂.val = F.K ∧
      ¬ ∃ g : edgeStabilizer G D.base F.y, (g : G) • T₁ = T₂ :=
  AlternatingFiveGeometry.exists_two_triangle_types D F.K eK F.y F.adjacent
    (le_sup_left.trans (F.endpoints_le he)) (le_sup_right.trans (F.endpoints_le he))

end EdgeFrame

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal

namespace CFSG.Quasithin.Janko23.J2Recognition.LocalData
open SourceLocal.AlternatingFiveGeometry
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (L : LocalData D)

/-- The literal `System.localEdge` is the induced graph inside the local A₅. -/
theorem localEdge_iff_of_alternatingFive (eK : L.K ≃* alternatingGroup (Fin 5))
    (hX : D.X ≤ L.K) (hY : L.y.val ≤ L.K)
    (hf : ∀ g : G, (∀ A : D.Vertex, g • A = A) → g = 1) (A B : D.Vertex) :
    (L.toSystem hf).localEdge A B ↔ D.graph.Adj A B ∧ A.val ≤ L.K ∧ B.val ≤ L.K :=
  edge_orbit_iff D L.K eK L.y L.adjacent hX hY A B

/-- The two source triangles are actual triangles of the local orbit graph. -/
theorem two_triangle_types_of_alternatingFive (eK : L.K ≃* alternatingGroup (Fin 5))
    (hX : D.X ≤ L.K) (hY : L.y.val ≤ L.K)
    (hf : ∀ g : G, (∀ A : D.Vertex, g • A = A) → g = 1) :
    ∃ T₁ T₂ : D.Vertex,
      ((L.toSystem hf).localEdge L.y T₁ ∧ (L.toSystem hf).localEdge T₁ D.base) ∧
      ((L.toSystem hf).localEdge L.y T₂ ∧ (L.toSystem hf).localEdge T₂ D.base) ∧
      (D.X ⊔ L.y.val) ⊔ T₁.val = D.X ⊔ L.y.val ∧
      (D.X ⊔ L.y.val) ⊔ T₂.val = L.K ∧
      ¬ ∃ g : edgeStabilizer G D.base L.y, (g : G) • T₁ = T₂ := by
  obtain ⟨T₁, T₂, _, _, h₁, h₂, hs, hl, hn⟩ :=
    exists_two_triangle_types D L.K eK L.y L.adjacent hX hY
  have lift (T : D.Vertex) (h : TriangleWitnesses D L.K L.y T) :
      (L.toSystem hf).localEdge L.y T ∧ (L.toSystem hf).localEdge T D.base := by
    obtain ⟨⟨g, hg⟩, ⟨k, hk⟩⟩ := h
    exact ⟨⟨g, Or.inl hg⟩, ⟨k, Or.inl hk⟩⟩
  exact ⟨T₁, T₂, lift T₁ h₁, lift T₂ h₂, hs, hl, hn⟩

end CFSG.Quasithin.Janko23.J2Recognition.LocalData
