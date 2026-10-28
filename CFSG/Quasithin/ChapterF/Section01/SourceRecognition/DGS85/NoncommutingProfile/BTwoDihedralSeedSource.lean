module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoDihedralSeed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSeedIntersectionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSuzukiExclusionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.DihedralApplication

/-!
# The original dihedral row and its saturated elementary core quotient

The actual original D₁₀ quotient enlarges either to D₁₀ or Sz(2). The
proved Suzuki obstruction excludes the latter, so the graph actor is
exactly the original starred endpoint under the completion inclusion.
Its order-two Sylow image saturates the seed and forces q_alpha = 2.
The literal original alpha core modulo D_alpha is elementary of order four;
the original endpoint and full Borel normalize the marked layers.

This specializes the remaining dihedral source branch without assuming its
exclusion or exceptional recognition. The earlier (6.5), center-action and
(7.4) inputs remain explicit. Source: DGS, Groups and Graphs (1985),
(6.1), pp.118--119, and (10.7), pp.158--159.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- The original dihedral row cannot acquire the Sz(2) enlargement.
The graph actor maps onto the original starred endpoint. -/
theorem original_bTwo_dihedral_graph_marking
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5) :
    (graphLocalGroup F₀ β).map (G₀ L S).subtype = starredParabolic L S 1 ∧
      Nonempty ((graphLocalGroup F₀ β ⧸ pCore 2 (graphLocalGroup F₀ β)) ≃* DihedralGroup 5) := by
  rcases reduced_graph_dihedral_alternatives h true e with hh | hh
  · exact hh
  · obtain ⟨f⟩ := hh
    exact (c.not_suzuki_beta_all (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht hne hcomm hnot f).elim

/-- Saturation and the two order-two indices, with the original full endpoint cores. -/
theorem original_bTwo_dihedral_seed_and_indices
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5) :
    (centralSeed F₀ α β t).map (G₀ L S).subtype = (parabolic L S 0).pCoreIn 2 ∧
      ((parabolic L S 1).pCoreIn 2).relIndex ((parabolic L S 0).pCoreIn 2) = 2 ∧
      ((parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype).relIndex
        ((parabolic L S 0).pCoreIn 2 ⊓ (parabolic L S 1).pCoreIn 2) = 2 := by
  obtain ⟨_,⟨f⟩⟩ := original_bTwo_dihedral_graph_marking h hb c hactor hcentral ht hne hcomm hnot e
  obtain ⟨hs,hi⟩ := c.dihedral_seed_eq_core_and_index (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) (reduced_kernel_sylow h)
    hb ht hne hnot f
  have hf := c.dihedral_seed_factor_index (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) (reduced_kernel_sylow h)
    hb ht hne hnot f
  have hs' : centralSeed F₀ α β t = Q F₀ α := hs
  refine ⟨?_,?_,?_⟩
  · rw [hs',reduced_base_Q_map h false]
    rfl
  · have hh := relIndex_map_map_of_injective (f := (G₀ L S).subtype)
      (Q F₀ β) (Q F₀ α) (G₀ L S).subtype_injective
    rw [reduced_base_Q_map h false,reduced_base_Q_map h true] at hh
    exact hh.trans hi
  · have hh := relIndex_map_map_of_injective (f := (G₀ L S).subtype)
      (D F₀ β t) (Q F₀ α ⊓ Q F₀ β) (G₀ L S).subtype_injective
    change ((Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype).relIndex
      ((Q F₀ α ⊓ Q F₀ β).map (G₀ L S).subtype) = _ at hh
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,
      map_inf _ _ _ (G₀ L S).subtype_injective,
      reduced_base_Q_map h false,reduced_base_Q_map h true] at hh
    exact hh.trans hf

private theorem map_elementary_section {H : Type*} [Group H]
    (A D : Subgroup H) (hDA : D ≤ A) [(D.subgroupOf A).Normal]
    [IsElementaryAbelian 2 (A ⧸ D.subgroupOf A)] (f : H →* G) (hf : Function.Injective f) :
    ∃ hN : ((D.map f).subgroupOf (A.map f)).Normal,
      letI := hN
      IsElementaryAbelian 2 (A.map f ⧸ (D.map f).subgroupOf (A.map f)) ∧
      Nat.card (A.map f ⧸ (D.map f).subgroupOf (A.map f)) = Nat.card (A ⧸ D.subgroupOf A) := by
  let e := A.equivMapOfInjective f hf
  have he : (D.subgroupOf A).map e.toMonoidHom = (D.map f).subgroupOf (A.map f) := by
    apply map_injective (A.map f).subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (map_mono hDA)]
    change (D.subgroupOf A).map (f.comp A.subtype) = D.map f
    rw [←map_map,map_subgroupOf_eq_of_le hDA]
  have hN : ((D.map f).subgroupOf (A.map f)).Normal :=
    he ▸ (inferInstance : (D.subgroupOf A).Normal).map e.toMonoidHom e.surjective
  let := hN
  let eqv := QuotientGroup.congr (D.subgroupOf A) ((D.map f).subgroupOf (A.map f)) e he
  exact ⟨hN,IsElementaryAbelian.of_surjective eqv.toMonoidHom eqv.surjective,
    (Nat.card_congr eqv.toEquiv).symm⟩

/-- The original alpha core quotient is elementary of order four, and the
alpha field has order two. The original marking discharges saturation. -/
theorem original_bTwo_dihedral_central_core
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    Nat.card k = 2 ∧
      ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
        IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
        Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = 4 := by
  obtain ⟨_,⟨f⟩⟩ := original_bTwo_dihedral_graph_marking h hb c hactor hcentral ht hne hcomm hnot e
  obtain ⟨hbound,hN,hE,hcard⟩ := c.dihedral_central_core_structure (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral ht hne
    hcomm hnot f
  let : ((D F₀ β t).subgroupOf (Q F₀ α)).Normal := hN
  let : IsElementaryAbelian 2 (Q F₀ α ⧸ (D F₀ β t).subgroupOf (Q F₀ α)) := hE
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift (reduced_triple h) ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry (reduced_triple h)
    (reduced_kernel_sylow h) hb g hg hop
  have hh := map_elementary_section (Q F₀ α) (D F₀ β t)
    d.separated (G₀ L S).subtype (G₀ L S).subtype_injective
  have hDm : (D F₀ β t).map (G₀ L S).subtype =
      (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype := by
    change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  rw [hDm,reduced_base_Q_map h false] at hh
  obtain ⟨hN',hE',hcard'⟩ := hh
  exact ⟨hbound,hN',hE',hcard'.trans hcard⟩


variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance dihedralSeedAlgebra {F : Type*} [Field F] [CharP F 2] : Algebra (ZMod 2) F :=
  ZMod.algebra F 2

/-- Apply the dihedral beta marking and the earlier center-action family to
the literal original core quotient. Characteristic-two exclusion supplies
centrality; the original reduced endpoint and full Borel normalize both layers. -/
theorem original_bTwo_dihedral_core_of_center_family
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hnot : ∀ y, (graph F₀).Adj y α →
      ¬ stabilizer F₀ α ≤ normalizer ((Q F₀ y ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ y, (graph F₀).Adj y α → IsCriticalPair F₀ β y →
      ⁅Z F₀ β,Z F₀ y⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F₀ β α y k₁ W₁))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    (centralSeed F₀ α β t).map (G₀ L S).subtype = Q₀ ∧
      P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      Nat.card k = 2 ∧
      ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
        IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
        Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = 4 := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  have hs := (original_bTwo_dihedral_seed_and_indices h hb c hactor hcentral hcomm ht htne (hnot β c.middle.symm) e).1
  have hlayers := original_bTwo_seed_layers_normalized h hb c ht htne
  dsimp only at hlayers
  rw [hs] at hlayers
  exact ⟨hs,hlayers.1,hlayers.2,original_bTwo_dihedral_central_core h hb c hactor
    hcentral ht htne hcomm (hnot β c.middle.symm) e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
