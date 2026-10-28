module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalVertices
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCoreRecognitionSource

/-!
# Original binary exceptional local recognition

The unchanged full beta core is Q₈ ◦ C₄, and the two-core of the full
original Borel is C₄ wreath C₂. Transport through the literal reduced
completion inclusion identifies both original Chapter 6 enlargements
with the actual parabolics of the native octonion G₂(2)′ model.

The original beta catalogue carries these models in its binary row;
PSU₃(2), SU₃(2), and the field-four row are retained. The earlier center
family discharges centrality and retains the full endpoint and Borel
normalizers. These equivalences concern the enlargements and Borel core;
restoration to the full parabolic amalgam and the path parameters remain.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (10.9), printed p.163, and original markings, pp.95--96.
The existing native-model imports retain their ATLAS license attribution.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance verticesSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The source full Borel two-core is the product of the original endpoint cores. -/
theorem original_bTwo_borel_core_eq_product
    (h : HypothesisF11 L S) {u : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W) :
    (commonBorel L S).pCoreIn 2 =
      (parabolic L S 0).pCoreIn 2 ⊔ (parabolic L S 1).pCoreIn 2 := by
  have hh := congrArg (map (G₀ L S).subtype) (c.core_product_eq_edge_core (reduced_triple h))
  change (Q F₀ β ⊔ Q F₀ α : Subgroup (G₀ L S)).map (G₀ L S).subtype =
    ((stabilizer F₀ β ⊓ stabilizer F₀ α).pCoreIn 2).map (G₀ L S).subtype at hh
  rw [Subgroup.map_sup,reduced_base_Q_map h true,reduced_base_Q_map h false] at hh
  have he : ((stabilizer F₀ β ⊓ stabilizer F₀ α).pCoreIn 2).map (G₀ L S).subtype =
      (commonBorel L S).pCoreIn 2 := by
    have hi : stabilizer F₀ β ⊓ stabilizer F₀ α = (B₀ L S).subgroupOf (G₀ L S) := by
      simp only [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
      exact (inf_comm _ _).trans (reduced_triple h).intersection
    rw [hi,map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
      map_subgroupOf_eq_of_le (show B₀ L S ≤ G₀ L S from le_sup_right.trans le_sup_left),B₀_core h]
  rw [he] at hh
  exact hh.symm.trans (sup_comm _ _)

/-- The original beta core, full Borel core, and both literal enlargements
have their native binary exceptional models. -/
theorem original_bTwo_exceptional_binary_vertices
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 2) :
    Nonempty ((parabolic L S 1).pCoreIn 2 ≃* QuaternionCyclic.Model) ∧
      Nonempty ((commonBorel L S).pCoreIn 2 ≃* Theory.GroupTheory.WreathedThirtyTwo) ∧
      Nonempty (enlargedEndpoint L S 0 ≃* Atlas.G2.BinaryParabolicPair.derivedSecond) ∧
      Nonempty (enlargedEndpoint L S 1 ≃* Atlas.G2.BinaryParabolicPair.derivedFirst) := by
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hD' : D F₀ β t = Z F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    exact hD
  obtain ⟨ea⟩ := c.exceptional_binary_alpha_vertex (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral
    ht hne hcomm.le hnot eβ hD' E hK
  obtain ⟨⟨eq⟩,⟨eb⟩⟩ := c.exceptional_binary_beta_vertex (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral
    ht hne hcomm hnot eβ hD' E hK
  obtain ⟨ew⟩ := c.exceptional_binary_core_product_wreathed (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral
    ht hne hcomm.le hnot eβ hD' E hK
  let ι := (G₀ L S).subtype
  have ha : c.actor.map ι = enlargedEndpoint L S 0 := by
    rw [hactor,reduced_graphLocalGroup_image h false]
    rfl
  have hb' : (graphLocalGroup F₀ β).map ι = enlargedEndpoint L S 1 := by
    rw [reduced_graphLocalGroup_image h true]
    rfl
  let eA : c.actor ≃* enlargedEndpoint L S 0 :=
    (c.actor.equivMapOfInjective ι (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr ha)
  let eB : graphLocalGroup F₀ β ≃* enlargedEndpoint L S 1 :=
    ((graphLocalGroup F₀ β).equivMapOfInjective ι (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr hb')
  let eQ : Q F₀ β ≃* (parabolic L S 1).pCoreIn 2 :=
    ((Q F₀ β).equivMapOfInjective ι (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr (reduced_base_Q_map h true))
  have hs : (Q F₀ β ⊔ Q F₀ α : Subgroup (G₀ L S)).map ι = (commonBorel L S).pCoreIn 2 := by
    rw [Subgroup.map_sup,reduced_base_Q_map h true,reduced_base_Q_map h false,
      original_bTwo_borel_core_eq_product h c]
    exact sup_comm _ _
  let eS : (Q F₀ β ⊔ Q F₀ α : Subgroup (G₀ L S)) ≃* (commonBorel L S).pCoreIn 2 :=
    ((Q F₀ β ⊔ Q F₀ α : Subgroup (G₀ L S)).equivMapOfInjective ι
      (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr hs)
  exact ⟨⟨eQ.symm.trans eq⟩,⟨eS.symm.trans ew⟩,⟨eA.symm.trans ea⟩,⟨eB.symm.trans eb⟩⟩

/-- Carry the two native enlargements and the full Borel core in the binary
catalogue row; retain both degree-one unitary rows and the field-four row. -/
theorem original_bTwo_exceptional_vertices_or_small_unitary
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
        Nat.card k = 2 ∧
        ((2^n = 2 ∧ Nat.card Q₀ = 16 ∧ Nat.card Q₁ = 16 ∧
          Nonempty (Q₀ ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
          Nat.card (enlargedEndpoint L S 0) = 96 ∧
          Nonempty (Q₁ ≃* QuaternionCyclic.Model) ∧
          Nonempty ((commonBorel L S).pCoreIn 2 ≃* Theory.GroupTheory.WreathedThirtyTwo) ∧
          Nonempty (enlargedEndpoint L S 0 ≃* Atlas.G2.BinaryParabolicPair.derivedSecond) ∧
          Nonempty (enlargedEndpoint L S 1 ≃* Atlas.G2.BinaryParabolicPair.derivedFirst)) ∨
          (2^n = 4 ∧ Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32)) := by
  rcases original_bTwo_beta_linear_or_small_unitary h hb c hactor hcentral ht hne
    hcomm hnot E with ⟨n,hn,hm⟩ | hp | hs
  · obtain ⟨K,hK,hfin,hcard,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    have hp := original_bTwo_exceptional_fields_and_orders h hb c hactor hcentral
      ht hne hcomm hnot e hD E
    refine Or.inr (Or.inr ⟨n,hn,⟨K,hK,hfin,hcard,⟨e⟩⟩,hp.1,?_⟩)
    rcases hp.2 with ⟨htwo,hQ₀,hQ₁⟩ | hfour
    · obtain ⟨hmodel,hactorCard,_⟩ := original_bTwo_exceptional_binary_alpha_structure
        h hb c hactor hcentral ht hne hcomm hnot e hD E htwo
      obtain ⟨hbeta,hborel,hleft,hright⟩ := original_bTwo_exceptional_binary_vertices
        h hb c hactor hcentral ht hne hcomm hnot e hD E htwo
      exact Or.inl ⟨hcard.symm.trans htwo,hQ₀,hQ₁,hmodel,hactorCard,hbeta,hborel,hleft,hright⟩
    · exact Or.inr (by simpa only [hcard] using hfour)
  · exact Or.inl hp
  · exact Or.inr (Or.inl hs)

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- The earlier center family supplies centrality for the original local-recognition
consumer, retaining the full endpoint and Borel normalizers. -/
theorem original_bTwo_exceptional_vertices_of_center_family
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hnot : ∀ y, (graph F₀).Adj y α →
      ¬ stabilizer F₀ α ≤ normalizer
        ((Q F₀ y ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ y, (graph F₀).Adj y α → IsCriticalPair F₀ β y →
      ⁅Z F₀ β,Z F₀ y⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F₀ β α y k₁ W₁))
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    P₀ L S 0 ≤ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (D₀ : Set G) ∧
      (ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
        IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
        ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
          Nat.card k = 2 ∧
          ((2^n = 2 ∧ Nat.card Q₀ = 16 ∧ Nat.card Q₁ = 16 ∧
            Nonempty (Q₀ ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
            Nat.card (enlargedEndpoint L S 0) = 96 ∧
            Nonempty (Q₁ ≃* QuaternionCyclic.Model) ∧
            Nonempty ((commonBorel L S).pCoreIn 2 ≃* Theory.GroupTheory.WreathedThirtyTwo) ∧
            Nonempty (enlargedEndpoint L S 0 ≃* Atlas.G2.BinaryParabolicPair.derivedSecond) ∧
            Nonempty (enlargedEndpoint L S 1 ≃* Atlas.G2.BinaryParabolicPair.derivedFirst)) ∨
            (2^n = 4 ∧ Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32))) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne
    hnot hcenters
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨hnorm.1.trans inf_le_right,hnorm.2.trans inf_le_right,
    original_bTwo_exceptional_vertices_or_small_unitary h hb c hactor hcentral
      ht htne hcomm (hnot β c.middle.symm) hD E⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
