module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCoreRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalBinarySource

/-!
# Original exceptional core recognition and its marked complement

In the binary beta row of (10.9), the full original alpha core is
isomorphic to C₄ × C₄. The actual Chapter 6 enlargement has order 96.
Its intersection with the ambient normalizer of a constructed cubic
complements that full core. Both the enlargement inclusion and the
complement's identification with SL₂(k) retain the original quotient map.
The normalizer is relative to the enlargement, not the whole completion.

The original beta catalogue now carries this core isomorphism in its
binary row. PSU₃(2), SU₃(2), and the field-four row remain explicit.
The earlier center family supplies centrality and preserves the full
endpoint and Borel normalizers. No parabolic-amalgam equivalence or path
parameters are inferred from the core or split local extension alone.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (10.9), printed p.163; original endpoint markings, pp.95--96.
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
local instance coreRecognitionSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

private theorem map_normalizer_in_range {H : Type*} [Group H] (f : H →* G)
    (hf : Function.Injective f) (C : Subgroup H) :
    (normalizer (C : Set H)).map f = f.range ⊓ normalizer (C.map f : Set G) := by
  have hn := comap_normalizer_eq_of_le_range (C.map_le_range (f := f))
  rw [comap_map_eq_self_of_injective hf] at hn
  rw [←hn,map_comap_eq]

/-- The full original core and the cubic normalizer inside its actual enlargement,
with both inclusion and quotient coordinates retained. -/
theorem original_bTwo_exceptional_binary_alpha_structure
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
    let Q₀ := (parabolic L S 0).pCoreIn 2
    Nonempty (Q₀ ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
      Nat.card (enlargedEndpoint L S 0) = 96 ∧
      ∃ eA : c.actor ≃* enlargedEndpoint L S 0,
        (∀ x, (eA x : G) = ((x : G₀ L S) : G)) ∧
        ∃ a : c.actor, orderOf ((a : G₀ L S) : G) = 3 ∧
          let N := enlargedEndpoint L S 0 ⊓ normalizer (zpowers ((a : G₀ L S) : G) : Set G)
          Disjoint Q₀ N ∧ Q₀ ⊔ N = enlargedEndpoint L S 0 ∧
            ∃ eN : N ≃* SL(2,k), ∀ x : N,
              eN x = c.quotient (eA.symm ⟨x,x.property.1⟩) := by
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hD' : D F₀ β t = Z F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    exact hD
  obtain ⟨eQ⟩ := c.exceptional_binary_alpha_core_equiv (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral
    ht hne hcomm.le hnot eβ hD' E hK
  obtain ⟨hcard,a,ha,hcomp,eN,heN⟩ := c.exceptional_binary_alpha_complement (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral
    ht hne hcomm.le hnot eβ hD' E hK
  let ι := (G₀ L S).subtype
  let f := ι.comp c.actor.subtype
  have hf : Function.Injective f := (G₀ L S).subtype_injective.comp c.actor.subtype_injective
  have hAm : c.actor.map ι = enlargedEndpoint L S 0 := by
    rw [hactor,reduced_graphLocalGroup_image h false]
    rfl
  let eA : c.actor ≃* enlargedEndpoint L S 0 :=
    (c.actor.equivMapOfInjective ι (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr hAm)
  let eQ₀ : Q F₀ α ≃* (parabolic L S 0).pCoreIn 2 :=
    ((Q F₀ α).equivMapOfInjective ι (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr (reduced_base_Q_map h false))
  have hrange : f.range = enlargedEndpoint L S 0 := by
    rw [MonoidHom.range_comp,range_subtype]
    exact hAm
  have hker : c.quotient.ker.map f = (parabolic L S 0).pCoreIn 2 := by
    rw [c.kernel,←map_map,map_subgroupOf_eq_of_le c.core_le,reduced_base_Q_map h false]
    rfl
  let H := normalizer (zpowers a : Set c.actor)
  let N := enlargedEndpoint L S 0 ⊓ normalizer (zpowers (f a) : Set G)
  have hNm : H.map f = N := by
    rw [map_normalizer_in_range f hf,hrange,MonoidHom.map_zpowers]
  let eHN : H ≃* N := (H.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hNm)
  refine ⟨⟨eQ₀.symm.trans eQ⟩,(Nat.card_congr eA.toEquiv).symm.trans hcard,eA,
    (fun _ => rfl),a,(orderOf_injective f hf a).trans ha,?_,?_,eHN.symm.trans eN,?_⟩
  · change Disjoint ((parabolic L S 0).pCoreIn 2) N
    rw [←hker,←hNm]
    exact disjoint_map hf hcomp.disjoint
  · have hh := congrArg (map f) hcomp.sup_eq_top
    rw [Subgroup.map_sup,hker,hNm,←MonoidHom.range_eq_map,hrange] at hh
    exact hh
  · intro x
    obtain ⟨y,rfl⟩ := eHN.surjective x
    change eN (eHN.symm (eHN y)) = _
    rw [eHN.symm_apply_apply,heN]
    congr 1
    apply eA.injective
    rw [eA.apply_symm_apply]
    rfl

/-- The original catalogue carries the homocyclic core model in its binary row,
while retaining both small-unitary alternatives and the field-four row. -/
theorem original_bTwo_exceptional_core_model_or_small_unitary
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
          Nat.card (enlargedEndpoint L S 0) = 96) ∨
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
      exact Or.inl ⟨hcard.symm.trans htwo,hQ₀,hQ₁,hmodel,hactorCard⟩
    · exact Or.inr (by simpa only [hcard] using hfour)
  · exact Or.inl hp
  · exact Or.inr (Or.inl hs)

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- The earlier center family supplies centrality for the original core-model
consumer, retaining the full endpoint and Borel normalizers. -/
theorem original_bTwo_exceptional_core_model_of_center_family
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
            Nat.card (enlargedEndpoint L S 0) = 96) ∨
            (2^n = 4 ∧ Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32))) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne
    hnot hcenters
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨hnorm.1.trans inf_le_right,hnorm.2.trans inf_le_right,
    original_bTwo_exceptional_core_model_or_small_unitary h hb c hactor hcentral
      ht htne hcomm (hnot β c.middle.symm) hD E⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
