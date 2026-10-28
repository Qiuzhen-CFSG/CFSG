module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalVerticesSource
public import Theory.GroupTheory.C4SquareCoreBound
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.StandardPair

/-!
# The full original binary exceptional parabolics

A self-centralizing C₄ × C₄ core bounds the full alpha endpoint by 96.
The already recognized enlargement has this order, so it is the full
endpoint. The proper full Borel contains its order-32 two-core and has
order dividing 96; therefore the Borel is that core. The starred endpoint
supplements then identify both enlargements with the full endpoints.

Combining the three native group identifications gives the raw parabolic
equivalence in the binary row of (10.9), with beta first and alpha second.
The catalogue and earlier-center-family consumers retain both small-unitary
alternatives and the field-four row. This proves neither the path parameters
nor compatibility of the three equivalences with the inclusion maps.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.9), printed pp.162--163; original F1.11 markings, pp.95--96.
The imported native model retains its ATLAS license attribution.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance parabolicSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

private theorem enlarged_le (i : Fin 2) : enlargedEndpoint L S i ≤ parabolic L S i :=
  sup_le (starredParabolic_le i) ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic i))

private theorem full_borel_eq_core_of_binary_orders
    (h : HypothesisF11 L S) (hp : Nat.card (parabolic L S 0) = 96)
    (hc : Nat.card ((commonBorel L S).pCoreIn 2) = 32) :
    commonBorel L S = (commonBorel L S).pCoreIn 2 := by
  let := h.finite_parabolic 0
  let := h.finite_commonBorel
  have hne : commonBorel L S ≠ parabolic L S 0 := by
    intro he
    apply (h.rankOneBorelFacts 0).proper.not_ge
    rw [←h.local_inf_commonBorel 0]
    exact le_inf le_rfl (he ▸ le_sup_left.trans le_sup_left)
  have hlt : Nat.card (commonBorel L S) < Nat.card (parabolic L S 0) :=
    lt_of_not_ge (fun hge => hne (eq_of_le_of_card_ge (commonBorel_le_parabolic 0) hge))
  rw [hp] at hlt
  have hd := card_dvd_of_le (commonBorel_le_parabolic (L := L) (S := S) 0)
  rw [hp] at hd
  have h32 := card_dvd_of_le (pCoreIn_le 2 (commonBorel L S))
  rw [hc] at h32
  have hb : Nat.card (commonBorel L S) = 32 := by
    obtain ⟨n,hn⟩ := h32
    have hpos : 0 < Nat.card (commonBorel L S) := Nat.card_pos
    have hn' : n = 1 ∨ n = 2 := by omega
    rcases hn' with rfl | rfl
    · omega
    · norm_num [hn] at hd
  exact (eq_of_le_of_card_ge (pCoreIn_le 2 _) (by rw [hc,hb])).symm

/-- Both full original endpoints equal their Chapter 6 enlargements, and
the full Borel is its order-32 two-core. -/
theorem original_bTwo_exceptional_binary_full_endpoints
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
    (∀ i : Fin 2, enlargedEndpoint L S i = parabolic L S i) ∧
      commonBorel L S = (commonBorel L S).pCoreIn 2 ∧
      Nat.card (commonBorel L S) = 32 := by
  let := h.finite_parabolic 0
  let := h.finite_commonBorel
  obtain ⟨⟨eQ⟩,hA,_⟩ := original_bTwo_exceptional_binary_alpha_structure h hb c hactor
    hcentral ht hne hcomm hnot e hD E hK
  let f : pCore 2 (parabolic L S 0) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
    ((pCore 2 (parabolic L S 0)).equivMapOfInjective (parabolic L S 0).subtype
      (parabolic L S 0).subtype_injective).trans eQ
  have hbound : Nat.card (parabolic L S 0) ≤ 96 :=
    card_le_ninety_six_of_c4_square_core
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two 0)) f
  have ha : enlargedEndpoint L S 0 = parabolic L S 0 :=
    eq_of_le_of_card_ge (enlarged_le 0) (hA ▸ hbound)
  have hp : Nat.card (parabolic L S 0) = 96 := ha ▸ hA
  obtain ⟨_,⟨ew⟩,_,_⟩ := original_bTwo_exceptional_binary_vertices h hb c hactor
    hcentral ht hne hcomm hnot e hD E hK
  have hc : Nat.card ((commonBorel L S).pCoreIn 2) = 32 :=
    (Nat.card_congr ew.toEquiv).trans wreathedThirtyTwo_card
  have hB := full_borel_eq_core_of_binary_orders h hp hc
  refine ⟨?_,hB,hB.symm ▸ hc⟩
  intro i
  change starredParabolic L S i ⊔ (commonBorel L S).pCoreIn 2 = parabolic L S i
  rw [←hB,h.starredParabolic_supplement i]


/-- The full original triple, with beta first, has the native G₂(2)′ parabolics. -/
theorem original_bTwo_exceptional_binary_parabolic_equiv
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
    Nonempty (RankTwoAmalgam.ParabolicEquiv
      (RankTwoAmalgam.ofSubgroups (parabolic L S 1) (commonBorel L S)
        (parabolic L S 0) (commonBorel_le_parabolic 1)
        (commonBorel_le_parabolic 0)) Atlas.G2.BinaryParabolicPair.derivedAmalgam) := by
  obtain ⟨hfull,hB,_⟩ := original_bTwo_exceptional_binary_full_endpoints
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨_,⟨ew⟩,⟨ea⟩,⟨eb⟩⟩ := original_bTwo_exceptional_binary_vertices
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨em⟩ := Atlas.G2.BinaryParabolicPair.derivedSylow_isWreathedOfHeight.nonempty_mulEquiv_regularWreath
  exact ⟨{
    left := (MulEquiv.subgroupCongr (hfull 1).symm).trans eb
    middle := ((MulEquiv.subgroupCongr hB).trans ew).trans em.symm
    right := (MulEquiv.subgroupCongr (hfull 0).symm).trans ea }⟩


/-- The original catalogue now includes full binary parabolic recognition. -/
theorem original_bTwo_exceptional_parabolics_or_small_unitary
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
          (∀ i : Fin 2, enlargedEndpoint L S i = parabolic L S i) ∧
          commonBorel L S = (commonBorel L S).pCoreIn 2 ∧
          Nat.card (commonBorel L S) = 32 ∧
          Nonempty (RankTwoAmalgam.ParabolicEquiv
            (RankTwoAmalgam.ofSubgroups (parabolic L S 1) (commonBorel L S)
              (parabolic L S 0) (commonBorel_le_parabolic 1)
              (commonBorel_le_parabolic 0)) Atlas.G2.BinaryParabolicPair.derivedAmalgam)) ∨
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
    · obtain ⟨hfull,hB,h32⟩ := original_bTwo_exceptional_binary_full_endpoints
        h hb c hactor hcentral ht hne hcomm hnot e hD E htwo
      exact Or.inl ⟨hcard.symm.trans htwo,hQ₀,hQ₁,hfull,hB,h32,
        original_bTwo_exceptional_binary_parabolic_equiv
          h hb c hactor hcentral ht hne hcomm hnot e hD E htwo⟩
    · exact Or.inr (by simpa only [hcard] using hfour)
  · exact Or.inl hp
  · exact Or.inr (Or.inl hs)

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- The earlier center family supplies centrality for the original full-parabolic
consumer, retaining the full endpoint and Borel normalizers. -/
theorem original_bTwo_exceptional_parabolics_of_center_family
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
            (∀ i : Fin 2, enlargedEndpoint L S i = parabolic L S i) ∧
            commonBorel L S = (commonBorel L S).pCoreIn 2 ∧
            Nat.card (commonBorel L S) = 32 ∧
            Nonempty (RankTwoAmalgam.ParabolicEquiv
              (RankTwoAmalgam.ofSubgroups (parabolic L S 1) (commonBorel L S)
                (parabolic L S 0) (commonBorel_le_parabolic 1)
                (commonBorel_le_parabolic 0)) Atlas.G2.BinaryParabolicPair.derivedAmalgam)) ∨
            (2^n = 4 ∧ Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32))) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne
    hnot hcenters
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨hnorm.1.trans inf_le_right,hnorm.2.trans inf_le_right,
    original_bTwo_exceptional_parabolics_or_small_unitary h hb c hactor hcentral
      ht htne hcomm (hnot β c.middle.symm) hD E⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
