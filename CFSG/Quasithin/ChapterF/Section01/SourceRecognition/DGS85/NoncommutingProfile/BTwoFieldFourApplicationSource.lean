module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourRecognitionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSmallUnitaryExclusionSource

/-!
# Exhaustive exceptional selection with the actual field-four core

Apply the field-four recognition to the original beta quotient selected by
the full rank-one catalogue. The binary alternative retains its complete
endpoint and Borel parabolic equivalence. The field-four alternative now
identifies the literal beta core with the minus extraspecial group, retaining
both original core orders and the beta field marking.

The center-family application discharges beta centrality and retains both
full reduced endpoint and Borel normalizers. The earlier center and
commutator inputs remain explicit; the field-four extension splitting,
J₂ parabolic recognition and path parameters still require proof.
Source: DGS, Groups and Graphs (1985), (10.9), printed p.163.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open BenderSuzuki.MatrixGroups Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourApplicationAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

/-- Exhaustive exceptional selection retains the full binary parabolics and now identifies the field-four beta core. -/
theorem original_bTwo_exceptional_parabolics_and_core
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
          (2^n = 4 ∧ Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32 ∧
            IsExtraspecial 2 Q₁ ∧ Nonempty (Q₁ ≃* MinusExtraspecial.Model))) := by
  obtain ⟨n,hn,hm,hk,hcase⟩ := original_bTwo_exceptional_parabolics h hb c hactor
    hcentral ht hne hcomm hnot hD E
  refine ⟨n,hn,hm,hk,?_⟩
  rcases hcase with htwo | ⟨hfour,hQa,hQb⟩
  · exact Or.inl htwo
  · obtain ⟨K,hK,hfin,hcard,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact Or.inr ⟨hfour,hQa,hQb,
      original_bTwo_field_four_beta_recognition h hb c hactor hcentral ht hne
        hcomm hnot e hD E (hcard.trans hfour)⟩

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- The earlier center family supplies centrality for the original exceptional consumer. -/
theorem original_bTwo_exceptional_core_exhaustive_of_center_family
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
      (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
          Nat.card k = 2 ∧
          ((2^n = 2 ∧ Nat.card Q₀ = 16 ∧ Nat.card Q₁ = 16 ∧
            (∀ i : Fin 2, enlargedEndpoint L S i = parabolic L S i) ∧
            commonBorel L S = (commonBorel L S).pCoreIn 2 ∧
            Nat.card (commonBorel L S) = 32 ∧
            Nonempty (RankTwoAmalgam.ParabolicEquiv
              (RankTwoAmalgam.ofSubgroups (parabolic L S 1) (commonBorel L S)
                (parabolic L S 0) (commonBorel_le_parabolic 1)
                (commonBorel_le_parabolic 0)) Atlas.G2.BinaryParabolicPair.derivedAmalgam)) ∨
            (2^n = 4 ∧ Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32 ∧
              IsExtraspecial 2 Q₁ ∧ Nonempty (Q₁ ≃* MinusExtraspecial.Model)))) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne
    hnot hcenters
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨hnorm.1.trans inf_le_right,hnorm.2.trans inf_le_right,
    original_bTwo_exceptional_parabolics_and_core h hb c hactor hcentral
      ht htne hcomm (hnot β c.middle.symm) hD E⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
