module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSmallUnitaryEnlargementSource

/-!
# Exhaustive original beta selection in the central noncommuting branch

Both original small-unitary alternatives are excluded through their genuine
Chapter 6 enlargements. The actual beta quotient is therefore binary linear.
The proved linear calculation supplies seed saturation, the elementary
alpha-core section of order q_beta squared, and the field-power relation.

In the exceptional D_alpha = Z_alpha branch the original full endpoints
have the binary G₂(2)′ parabolic equivalence, or the field-four core orders
(64,32). The earlier center-family application discharges centrality and
preserves both full endpoints, the full Borel and the literal D subgroup.
Field-four J₂ recognition and all remaining path conclusions still require
proof; no ambient completion recognition is asserted.

Source: DGS, Groups and Graphs (1985), (10.7)--(10.9), pp.158--163;
Aschbacher--Smith F.1.9 endpoint markings, pp.261--262.
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

local instance smallUnitaryExclusionAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- Exhaustive beta linearity after excluding both actual small-unitary enlargements. -/
theorem original_bTwo_beta_linear
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) := by
  rcases original_bTwo_beta_linear_or_projective144 h hb c hactor hcentral ht hne
    hcomm hnot E with hl | ⟨hp,_⟩
  · exact hl
  · exact (original_bTwo_not_small_projective_beta h hb c hactor hcentral ht hne
      hcomm.le hnot hp).elim

/-- The literal original seed is saturated, with the beta field and elementary core section. -/
theorem original_bTwo_central_core_field
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
        (∃ r : ℕ, 0 < r ∧ 2^n = Nat.card k ^ r) ∧
        (centralSeed F₀ α β t).map (G₀ L S).subtype = Q₀ ∧
        P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
        B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
        ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
          IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
          Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (2^n)^2 := by
  rcases original_bTwo_central_core_field_or_projective144 h hb c hactor hcentral ht hne
    hcomm hnot E with ⟨hp,_⟩ | hl
  · exact (original_bTwo_not_small_projective_beta h hb c hactor hcentral ht hne
      hcomm.le hnot hp).elim
  · exact hl

/-- The exceptional branch has the full binary parabolic equivalence or the field-four core orders. -/
theorem original_bTwo_exceptional_parabolics
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
          (2^n = 4 ∧ Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32)) := by
  rcases original_bTwo_exceptional_parabolics_or_projective144 h hb c hactor hcentral ht hne
    hcomm hnot hD E with ⟨hp,_⟩ | hl
  · exact (original_bTwo_not_small_projective_beta h hb c hactor hcentral ht hne
      hcomm.le hnot hp).elim
  · exact hl

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]

/-- The earlier center family supplies centrality for the original exceptional consumer. -/
theorem original_bTwo_exceptional_parabolics_exhaustive_of_center_family
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
            (2^n = 4 ∧ Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32))) := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne
    hnot hcenters
  have hnorm := original_bTwo_seed_layers_normalized h hb c ht htne
  exact ⟨hnorm.1.trans inf_le_right,hnorm.2.trans inf_le_right,
    original_bTwo_exceptional_parabolics h hb c hactor hcentral
      ht htne hcomm (hnot β c.middle.symm) hD E⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
