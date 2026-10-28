module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoDihedralSeedSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearSeedSource

/-!
# Seed saturation across the actual beta catalogue

The Suzuki and unitary obstructions leave a linear or dihedral graph
quotient. Both now saturate the actual seed. Consequently Q_alpha/D_alpha
is elementary, its order is the square of the adjacent-core index, and
that index bounds the alpha field order. This argument does not assume
beta linearity, seed saturation, or a numerical index.

At the original F1.11 endpoints the degree-one unitary enlargement is still
unidentified. The original application retains exactly those two rows as
alternatives, and proves saturation and the full marked core quotient in
every other row. It retains the full Borel and endpoint normalizers.
This is the saturation and elementary-section part of DGS (10.7),
pp.158--159; dihedral exclusion and subsequent recognition remain separate.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Saturation and the actual elementary quotient across the entire graph
catalogue. The cardinal is expressed using the literal adjacent-core index. -/
theorem BTwoCenterActionData.central_core_of_rankOne
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (hmodel : IsRankOneModel (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m))) :
    centralSeed F v m t = Q F v ∧
      Nat.card k ≤ (Q F m).relIndex (Q F v) ∧
      ∃ hN : ((D F m t).subgroupOf (Q F v)).Normal, letI := hN
        IsElementaryAbelian 2 (Q F v ⧸ (D F m t).subgroupOf (Q F v)) ∧
        Nat.card (Q F v ⧸ (D F m t).subgroupOf (Q F v)) =
          ((Q F m).relIndex (Q F v)) ^ 2 := by
  have hS := source_kernel_sylow h hB hSyl
  rcases c.beta_quotient_linear_or_dihedral h hB hSyl hb hactor hcentral ht hne
    hcomm hnot hmodel with ⟨n,hn,hm⟩ | ⟨e⟩
  · obtain ⟨K,hK,hfin,hcard,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let f := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    obtain ⟨hs,hi⟩ := c.linear_seed_eq_core_and_index h hB hSyl hS hb ht hne hnot f
    have hh := c.linear_central_core_structure h hB hSyl hb hactor hcentral ht hne hcomm hnot f
    rw [hi]
    exact ⟨hs,hh⟩
  · obtain ⟨e⟩ := e
    obtain ⟨hs,hi⟩ := c.dihedral_seed_eq_core_and_index h hB hSyl hS hb ht hne hnot e
    obtain ⟨hk,hN,hE,hcard⟩ := c.dihedral_central_core_structure h hB hSyl hb hactor
      hcentral ht hne hcomm hnot e
    rw [hi]
    exact ⟨hs,hk.le,hN,hE,hcard⟩

namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- On the original full endpoints, saturation and the marked elementary
core quotient hold unless the original beta row is one of the two still
unidentified degree-one unitary enlargements. -/
theorem original_bTwo_central_core_or_small_unitary
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁ ⊓ (Q F₀ t).map (G₀ L S).subtype
    ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      ((centralSeed F₀ α β t).map (G₀ L S).subtype = Q₀ ∧
        P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
        B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
        Nat.card k ≤ Q₁.relIndex Q₀ ∧
        ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
          IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
          Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (Q₁.relIndex Q₀)^2) := by
  have hlayers := original_bTwo_seed_layers_normalized h hb c ht hne
  dsimp only at hlayers ⊢
  rcases original_bTwo_beta_quotient_remaining h hb c hactor hcentral ht hne hcomm hnot
      with ⟨n,hn,hm⟩ | hp | hs | ⟨e⟩
  · obtain ⟨K,hK,hfin,hcard,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    obtain ⟨hs,hi,_⟩ := original_bTwo_linear_seed_and_indices h hb c ht hne hnot e
    have hc := original_bTwo_linear_central_core h hb c hactor hcentral ht hne hcomm hnot e
    dsimp only at hc
    rw [hs] at hlayers
    right; right
    rw [hi]
    exact ⟨hs,hlayers.1,hlayers.2,hc⟩
  · exact Or.inl hp
  · exact Or.inr (Or.inl hs)
  · obtain ⟨e⟩ := e
    obtain ⟨hs,hi,_⟩ := original_bTwo_dihedral_seed_and_indices h hb c hactor hcentral
      hcomm ht hne hnot e
    obtain ⟨hk,hN,hE,hcard⟩ := original_bTwo_dihedral_central_core h hb c hactor hcentral
      ht hne hcomm hnot e
    rw [hs] at hlayers
    right; right
    rw [hi]
    exact ⟨hs,hlayers.1,hlayers.2,hk.le,hN,hE,hcard⟩

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
