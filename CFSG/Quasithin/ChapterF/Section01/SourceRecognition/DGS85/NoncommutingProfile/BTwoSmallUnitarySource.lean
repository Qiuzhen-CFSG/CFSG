module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCoreFactors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoDihedralExclusionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallUnitarySolvability

/-!
# The degree-one unitary rows in the original Chapter 10 branch

The original beta catalogue after dihedral exclusion still has the two literal
fixed-field-two unitary quotients.  The source F.1.1 parabolics are
nonsolvable in the applications that reach Chapter 10.  The fixed-field-two
projective and special-unitary carriers are solvable, so the exact local
quotient criterion excludes those rows.  This extension keeps the original
quotient, center action, endpoint and Borel markings while discharging the
small-unitary alternatives for that source consumer.

Source: DGS, *Groups and Graphs* (1985), (6.1) and (10.7), pp.118--119,
158--159.  The concrete solvability calculation is in
`LocalStructure.SmallUnitarySolvability`.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
open DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance smallUnitarySourceAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The exact original beta quotient is linear once both source parabolics are
known to be nonsolvable; the degree-one unitary rows are eliminated by their
literal quotient models. -/
theorem original_bTwo_beta_linear_of_nonsolvable_parabolics
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i)) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) := by
  rcases original_bTwo_beta_linear_or_small_unitary h hb c hactor hcentral ht hne
      hcomm hnot E with hlin | hpu | hsu
  · exact hlin
  · exact ((no_small_unitary_of_nonsolvable_parabolics h hns 1).1 hpu).elim
  · exact ((no_small_unitary_of_nonsolvable_parabolics h hns 1).2 hsu).elim

/-- The source core-factor consumer with the small-unitary alternatives
fully discharged.  The returned denominator, normality and elementary
quotient are the literal original subgroups used by (10.7). -/
theorem original_bTwo_core_factors_of_nonsolvable_parabolics
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let Q₂ := (Q F₀ t).map (G₀ L S).subtype
    let D₀ := Q₁ ⊓ Q₂
    ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
      ∃ hE : IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀), letI := hE
        let q := QuotientGroup.mk' (D₀.subgroupOf Q₀)
        let A := ((Q₀ ⊓ Q₁).subgroupOf Q₀).map q
        let C := ((Q₀ ⊓ Q₂).subgroupOf Q₀).map q
        Disjoint A C ∧ ∃ e : A × C ≃* (Q₀ ⧸ D₀.subgroupOf Q₀),
          ∀ a c, e (a,c) = (a : Q₀ ⧸ D₀.subgroupOf Q₀) * c := by
  rcases original_bTwo_core_factors_or_small_unitary h hb c hactor hcentral ht hne
      hcomm hnot with hpu | hsu | hfactor
  · exact ((no_small_unitary_of_nonsolvable_parabolics h hns 1).1 hpu).elim
  · exact ((no_small_unitary_of_nonsolvable_parabolics h hns 1).2 hsu).elim
  · exact hfactor

/-- The central-core consumer likewise has no retained degree-one unitary
branch under the exact nonsolvability premise. -/
theorem original_bTwo_central_core_of_nonsolvable_parabolics
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i)) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype
    ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
        (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
      (∃ r : ℕ, 0 < r ∧ 2^n = Nat.card k ^ r) ∧
      (centralSeed F₀ α β t).map (G₀ L S).subtype = Q₀ ∧
      P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
        IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
        Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (2^n)^2 := by
  rcases original_bTwo_central_core_field_or_small_unitary h hb c hactor hcentral ht hne
      hcomm hnot E with hpu | hsu | hlin
  · exact ((no_small_unitary_of_nonsolvable_parabolics h hns 1).1 hpu).elim
  · exact ((no_small_unitary_of_nonsolvable_parabolics h hns 1).2 hsu).elim
  · exact hlin

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
