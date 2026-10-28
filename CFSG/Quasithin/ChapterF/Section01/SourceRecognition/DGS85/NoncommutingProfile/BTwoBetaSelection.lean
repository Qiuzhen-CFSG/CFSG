module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSuzukiExclusionSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoUnitaryExclusionSource

/-!
# Remaining beta quotient rows after the Frattini exclusions

For an actual graph beta quotient in the earlier rank-one catalogue,
Suzuki and both unitary rows are excluded, leaving the binary linear
row or the order-ten dihedral row. On the original F1.11 quotient,
the literal enlargement maps exclude every Suzuki parameter and unitary
degrees at least two. The original degree-one unitary rows are retained
because their enlargement has not been identified by those maps.

The statements keep actual quotient isomorphisms and every earlier
center, (6.5), and (7.4) input. They do not claim full (10.7): dihedral
exclusion, original small-unitary enlargement, and final saturation still
need to be assembled. Source: DGS, Groups and Graphs (1985), (10.7),
pp.158--159; original F1.11 rank-one alternatives and Chapter 6 enlargement.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Applying the proved exclusions to the actual earlier graph-model
catalogue leaves precisely the linear or dihedral rows. -/
theorem BTwoCenterActionData.beta_quotient_linear_or_dihedral
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
    (∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) 2 (2^n)) ∨
    Nonempty ((graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* DihedralGroup 5) := by
  cases hmodel with
  | linear n hn he => exact Or.inl ⟨n,hn,he⟩
  | suzuki n he =>
    obtain ⟨e⟩ := he
    exact (c.not_suzuki_beta_all h hB hSyl hb hactor hcentral ht hne hcomm hnot e).elim
  | projective_unitary n hn he =>
    obtain ⟨K,hK,hfin,J,hcard,hconj,⟨e⟩⟩ := he
    let := hK
    let := hfin
    exact (c.not_projective_unitary_beta h hB hSyl hb hactor hcentral ht hne hcomm hnot
      J hn hcard hconj e).elim
  | special_unitary n hn he =>
    obtain ⟨K,hK,hfin,J,hcard,hconj,⟨e⟩⟩ := he
    let := hK
    let := hfin
    exact (c.not_special_unitary_beta h hB hSyl hb hactor hcentral ht hne hcomm hnot
      J hn hcard hconj e).elim
  | dihedral he => exact Or.inr he

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- The original quotient alternatives after the model exclusions,
retaining the degree-one unitary rows whose enlargement remains separate. -/
theorem original_bTwo_beta_quotient_remaining
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ ≤ Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    : (∃ n, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n)) ∨
      ClassicalGroup.IsPSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      IsSU (L 1 ⧸ pCore 2 (L 1)) 3 2 ∨
      Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* DihedralGroup 5) := by
  cases h.quotient 1 with
  | linear n hn he => exact Or.inl ⟨n,hn,he⟩
  | suzuki n he =>
    obtain ⟨e⟩ := he
    exact (original_bTwo_not_suzuki_beta_all h hb c hactor hcentral ht hne hcomm hnot e).elim
  | projective_unitary n hn he =>
    by_cases hn2 : 2 ≤ n
    · exact (original_bTwo_not_unitary_beta h hb c hactor hcentral ht hne hcomm hnot hn2
        (Or.inl he)).elim
    · have heq : n = 1 := by omega
      subst n
      exact Or.inr (Or.inl (by simpa only [pow_one] using he))
  | special_unitary n hn he =>
    by_cases hn2 : 2 ≤ n
    · exact (original_bTwo_not_unitary_beta h hb c hactor hcentral ht hne hcomm hnot hn2
        (Or.inr he)).elim
    · have heq : n = 1 := by omega
      subst n
      exact Or.inr (Or.inr (Or.inl (by simpa only [pow_one] using he)))
  | dihedral he => exact Or.inr (Or.inr (Or.inr he))

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
