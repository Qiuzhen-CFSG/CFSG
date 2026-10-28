module
public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.SolvableResidual.CoreOuter

/-!
# Component counts from prime rank at most two

Distinct components of a radical-free finite group commute and have disjoint
intersection. Their prime ranks therefore add, including for three distinct
components. If every component has positive p-rank and the ambient p-rank is
at most two, any two distinct components exhaust the component family.

The layer is self-centralizing when the radical is trivial. A two-group outer
automorphism group then makes the layer the solvable residual. These are the
group-theoretic steps used in Aschbacher--Smith 14.6.21 and 14.6.23(1), printed
pp.1037--1038; no component-model classification is assumed in these lemmas.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Two distinct components contribute independent prime ranks. -/
theorem IsCComponent.primeRank_pair_le
    {p : ℕ} [Fact p.Prime] {B C : Subgroup G}
    (hR : solvableRadical G = ⊥) (hB : B.IsCComponent) (hC : C.IsCComponent)
    (hne : B ≠ C) : primeRank p B + primeRank p C ≤ primeRank p G := by
  have hc := hB.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hC hne
  have hd := hB.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hR hc
  rw [← primeRank_sup_eq_add_of_disjoint_commuting B C hd
    (commutator_eq_bot_iff_le_centralizer.mp hc) p]
  exact primeRank_subgroup_le p _

/-- Three distinct components contribute three independent prime ranks. -/
theorem IsCComponent.primeRank_triple_le
    {p : ℕ} [Fact p.Prime] {B C D : Subgroup G}
    (hR : solvableRadical G = ⊥) (hB : B.IsCComponent) (hC : C.IsCComponent)
    (hD : D.IsCComponent) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    primeRank p B + primeRank p C + primeRank p D ≤ primeRank p G := by
  have hbc := hB.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hC hBC
  have hbd := hB.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hD hBD
  have hcd := hC.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hD hCD
  have hcomm : ⁅D, B ⊔ C⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hbd)
      (commutator_eq_bot_iff_le_centralizer.mp hcd)
  have hd := hD.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hR hcomm
  have he := primeRank_sup_eq_add_of_disjoint_commuting D (B ⊔ C) hd
    (commutator_eq_bot_iff_le_centralizer.mp hcomm) p
  have hf := primeRank_sup_eq_add_of_disjoint_commuting B C
    (hB.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hR hbc)
    (commutator_eq_bot_iff_le_centralizer.mp hbc) p
  have hr := primeRank_subgroup_le p (D ⊔ (B ⊔ C))
  rw [he, hf] at hr
  omega

/-- Positive component ranks and ambient rank two leave at most two components. -/
theorem IsCComponent.eq_or_eq_of_rank_two
    {p : ℕ} [Fact p.Prime] {B C : Subgroup G}
    (hR : solvableRadical G = ⊥) (hr : primeRank p G ≤ 2)
    (hpos : ∀ D : Subgroup G, D.IsCComponent → 0 < primeRank p D)
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hBC : B ≠ C)
    {D : Subgroup G} (hD : D.IsCComponent) : D = B ∨ D = C := by
  by_contra hn
  have hDB : D ≠ B := fun he => hn (Or.inl he)
  have hDC : D ≠ C := fun he => hn (Or.inr he)
  have hadd := hB.primeRank_triple_le (p := p) hR hC hD hBC hDB.symm hDC.symm
  have hb := hpos B hB
  have hc := hpos C hC
  have hd := hpos D hD
  omega

omit [Finite G] in
/-- An exhaustive component pair generates the layer. -/
theorem cComponentLayer_eq_sup_of_pair {B C : Subgroup G}
    (hB : B.IsCComponent) (hC : C.IsCComponent)
    (hall : ∀ D : Subgroup G, D.IsCComponent → D = B ∨ D = C) :
    cComponentLayer G = B ⊔ C := by
  apply le_antisymm
  · apply sSup_le
    intro D hD
    rcases hall D hD with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_cComponentLayer hB) (le_cComponentLayer hC)

/-- The layer has trivial centralizer in a radical-free finite group. -/
theorem centralizer_cComponentLayer_eq_bot_of_radical_eq_bot
    (hR : solvableRadical G = ⊥) :
    centralizer (cComponentLayer G : Set G) = ⊥ := by
  let := cComponentLayer_characteristic (G := G)
  have hf : generalizedFitting G = cComponentLayer G := by
    rw [generalizedFitting,
      ← cComponentLayer_eq_componentLayer_of_solvableRadical_eq_bot hR]
    exact sup_eq_right.mpr ((le_solvableRadical (fittingSubgroup G)
      inferInstance inferInstance).trans (hR.le.trans bot_le))
  have hc : centralizer (cComponentLayer G : Set G) ≤ cComponentLayer G := by
    rw [← hf]
    exact centralizer_generalizedFitting_le G
  have ha : IsMulCommutative (centralizer (cComponentLayer G : Set G)) :=
    le_centralizer_iff_isMulCommutative.mp (centralizer_le hc)
  let := ha
  let : Group.IsSolvable (centralizer (cComponentLayer G : Set G)) :=
    Group.isSolvable_of_comm ha.is_comm.comm
  exact le_bot_iff.mp ((le_solvableRadical _ inferInstance inferInstance).trans hR.le)

/-- A two-group outer action identifies the radical-free layer with the residual. -/
theorem cComponentLayer_eq_residual_of_radical_eq_bot_of_outer_two
    (hR : solvableRadical G = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer (cComponentLayer G))) :
    cComponentLayer G = solvableResidual G := by
  let := cComponentLayer_characteristic (G := G)
  let : Group.IsPerfect (cComponentLayer G) := cComponentLayer_isPerfect
  have hp : IsPGroup 2 (G ⧸ cComponentLayer G) := ho.of_injective
    (MulAut.outerAction (cComponentLayer G)) (MulAut.outerAction_injective _
      (centralizer_cComponentLayer_eq_bot_of_radical_eq_bot hR))
  let : Group.IsNilpotent (G ⧸ cComponentLayer G) := hp.isNilpotent
  exact le_antisymm (le_solvableResidual_of_isPerfect _)
    (solvableResidual_le_of_solvable_quotient _)
end Subgroup
