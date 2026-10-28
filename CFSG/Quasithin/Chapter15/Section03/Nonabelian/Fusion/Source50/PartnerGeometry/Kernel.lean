module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Intersection
public import Theory.ElementaryAbelian.ExtraspecialAbelianBound

/-!
# Detecting the partner actor kernel through the singular intersection

The intersection E is a maximal abelian subgroup of the extraspecial Uʸ
once its source order is known. An x in X∩Q_H centralizes E modulo Z,
while Uʸ-commutators lie in Zʸ. Since the two central lines are disjoint,
x centralizes E and hence belongs to E. This proves the literal intersection
field in Partner.EarlierGeometry without reusing any later recognition.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
variable {G : Type*} [Group G] (Z ZS : Subgroup G)

/-- Two disjoint central commutator bounds force actual centralization. -/
theorem commutes_of_disjoint_commutator_bounds
    (A B Z₁ Z₂ : Subgroup G) (h₁ : ⁅A,B⁆ ≤ Z₁) (h₂ : ⁅A,B⁆ ≤ Z₂)
    (hd : Disjoint Z₁ Z₂) : A ≤ centralizer (B : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  exact (le_inf h₁ h₂).trans (disjoint_iff.mp hd).le

/-- The extraspecial abelian bound, transported to actual ambient subgroups.
The cardinal identity is exactly the singular half-dimension calculation. -/
theorem ambient_selfCentralizing_of_card_sq [Finite G]
    (P E : Subgroup G) [IsExtraspecial 2 P] [IsMulCommutative E]
    (hEP : E ≤ P) (hZE : center P ≤ E.subgroupOf P)
    (hcard : (Nat.card E)^2 = 2 * Nat.card P) :
    P ⊓ centralizer (E : Set G) = E := by
  let e : E.subgroupOf P ≃* E := subgroupOfEquivOfLe hEP
  let : IsMulCommutative (E.subgroupOf P) :=
    ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)⟩⟩
  have hsize : (Nat.card (E.subgroupOf P))^2 = 2 * Nat.card P := by
    rw [Nat.card_congr e.toEquiv]
    exact hcard
  have hc := extraspecial_two_centralizer_eq_of_card_sq (E.subgroupOf P) hZE hsize
  apply le_antisymm
  · intro x hx
    have hh : (⟨x, hx.1⟩ : P) ∈ centralizer (E.subgroupOf P : Set P) := by
      intro a ha
      exact Subtype.ext (hx.2 a ha)
    rw [hc] at hh
    exact hh
  · exact le_inf hEP E.le_centralizer

/-- A self-centralizing intersection inside Uʸ detects the exact partner
kernel from the original commutator bound [U,Q_H]≤Z. -/
theorem partner_inf_core_of_selfCentralizing (y : G)
    (hUQ : closureU Z ZS ≤ coreQ Z)
    (hEeq : intersectionE Z ZS y = closureU Z ZS ⊓ rightConjugate (closureU Z ZS) y)
    (hcomm : ⁅closureU Z ZS, coreQ Z⁆ ≤ Z)
    (hderived : ⁅rightConjugate (closureU Z ZS) y,
      rightConjugate (closureU Z ZS) y⁆ ≤ rightConjugate Z y)
    (hdis : Disjoint Z (rightConjugate Z y))
    (hself : (rightConjugate (closureU Z ZS) y) ⊓
      centralizer (intersectionE Z ZS y : Set G) ≤ intersectionE Z ZS y) :
    partnerX Z ZS y ⊓ coreQ Z = intersectionE Z ZS y := by
  have hEU : intersectionE Z ZS y ≤ closureU Z ZS := by rw [hEeq]; exact inf_le_left
  have hEUy : intersectionE Z ZS y ≤ rightConjugate (closureU Z ZS) y := by
    rw [hEeq]; exact inf_le_right
  have hXUy : partnerX Z ZS y ≤ rightConjugate (closureU Z ZS) y := map_mono inf_le_left
  have h₁ : ⁅intersectionE Z ZS y, partnerX Z ZS y ⊓ coreQ Z⁆ ≤ Z :=
    (commutator_mono hEU inf_le_right).trans hcomm
  have h₂ : ⁅intersectionE Z ZS y, partnerX Z ZS y ⊓ coreQ Z⁆ ≤ rightConjugate Z y :=
    (commutator_mono hEUy (inf_le_left.trans hXUy)).trans hderived
  have hC := le_centralizer_iff.mp
    (commutes_of_disjoint_commutator_bounds _ _ _ _ h₁ h₂ hdis)
  apply le_antisymm
  · exact (le_inf (inf_le_left.trans hXUy) hC).trans hself
  · exact le_inf inf_le_right (hEU.trans hUQ)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
