module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ExtensionModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ExtensionModels.UnitaryPlacement.Borel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.UnitaryLocal.Placement
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Local
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData

/-!
# Local placement in the split unitary extension

Assume Y₊ lies in the actual PSU₃(q) component, with q = 2ⁿ congruent to -1
modulo three. The relative component Sylow is S ∩ L. Its unique proper
Sylow overgroup contains M ∩ L, hence all the cubic generators of
Y₊ = theta(M ∩ I). The local theta identity also makes S normalize Y₊,
so V₂ = [V₂,Y₊] lies in Y₊ and therefore in S ∩ L.

The concrete unitary calculation says those cubic generators fix every
involution in S ∩ L. Thus they centralize V₂, contradicting its nontrivial
commutator identity. In particular failure of theta(I) containment implies
Y₊ is not contained in L. The final corollary supplies this noncontainment
to the existing literal PGU extension theorem and constructs the compatible
outer diagonal actor on L/O₂(L), over the same field and with the same q.

`LocalSetup` and `PlaneData` retain genuine earlier source conclusions.
Only their relative component/Sylow data, local theta and normalization,
and moving elementary plane are used here. No rank-two-Y₊ assertion of
15.3.12, minimality of I, later containment result, or actor is assumed.
The signed restriction and extension equivalence remain explicit inputs;
their ModelIntersection and A.3.18 assembly is owned by the parent.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.2,
15.3.11, 15.3.25, and the selected component preceding 15.3.33, printed
pp.1121--1125 and 1134; 15.3.43(b) and its signed reduction on p.1139;
A.3.18(2), printed pp.51--52. The proof strengthens the needed local
implication rather than importing the later conclusion of 15.3.43.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ExtensionModels.UnitaryPlacement

variable {F : Type} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

open RankOne.DiagonalExclusion
open CFSG.Quasithin.ChapterF.Source

include hJ in
/-- The genuine moving plane excludes containment in the signed unitary
component. This is stronger than the implication needed when theta(I) is
not contained in L; no assumption about theta(I) is required. -/
theorem yplus_not_le_of_unitary
    {G : Type*} [Group G] [Finite G] (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (v : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    [Finite F] {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hfrob : ∀ x, J.conj x = x ^ (2 ^ n)) (hq : (2 ^ n) % 3 = 2)
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J) : ¬ d.Yplus ≤ L := by
  intro hYL
  obtain ⟨Q, hQ⟩ := h.sylow
  obtain ⟨P, hP⟩ := UnitaryLocal.component_sylow h.component_le h.component.1 Q hQ
  have hfacts := rankOneSylowFacts_of_equiv P e
    (rankOneSylowFacts_psu3 J n hn hcard hfrob _)
  have hMproper : d.M.subgroupOf L < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    apply h.component_outside
    intro x hx
    have hh : (⟨x, hx⟩ : L) ∈ d.M.subgroupOf L := he.symm ▸ mem_top _
    exact hh
  have hPM : (P : Subgroup L) ≤ d.M.subgroupOf L := by
    rw [hP]
    exact subgroupOf_mono L h.sylow_le
  have hMB := hfacts.unique_maximal _ hPM hMproper
  have hVY : d.V₂ ≤ d.Yplus := by
    rw [← v.second_commutator]
    exact le_normalizer_iff_commutator_le_right.mp
      ((v.second_le.trans (le_inf h.sylow_le h.sylow_le_overgroup)).trans h.local_normalizes)
  have hVL : d.V₂ ≤ L := hVY.trans hYL
  have hcentral : d.Yplus ≤ centralizer (d.V₂ : Set G) := by
    rw [← h.theta_eq]
    apply (closure_le _).mpr
    intro y hy
    have hyY : y ∈ d.Yplus := h.theta_eq ▸ subset_closure hy
    let yL : L := ⟨y, hYL hyY⟩
    have hyB : yL ∈ normalizer (P : Set L) := hMB hy.1.1
    have hy3 : yL ^ 3 = 1 := Subtype.ext (hy.2 ▸ pow_orderOf_eq_one y)
    apply mem_centralizer_iff.mpr
    intro w hw
    let wL : L := ⟨w, hVL hw⟩
    have hwP : wL ∈ P := by
      change wL ∈ (P : Subgroup L)
      rw [hP]
      exact v.second_le hw
    let : IsElementaryAbelian 2 d.V₂ := v.second_elementary
    have hw2 : wL ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian w hw)
    exact congrArg Subtype.val
      (cubic_commutes_of_mem_sylowNormalizer J hJ hn hcard hfrob hq e P hyB hy3 hwP hw2)
  have hvbot : d.V₂ = ⊥ := v.second_commutator.symm.trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcentral))
  have hcardV := v.second_card
  rw [hvbot] at hcardV
  simp at hcardV


include hJ in
/-- Discharge the local noncontainment premise of the literal PGU actor theorem.
Both the actual component model and its two-core quotient coordinates are
retained, as is the unmarked equivalence with O^{3'}(I/O_{3'}(I)). -/
theorem actor_of_pgu
    {G : Type*} [Group G] [Finite G] (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (v : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    (hrankL : 2 ≤ primeRank 3 L)
    [Finite F] {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hfrob : ∀ x, J.conj x = x ^ (2 ^ n)) (hq : (2 ^ n) % 3 = 2)
    (componentModel : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (quotientModel : (L ⧸ pCore 2 L) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (extensionModel : Residual I ≃* J.unitarySubgroup.map Matrix.ProjGenLinGroup.mk) :
    ∃ y ∈ d.Yplus, orderOf y = 3 ∧ y ∉ L ∧ UnitaryDiagonalOnTwoQuotient L y (2 ^ n) := by
  exact unitary_actor_of_pgu h.theta_eq
    (yplus_not_le_of_unitary J hJ d h v hn hcard hfrob hq componentModel)
    h.component_le h.component h.odd_core hrankL h.rank_overgroup h.orbit_bound
    J hJ hn hcard hfrob extensionModel quotientModel

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ExtensionModels.UnitaryPlacement
