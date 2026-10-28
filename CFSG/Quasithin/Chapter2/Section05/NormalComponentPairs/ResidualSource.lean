module
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.Source
public import Theory.GroupTheory.FourNormalizerResidual

/-!
# The original largest-pair residual and four-core

The forward pair classification constructs E in the original S∩K and
identifies both normalizers. The actual small-component model theorem
identifies N_K(E) with S₄. Normality and H=KS then identify the pair's
residual with A₄ and its embedded two-core with E=C_K(E).
This discharges the complete forward structural inputs used in 2.5.15.
Source: Aschbacher--Smith 2.5.12(1--2),(4), printed pp.557--558.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentSelection ComponentRefinement
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

/-- The actual original-source pair, residual, residual core and component centralizer. -/
theorem largest_pair_four_structure_of_source
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H)
    (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    ∃ E : Subgroup G, E ≤ (S : Subgroup H).map H.subtype ⊓ K ∧ IsKleinFour E ∧
      L = H ⊓ normalizer (E : Set G) ∧
      U = (S : Subgroup H).map H.subtype ⊓ normalizer (E : Set G) ∧
      Nonempty (pResidual 2 L ≃* alternatingGroup (Fin 4)) ∧
      twoCore ((pResidual 2 L).map L.subtype) = E ∧ K ⊓ centralizer (E : Set G) = E := by
  obtain ⟨E,hES,hE,hL,hU,_⟩ := largest_pair_four_normalizers_of_source c hG hempty hgen hb hp hUS
  let := hE
  have hEK : E ≤ K := hES.trans inf_le_right
  have hm := ComponentSelection.MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  obtain ⟨e⟩ := ComponentSelection.MathieuSourceSetup.four_normalizer c hm E hEK
  let D := K ⊓ normalizer (E : Set G)
  have hh : D.subgroupOf K = normalizer (E.subgroupOf K : Set K) := by
    change (K ⊓ normalizer (E : Set G)).subgroupOf K = _
    rw [inf_subgroupOf_left, subgroupOf_normalizer_eq hEK]
  let eD : D ≃* Equiv.Perm (Fin 4) :=
    ((subgroupOfEquivOfLe (show D ≤ K from inf_le_left)).symm.trans
      (MulEquiv.subgroupCongr hh)).trans e
  obtain ⟨hr,hc,hcent⟩ := residual_four_normalizer_of_normal_supplement H K
    ((S : Subgroup H).map H.subtype) E c.component_le hgen
    (S.isPGroup'.map H.subtype) hEK eD
  rw [← hL] at hr hc
  exact ⟨E,hES,hE,hL,hU,hr,hc,hcent⟩

end CFSG.Quasithin.Chapter2.Section05
