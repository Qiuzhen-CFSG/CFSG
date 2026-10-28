module

public import Theory.ElementaryAbelian.Basic
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupCoverage.Cardinality

/-!
# The three-row cover of Sylow-normal four-groups in Held

Conjugate an arbitrary Sylow two-subgroup to the certified literal
representative. A four-group that it normalizes then restricts to a normal
elementary subgroup of that representative. The explicit enumeration premise
places it in the 22-row table, and the certified cardinality filter leaves
only rows 1, 2 and 3. Mapping back through the actual subtype inclusion gives
the required ambient conjugacy equality.

The only remaining premise is the intrinsic enumeration. This conditional
refinement is used by the Held branch of Aschbacher--Smith 15.3.43, printed
p.1140, via GLS3 Table 5.3p. The final source exclusion also requires the
three normalizer arithmetic calculations; it is assembled by the chapter
consumer, separately from this concrete subgroup cover.
-/

open Subgroup
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open LocalPairs.SylowGeometry.Calculations
open scoped Pointwise

/-- Every Sylow-normal four-group is conjugate to row 1, 2 or 3, conditional
only on enumeration of the normal elementary subgroups of the fixed Sylow.
Normality is relative to that representative, never normality in Held. -/
public theorem four_group_conjugate_rows_of_enumeration
    (henum : ∀ R : Subgroup representative, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R → ∃ j : Fin 22, R = entry j)
    (T : Sylow 2 He) (W : Subgroup He)
    (hWT : W ≤ (T : Subgroup He)) (hWE : IsElementaryAbelian 2 W)
    (hWc : Nat.card W = 4) (hTN : (T : Subgroup He) ≤ normalizer (W : Set He)) :
    ∃ (j : Fin 22) (g : He), (j = 1 ∨ j = 2 ∨ j = 3) ∧
      W.map (MulAut.conj g).toMonoidHom = ambient j := by
  obtain ⟨P, hP⟩ := exists_representative_sylow representative_isPGroup
    InnerNormalizer.normalizer_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq He T P
  have hTP : (T : Subgroup He).map (MulAut.conj g).toMonoidHom = representative := by
    change ((g • T : Sylow 2 He) : Subgroup He) = representative
    rw [hg, hP]
  let U := W.map (MulAut.conj g).toMonoidHom
  have hUP : U ≤ representative := by
    rw [← hTP]
    exact map_mono hWT
  have hPN : representative ≤ normalizer (U : Set He) := by
    rw [← hTP, ← map_equiv_normalizer_eq W (MulAut.conj g)]
    exact map_mono hTN
  let R := U.subgroupOf representative
  let : IsElementaryAbelian 2 W := hWE
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hRE : IsElementaryAbelian 2 R := IsElementaryAbelian.subgroupOf hUP
  have hRn : R.Normal := (normal_subgroupOf_iff_le_normalizer hUP).mpr hPN
  have hRc : Nat.card R = 4 := by
    calc
      Nat.card R = Nat.card U := Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv
      _ = Nat.card W := card_map_of_injective (MulAut.conj g).injective
      _ = 4 := hWc
  have hRne : R ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hRc
    omega
  obtain ⟨j, hj⟩ := henum R hRne hRn hRE
  refine ⟨j, g, entry_card_four_rows j (hj ▸ hRc), ?_⟩
  change U = (entry j).map representative.subtype
  rw [← hj]
  exact (map_subgroupOf_eq_of_le hUP).symm

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
