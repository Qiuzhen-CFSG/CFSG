module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.EdgeData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.LocalData
import Mathlib.Tactic.FinCases

/-!
# Placement of the explicit local A₅ generators

Word evaluations identify the two additional elements with their permutation
tables. The edge word centralizes both endpoints; the local involution
centralizes the marked dihedral group and inverts the base generator.
Thus all candidate groups lie in the literal groups required by 47.10.
Source: Aschbacher, *Sporadic Groups*, 47.5 and 47.10, pp.263, 266–267.
-/

public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Subgroup Theory.GroupTheory GeneratorPair

theorem inclusion_word (w : List (Fin 3)) :
    inclusion (evalWord ![a, b, b⁻¹] w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [evalWord, map_mul, ih, evalWord]
    congr 1
    fin_cases i
    · exact generatorA_eq_table
    · exact generatorB_eq_table
    · exact (map_inv inclusion b).trans (congrArg Inv.inv generatorB_eq_table)

theorem inclusion_rotation : inclusion rotation = EdgeData.table0 :=
  (inclusion_word rotationWord).trans (by decide +kernel)

theorem inclusion_edgeExtra : inclusion edgeExtra = EdgeData.table1 :=
  (inclusion_word edgeExtraWord).trans (by decide +kernel)

theorem inclusion_inverter : inclusion inverter = LocalData.table2 :=
  (inclusion_word inverterWord).trans (by decide +kernel)

theorem inclusion_x : inclusion x = LocalData.table0 := by
  simp only [x, map_pow, map_mul, map_inv,
    (show inclusion a = tableA from generatorA_eq_table),
    (show inclusion b = tableB from generatorB_eq_table)]
  decide +kernel

theorem inclusion_y : inclusion y = LocalData.table1 := by
  change inclusion (conjugator * x * conjugator⁻¹) = _
  simp only [conjugator, map_mul, map_inv, inclusion_x,
    (show inclusion a = tableA from generatorA_eq_table),
    (show inclusion b = tableB from generatorB_eq_table)]
  decide +kernel

theorem inclusion_reflection : inclusion reflection = DihedralData.reflectionTable :=
  (inclusion_word reflectionWord).trans (by decide +kernel)

theorem edgeExtra_conj_x : MulAut.conj edgeExtra x = x := by
  apply inclusion_injective
  simp only [MulAut.conj_apply, map_mul, map_inv, inclusion_edgeExtra, inclusion_x]
  decide +kernel

theorem edgeExtra_conj_y : MulAut.conj edgeExtra y = y := by
  apply inclusion_injective
  simp only [MulAut.conj_apply, map_mul, map_inv, inclusion_edgeExtra, inclusion_y]
  decide +kernel

theorem inverter_conj_x : MulAut.conj inverter x = x⁻¹ := by
  apply inclusion_injective
  simp only [MulAut.conj_apply, map_mul, map_inv, inclusion_inverter, inclusion_x]
  decide +kernel

theorem inverter_square : inverter ^ 2 = 1 := by
  apply inclusion_injective
  rw [map_pow, map_one, inclusion_inverter]
  decide +kernel

theorem edgeExtra_mem_E : edgeExtra ∈ E := by
  constructor <;> apply mem_normalizer_iff_map_conj_eq.mpr
  · rw [X, MonoidHom.map_zpowers]
    exact congrArg zpowers edgeExtra_conj_x
  · rw [Y, MonoidHom.map_zpowers]
    exact congrArg zpowers edgeExtra_conj_y

theorem inverter_mem_M : inverter ∈ M := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [X, MonoidHom.map_zpowers]
  exact (congrArg zpowers inverter_conj_x).trans zpowers_inv

theorem inverter_mem_K : inverter ∈ K := by
  have hr : rotation * inverter = inverter * rotation := by
    apply inclusion_injective
    simp only [map_mul, inclusion_rotation, inclusion_inverter]
    decide +kernel
  have hs : reflection * inverter = inverter * reflection := by
    apply inclusion_injective
    simp only [map_mul, inclusion_reflection, inclusion_inverter]
    decide +kernel
  have hb : B ≤ centralizer ({inverter} : Set Carrier) := by
    apply sup_le <;> apply zpowers_le.mpr
    · exact mem_centralizer_singleton_iff.mpr hr
    · exact mem_centralizer_singleton_iff.mpr hs
  apply mem_centralizer_iff.mpr
  intro d hd
  exact mem_centralizer_singleton_iff.mp (hb hd)

theorem edgeCandidate_le_E : edgeCandidate ≤ E :=
  sup_le (zpowers_le.mpr (B_le_E (mem_sup_left (mem_zpowers rotation))))
    (zpowers_le.mpr edgeExtra_mem_E)

theorem localCandidate_le_K : localCandidate ≤ K :=
  sup_le X_sup_Y_le_K (zpowers_le.mpr inverter_mem_K)

theorem vertexCandidate_le_K_inf_M : vertexCandidate ≤ K ⊓ M := by
  apply sup_le
  · exact le_inf (le_sup_left.trans X_sup_Y_le_K) X.le_normalizer
  · exact zpowers_le.mpr ⟨inverter_mem_K, inverter_mem_M⟩

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
