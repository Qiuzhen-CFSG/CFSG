module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.MainComparison
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.PLevel0Data
import Mathlib.Tactic.FinCases

/-!
# Identification of the fixed local words with the certified permutations

The tables are identified with the unchanged four local generators through the
fourth ATLAS generator pair. This identifies the whole generated subgroup,
not merely a group of the same order. The inverse point-action convention
preserves products. See `SylowOvergroups.Definitions` for ATLAS attribution.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow
open Theory.GroupTheory
set_option Elab.async false

/-- The faithful permutation map, with the model's declared group instance. -/
@[expose] public def permutation : Model →* Equiv.Perm (Fin 4060) :=
  modelSubgroup.subtype

private theorem main0_perm : permutation max4Generators.1 = Main.gen 0 :=
  Main.generator0_eq.symm

private theorem main1_perm : permutation max4Generators.2 = Main.gen 1 :=
  Main.generator1_eq.symm

@[expose] public def mainLetter : Fin 4 → Model :=
  ![max4Generators.1, max4Generators.2, max4Generators.1⁻¹, max4Generators.2⁻¹]

public theorem mainLetter_mem (i : Fin 4) : mainLetter i ∈ max4 := by
  have hx : max4Generators.1 ∈ max4 := Subgroup.subset_closure (by simp)
  have hy : max4Generators.2 ∈ max4 := Subgroup.subset_closure (by simp)
  fin_cases i
  · exact hx
  · exact hy
  · exact max4.inv_mem hx
  · exact max4.inv_mem hy

public theorem mainLetter_perm (i : Fin 4) :
    permutation (mainLetter i) = Main.gen i := by
  fin_cases i
  · exact Main.generator0_eq.symm
  · exact Main.generator1_eq.symm
  · change permutation (max4Generators.1⁻¹) = Main.gen 2
    rw [map_inv, main0_perm]
    exact (Main.gen_inv 0).symm
  · change permutation (max4Generators.2⁻¹) = Main.gen 3
    rw [map_inv, main1_perm]
    exact (Main.gen_inv 1).symm

private def cachedLocal : Fin 4 → Equiv.Perm (Fin 4060) :=
  let x := Main.gen 0
  let y := Main.gen 1
  ![y * x * y⁻¹, x * y * x * y⁻¹ * x,
    y⁻¹ * x * y⁻¹ * x * y * x * y,
    x * y⁻¹ * x * y * x * y * x * y⁻¹ * x * y]

set_option maxRecDepth 30000 in
private theorem cachedLocal_eq : ∀ i : Fin 4,
    cachedLocal i = P.L0.gen (i.castAdd 4) := by
  have h : ∀ (i : Fin 4) (x : Fin 4060),
      cachedLocal i x = P.L0.gen (i.castAdd 4) x := by
    apply Rudvalis.OrderCertificate.allFin₂
    decide +kernel
  exact fun i => Equiv.ext (h i)

public theorem localGenerators_perm (i : Fin 4) :
    permutation (localGenerators i) = P.L0.gen (i.castAdd 4) := by
  rw [← cachedLocal_eq]
  fin_cases i <;> simp [localGenerators, cachedLocal, map_mul, map_inv,
    main0_perm, main1_perm]

public theorem localLetter_mem (i : Fin 8) : localLetter i ∈ localP := by
  simpa [localWord] using localWord_mem [i]

public theorem localLetter_perm (i : Fin 8) :
    permutation (localLetter i) = P.L0.gen i := by
  have h0 := localGenerators_perm 0
  have h1 := localGenerators_perm 1
  have h2 := localGenerators_perm 2
  have h3 := localGenerators_perm 3
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · change permutation ((localGenerators 0)⁻¹) = P.L0.gen 4
    rw [map_inv, h0]
    exact (P.L0.gen_inv 0).symm
  · change permutation ((localGenerators 1)⁻¹) = P.L0.gen 5
    rw [map_inv, h1]
    exact (P.L0.gen_inv 1).symm
  · change permutation ((localGenerators 2)⁻¹) = P.L0.gen 6
    rw [map_inv, h2]
    exact (P.L0.gen_inv 2).symm
  · change permutation ((localGenerators 3)⁻¹) = P.L0.gen 7
    rw [map_inv, h3]
    exact (P.L0.gen_inv 3).symm

/-- Equality with the image of the exact fixed subgroup. -/
public theorem map_localP : localP.map permutation = P.L0.subgroup := by
  apply le_antisymm
  · rw [localP, MonoidHom.map_closure, ← Set.range_comp]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change permutation (localGenerators i) ∈ P.L0.subgroup
    rw [localGenerators_perm]
    exact ⟨[i.castAdd 4], mul_one _⟩
  · rintro g ⟨w, rfl⟩
    induction w with
    | nil => exact Subgroup.one_mem _
    | cons i w ih =>
      apply Subgroup.mul_mem _ _ ih
      exact ⟨localLetter i, localLetter_mem i, localLetter_perm i⟩

@[expose] public def mainWord (w : List (Fin 4)) : Model := evalWord mainLetter w

public theorem mainWord_mem (w : List (Fin 4)) : mainWord w ∈ max4 := by
  induction w with
  | nil => exact max4.one_mem
  | cons i w ih => exact max4.mul_mem (mainLetter_mem i) ih

public theorem mainWord_perm (w : List (Fin 4)) :
    permutation (mainWord w) = evalWord Main.gen w := by
  induction w with
  | nil => exact map_one _
  | cons i w ih =>
    change permutation (mainLetter i * mainWord w) = _
    rw [map_mul, mainLetter_perm, ih]

public theorem localWord_perm (w : List (Fin 8)) :
    permutation (localWord w) = evalWord P.L0.gen w := by
  induction w with
  | nil => exact map_one _
  | cons i w ih =>
    change permutation (localLetter i * localWord w) = _
    rw [map_mul, localLetter_perm, ih]

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow
