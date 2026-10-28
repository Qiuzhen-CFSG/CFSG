module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.GroupTheory.PCoreLocalSetup
import Mathlib.Tactic.FinCases

/-!
# The concrete line-parabolic two-core in SL₃(2)

The stabilizer of the plane v₂ = 0 has two-core equal to the range of the
shear map `(a,b) ↦ [[1,0,a],[0,1,b],[0,0,1]]` from `SmallModules`.
Both sides of the equality are subgroups of the actual matrix group SL₃(2).

The shears are precisely the pointwise fixer of the plane, hence are normal
in its setwise stabilizer. Their order four puts them in its two-core.
Conversely, the upper triangular subgroup has order eight and is Sylow in
the order-24 parabolic. The two-core lies in this Sylow subgroup and its
conjugate swapping the first two coordinates. The resulting matrix equations
force a shear.

This is the concrete radical calculation used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.19, printed p.953
(combined manuscript of 1 March 2004). The compatible source marking and
transport from the source local group are separate from this intrinsic result.
-/

open Matrix
open scoped Pointwise
namespace Matrix.PSL3Two

private theorem mem_R_iff_fixes (g : SL) :
    g ∈ BinaryLinearThree.R ↔
      ∀ v : Fin 3 → ZMod 2, v 2 = 0 → g • v = v := by
  constructor
  · rintro ⟨c, rfl⟩ v hv
    change !![1,0,c.toAdd.1; 0,1,c.toAdd.2; 0,0,1].mulVec v = v
    ext i
    fin_cases i <;>
      simp [mulVec, dotProduct, Fin.sum_univ_three, hv]
  · intro hf
    have h0 := hf ![1, 0, 0] (by simp)
    have h1 := hf ![0, 1, 0] (by simp)
    have hc0 : ∀ i, g.val i 0 = (![1, 0, 0] : Fin 3 → ZMod 2) i := by
      intro i
      simpa [SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_three]
        using congrFun h0 i
    have hc1 : ∀ i, g.val i 1 = (![0, 1, 0] : Fin 3 → ZMod 2) i := by
      intro i
      simpa [SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_three]
        using congrFun h1 i
    have h22 : g.val 2 2 = 1 := by
      have hd := g.property
      rw [det_fin_three] at hd
      simpa [hc0, hc1] using hd
    refine ⟨Multiplicative.ofAdd (g.val 0 2, g.val 1 2), ?_⟩
    apply Subtype.ext
    change !![1,0,g.val 0 2; 0,1,g.val 1 2; 0,0,1] = g.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hc0, hc1, h22]

private theorem R_le_line : BinaryLinearThree.R ≤ lineParabolicSL := by
  rintro g ⟨c, rfl⟩
  rw [mem_lineParabolicSL_iff]
  exact ⟨rfl, rfl⟩

private theorem R_normal : (BinaryLinearThree.R.subgroupOf lineParabolicSL).Normal := by
  refine ⟨?_⟩
  intro n hn g
  change (g : SL) * (n : SL) * (g : SL)⁻¹ ∈ BinaryLinearThree.R
  rw [mem_R_iff_fixes]
  intro v hv
  have hinv : ((g : SL)⁻¹ • v) 2 = 0 :=
    (MulAction.mem_stabilizer_set.mp
      (lineParabolicSL.inv_mem g.property) v).mpr hv
  have hf := (mem_R_iff_fixes (n : SL)).mp hn _ hinv
  simp only [mul_smul, hf, smul_inv_smul]

private theorem R_le_core : BinaryLinearThree.R ≤ lineParabolicSL.pCoreIn 2 := by
  apply Subgroup.le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 2) BinaryLinearThree.card_R) R_le_line
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer R_le_line).mp R_normal

private theorem core_le_borel : lineParabolicSL.pCoreIn 2 ≤ borelSL := by
  -- Restrict the ambient Borel to the parabolic before using Sylow theory.
  have hcard : Nat.card (borelSL.subgroupOf lineParabolicSL) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show borelSL ≤ lineParabolicSL from inf_le_right)).toEquiv]
    exact card_borelSL
  let sylow : Sylow 2 lineParabolicSL := Sylow.ofCard
    (borelSL.subgroupOf lineParabolicSL) (by
      rw [hcard, card_lineParabolicSL]
      decide +kernel)
  have hle := Subgroup.pCoreIn_le_sylow lineParabolicSL sylow
  simpa only [sylow, Sylow.coe_ofCard,
    Subgroup.map_subgroupOf_eq_of_le (show borelSL ≤ lineParabolicSL from inf_le_right)]
    using hle

private theorem core_le_R : lineParabolicSL.pCoreIn 2 ≤ BinaryLinearThree.R := by
  rintro g ⟨x, hx, rfl⟩
  have hb := core_le_borel (Subgroup.mem_map_of_mem lineParabolicSL.subtype hx)
  obtain ⟨h10, h20, h21⟩ := (mem_borelSL_iff _).mp hb
  change x.val.val 1 0 = 0 at h10
  change x.val.val 2 0 = 0 at h20
  change x.val.val 2 1 = 0 at h21
  -- Normality forces membership in the conjugate Borel as well.
  let s : lineParabolicSL :=
    ⟨⟨!![0,1,0; 1,0,0; 0,0,1], by decide⟩,
      (mem_lineParabolicSL_iff _).mpr ⟨rfl, rfl⟩⟩
  have hsinv : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    apply Subtype.ext
    decide
  have hc : s * x * s⁻¹ ∈ pCore 2 lineParabolicSL :=
    Subgroup.Normal.conj_mem inferInstance x hx s
  have hb' := core_le_borel (Subgroup.mem_map_of_mem lineParabolicSL.subtype hc)
  have h01 := ((mem_borelSL_iff _).mp hb').1
  rw [hsinv] at h01
  change ((!![0,1,0; 1,0,0; 0,0,1] * x.val.val *
    !![0,1,0; 1,0,0; 0,0,1]) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 at h01
  simp [Matrix.mul_apply, vecMul, dotProduct, Fin.sum_univ_three] at h01
  have hd := x.val.property
  rw [det_fin_three] at hd
  simp only [h10, h20, h21, h01, mul_zero, zero_mul, sub_zero, add_zero] at hd
  have hdiag : ∀ a b c : ZMod 2, a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1 := by
    decide
  obtain ⟨h00, h11, h22⟩ := hdiag _ _ _ hd
  refine ⟨Multiplicative.ofAdd (x.val.val 0 2, x.val.val 1 2), ?_⟩
  apply Subtype.ext
  change !![1,0,x.val.val 0 2; 0,1,x.val.val 1 2; 0,0,1] = x.val.val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, h10, h20, h21, h01]

/-- The ambient image of the line stabilizer's intrinsic two-core is the shear subgroup. -/
public theorem lineParabolicSL_pCoreIn_two_eq_R :
    lineParabolicSL.pCoreIn 2 = BinaryLinearThree.R :=
  le_antisymm core_le_R R_le_core

end Matrix.PSL3Two
