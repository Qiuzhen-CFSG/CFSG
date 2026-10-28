module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.SporadicFour.OddSubgroups
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates

/-!
# J₄ is not an ordinary rank-one model

The actual binary matrix carrier contains the checked subgroup of order 27.
Its commutator is nonidentity: the normal forms with coordinates (0,0,1)
and (0,0,0) are distinct. Thus the subgroup is noncyclic, contradicting the
odd-subgroup structure of any ordinary PSL₂ model.

The two generator identities required by the local certificates are
supplied by the checked ATLAS matrix identities, without ambient order
or simplicity assumptions.

Source: Aschbacher–Smith, 1.1.5(3)(f), printed pp.501–503, compared with
15.4.20, printed p.1164. The local words are ATLAS `J4G1-max10W1`;
R. A. Wilson, S. J. Nickerson and J. N. Bray. Their attribution and
kernel certificates remain in the imported Janko4 modules.
-/

@[expose] public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels

set_option maxRecDepth 2000 in
private theorem j4_local_not_cyclic :
    ¬ IsCyclic (Janko4.Simplicity.threeLocalSubgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four) := by
  intro hc
  let := hc
  let hA := Janko4.matrixA_mul_self
  let hB := Janko4.matrixB_pow_four
  let u : Janko4.Simplicity.threeLocalSubgroup hA hB :=
    ⟨_, Janko4.Simplicity.threeLocalU_mem hA hB⟩
  let v : Janko4.Simplicity.threeLocalSubgroup hA hB :=
    ⟨_, Janko4.Simplicity.threeLocalV_mem hA hB⟩
  have huv : Janko4.Simplicity.threeLocalU hA hB * Janko4.Simplicity.threeLocalV hA hB =
      Janko4.Simplicity.threeLocalV hA hB * Janko4.Simplicity.threeLocalU hA hB := by
    have he : u * v = v * u := mul_comm u v
    have hv := congrArg (Janko4.Simplicity.threeLocalSubgroup hA hB).subtype he
    exact hv
  have hz : Janko4.Simplicity.threeLocalZ hA hB = 1 := by
    change (Janko4.Simplicity.threeLocalU hA hB)⁻¹ *
      (Janko4.Simplicity.threeLocalV hA hB)⁻¹ *
      Janko4.Simplicity.threeLocalU hA hB * Janko4.Simplicity.threeLocalV hA hB = 1
    calc
      _ = (Janko4.Simplicity.threeLocalU hA hB)⁻¹ *
          (Janko4.Simplicity.threeLocalV hA hB)⁻¹ *
          (Janko4.Simplicity.threeLocalU hA hB * Janko4.Simplicity.threeLocalV hA hB) := by simp only [mul_assoc]
      _ = 1 := by rw [huv]; simp
  have he := Janko4.Simplicity.threeLocalNormalForm_injective hA hB
    (a₁ := (0, 0, 1)) (a₂ := (0, 0, 0)) (by
      simpa only [Janko4.Simplicity.threeLocalNormalForm, Fin.val_zero, Fin.val_one,
        pow_zero, pow_one, one_mul, mul_one] using hz)
  exact (by decide : ((0, 0, 1) : Fin 3 × Fin 3 × Fin 3) ≠ (0, 0, 0)) he

/-- The actual J₄ matrix carrier is not an ordinary rank-one model. -/
theorem j4_rank_one_separation {q : ℕ}
    (hq : (∃ n : ℕ, Even n ∧ q = 2^n) ∨ q.Prime ∧ Odd q) :
    ¬ ClassicalGroup.IsPSL Janko4.Model 2 q := by
  intro hm
  apply j4_local_not_cyclic
  exact ordinary_rank_one_odd_subgroup_cyclic (r := 3) (by decide)
    (Janko4.Simplicity.threeLocalSubgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (IsPGroup.of_card (n := 3) (Janko4.Simplicity.threeLocal_card
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four)) hq hm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
