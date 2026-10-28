module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.LinearLeviLocals
import all CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.LinearLeviLocals
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PerfectSubgroups

/-!
# The unitary-four linear Levi obstruction

The full two-local normalizer is placed in the actual point or plane
parabolic of SU₄. Perfectness removes the scalar character or determinant.
The remaining map to binary SL₂ has solvable kernel, including the kernel
of the original residual representation. The simple quotient with a
nonidentity two-square is therefore impossible. No full Sylow or radical
normalizer hypothesis is added.

Source: Aschbacher--Smith 4.4.12, printed p.622, and F.1.12(6), pp.262--264.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
noncomputable section

variable {A S : Type*} [Group A] [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect A]

/-- The point and plane parabolics both exclude the marked simple quotient. -/
theorem no_unitary_four_local
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : A →* S) (hπ : Function.Surjective π)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x, σ x = x ^ (2 ^ n))
    (P : Subgroup (UnitaryFourFlag.form E σ hσ).specialSubgroup)
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (r : A →* (UnitaryFourFlag.form E σ hσ).specialSubgroup) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) : False := by
  let J := UnitaryFourFlag.form E σ hσ
  obtain ⟨g,hg⟩ := UnitaryFourConverse.TwoLocalCover.twoLocal_parabolic_cover
    σ hσ n hn hcard hconj (normalizer (P : Set _)) ⟨P,hne,hp,rfl⟩
  let j := (MulAut.conj g⁻¹).toMonoidHom.comp r
  let : Group.IsSolvable j.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show j.ker ≤ r.ker from fun x hx => by
      change (MulAut.conj g⁻¹) (r x) = 1 at hx
      exact (MulAut.conj g⁻¹).injective (hx.trans (MulAut.conj g⁻¹).map_one.symm)))
    (inclusion_injective _)
  have hc (D : Subgroup J.specialSubgroup)
      (hD : normalizer (P : Set _) ≤ D.map (MulAut.conj g).toMonoidHom) : j.range ≤ D := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hD (hr ⟨x,rfl⟩)
    change g⁻¹ * r x * (g⁻¹)⁻¹ ∈ D
    rw [← he]
    simpa [MulAut.conj_apply,mul_assoc] using hy
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  rcases hg with hg | hg
  · have hi := (le_map_solvableResidual_of_isPerfect j.range _ (hc _ hg)).trans
      (UnitaryFourPointResidual.pointParabolic_solvableResidual_le E J)
    let q := (UnitaryFourPointQuotient.middleEquivSL E σ hσ).toMonoidHom.comp
      (UnitaryFourPointQuotient.middleSU E σ hσ)
    have hk : IsPGroup 2 q.ker := by
      dsimp only [q]
      rw [MonoidHom.ker_comp_of_injective _ _
        (UnitaryFourPointQuotient.middleEquivSL E σ hσ).injective,
        UnitaryFourPointQuotient.middleSU_ker]
      exact UnitaryFourConverse.PointParabolic.radical_isTwoGroup E σ hσ
    let := hk.isNilpotent
    exact no_quotient_in_local hS hexp π hπ j _ hi q
  · let jD := j.codRestrict _ (fun x => hc _ hg ⟨x,rfl⟩)
    let : Group.IsSolvable jD.ker := Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show jD.ker ≤ j.ker from fun _ hx => congrArg Subtype.val hx))
      (inclusion_injective _)
    let q := UnitaryFourPlaneLocal.restriction E J
    have hk : IsPGroup 2 q.ker := UnitaryFourConverse.PlaneParabolic.kernel_isTwoGroup E σ hσ
    let := hk.isNilpotent
    let v := q.comp jD
    let : Group.IsSolvable v.ker := by
      change Group.IsSolvable (q.comp jD).ker
      rw [← MonoidHom.comap_ker]
      exact isSolvable_comap_of_solvable_ker jD q.ker
    let d := (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := E)).comp v
    have hd (x : A) : d x = 1 :=
      Abelianization.commutator_subset_ker d Group.IsPerfect.mem_commutator
    let k : A →* (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := E)).ker := v.codRestrict _ hd
    let s := (Matrix.SpecialLinearGroup.determinantKernelEquiv (Fin 2) E).symm.toMonoidHom.comp k
    let : Group.IsSolvable s.ker := Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show s.ker ≤ v.ker from fun x hx => by
        have h : k x = 1 :=
          (Matrix.SpecialLinearGroup.determinantKernelEquiv (Fin 2) E).symm.injective
            ((show s x = 1 from hx).trans (map_one _).symm)
        exact congrArg Subtype.val h))
      (inclusion_injective _)
    exact no_rankOne_quotient_in_binary_linear_two hS hexp π hπ s
end
end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
