module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PointParabolic
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PlaneParabolic
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel

/-!
# Perfect subgroups of binary unitary-four two-locals

Every two-local lies in a conjugate point or plane parabolic. Perfectness
kills the scalar character of the point stabilizer and the determinant of
the plane restriction. Both resulting maps have two-group kernel and SL₂
target, so every odd-prime rank is at most one.

Source: the unitary parabolic calculation used in Aschbacher--Smith 4.4.12,
printed p.622, with the full parabolic conventions of F.1.12(6).
-/

public section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PerfectSubgroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)

theorem pointLocal_odd_primeRank_le_one {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (UnitaryFourPointLocal.localSU F (UnitaryFourFlag.form F σ hσ)) ≤ 1 := by
  let f := (UnitaryFourPointQuotient.middleEquivSL F σ hσ).toMonoidHom.comp
    (UnitaryFourPointQuotient.middleSU F σ hσ)
  apply Matrix.SL2.primeRank_le_one_of_two_kernel ho f
  dsimp only [f]
  rw [MonoidHom.ker_comp_of_injective _ _
    (UnitaryFourPointQuotient.middleEquivSL F σ hσ).injective,
    UnitaryFourPointQuotient.middleSU_ker]
  exact PointParabolic.radical_isTwoGroup F σ hσ

theorem perfect_point_odd_primeRank_le_one {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (f : H →* (UnitaryFourFlag.form F σ hσ).specialSubgroup)
    (hf : Function.Injective f)
    (hle : f.range ≤ UnitaryFourFlag.pointParabolicSU F (UnitaryFourFlag.form F σ hσ)) :
    primeRank p H ≤ 1 := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hl := (le_map_solvableResidual_of_isPerfect f.range _ hle).trans
    (UnitaryFourPointResidual.pointParabolic_solvableResidual_le F _)
  let j := f.codRestrict _ (fun x => hl ⟨x,rfl⟩)
  have hj : Function.Injective j := fun _ _ h => hf (congrArg Subtype.val h)
  exact (primeRank_le_of_injective p j hj).trans
    (pointLocal_odd_primeRank_le_one σ hσ ho)

theorem perfect_plane_odd_primeRank_le_one {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (f : H →* (UnitaryFourFlag.form F σ hσ).specialSubgroup)
    (hf : Function.Injective f)
    (hle : f.range ≤ UnitaryFourFlag.planeParabolicSU F (UnitaryFourFlag.form F σ hσ)) :
    primeRank p H ≤ 1 := by
  let j := f.codRestrict _ (fun x => hle ⟨x,rfl⟩)
  have hj : Function.Injective j := fun _ _ h => hf (congrArg Subtype.val h)
  let r := (UnitaryFourPlaneLocal.restriction F (UnitaryFourFlag.form F σ hσ)).comp j
  let d := (GeneralLinearGroup.det (n := Fin 2) (R := F)).comp r
  have hd (x : H) : d x = 1 :=
    Abelianization.commutator_subset_ker d Group.IsPerfect.mem_commutator
  let k : H →* (GeneralLinearGroup.det (n := Fin 2) (R := F)).ker :=
    r.codRestrict _ hd
  let s := (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm.toMonoidHom.comp k
  have hk : s.ker = r.ker := by
    ext x
    change (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm (k x) = 1 ↔ r x = 1
    rw [MulEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  apply Matrix.SL2.primeRank_le_one_of_two_kernel ho s
  rw [hk]
  exact (PlaneParabolic.kernel_isTwoGroup F σ hσ).comap_of_injective j hj

theorem perfect_twoLocal_odd_primeRank_le_one
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, σ x = x ^ (2 ^ n))
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (f : H →* (UnitaryFourFlag.form F σ hσ).specialSubgroup)
    (hf : Function.Injective f) (M : Subgroup (UnitaryFourFlag.form F σ hσ).specialSubgroup)
    (hM : IsTwoLocal M) (hle : f.range ≤ M) : primeRank p H ≤ 1 := by
  obtain ⟨g,hg⟩ := TwoLocalCover.twoLocal_parabolic_cover σ hσ n hn hcard hconj M hM
  let j := (MulAut.conj g⁻¹).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.conj g⁻¹).injective.comp hf
  have hc (P : Subgroup (UnitaryFourFlag.form F σ hσ).specialSubgroup)
      (h : M ≤ P.map (MulAut.conj g).toMonoidHom) : j.range ≤ P := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := h (hle ⟨x,rfl⟩)
    change g⁻¹ * f x * (g⁻¹)⁻¹ ∈ P
    rw [← he]
    simpa [MulAut.conj_apply, mul_assoc] using hy
  rcases hg with hp | hp
  · exact perfect_point_odd_primeRank_le_one σ hσ ho j hj (hc _ hp)
  · exact perfect_plane_odd_primeRank_le_one σ hσ ho j hj (hc _ hp)
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PerfectSubgroups
