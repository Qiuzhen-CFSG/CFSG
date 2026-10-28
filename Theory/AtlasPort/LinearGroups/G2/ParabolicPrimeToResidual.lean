module

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Perfectness
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Nonsolvable prime-to-three residuals in full G₂ parabolics

Over a finite field of characteristic two with more than two elements,
each full root parabolic contains its concrete local subgroup surjecting
onto SL₂. This SL₂ is simple and perfect, and its explicit order-three
matrix makes its prime-to-three residual the whole group. Functoriality
and surjective transport of the residual therefore rule out solvability
of the parabolic residual.

The argument works for every nonbinary field; no three-rank estimate or
field-degree restriction replaces the residual calculation. It refines the
intrinsic calculation in the Chapter 15 `ResidualModels.G2` inspection to
the `primeToResidual` interface without importing chapter results.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the inspection
in 15.3.28, printed p.1131, and the local quotients in F.1.12(I)(3),
printed pp.262–264. The imported root models and quotient calculations
retain the ATLAS attribution and license in LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Atlas.G2.LieParabolicSetup

private theorem residual_solvable_of_injective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) [Group.IsSolvable (primeToResidual 3 B)] :
    Group.IsSolvable (primeToResidual 3 A) := by
  let g : primeToResidual 3 A →* primeToResidual 3 B :=
    (f.comp (primeToResidual 3 A).subtype).codRestrict _
      (fun a => map_primeToResidual_le_of_hom 3 f (mem_map_of_mem f a.property))
  exact Group.isSolvable_of_isSolvable_injective (f := g)
    (fun a b h => Subtype.ext (hf (congrArg Subtype.val h)))

private theorem residual_solvable_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hf : Function.Surjective f) [Group.IsSolvable (primeToResidual 3 A)]
    (hB : primeToResidual 3 B = ⊤) : Group.IsSolvable B := by
  let g := f.comp (primeToResidual 3 A).subtype
  apply Group.isSolvable_of_surjective (f := g)
  intro b
  have hb : b ∈ (primeToResidual 3 A).map f := by
    rw [map_primeToResidual_of_surjective 3 f hf, hB]
    trivial
  obtain ⟨a, ha, he⟩ := hb
  exact ⟨⟨a, ha⟩, he⟩

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem field_four (hq : 2 < Nat.card F) : 4 ≤ Nat.card F := by
  obtain ⟨n, hn, he⟩ := field_card (F := F)
  have hn2 : 2 ≤ n := by
    by_contra h
    have : n = 1 := by omega
    simp [this] at he
    omega
  rw [he]
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hn2

private theorem sl_threeResidual (hq : 2 < Nat.card F) :
    primeToResidual 3 SL(2,F) = ⊤ := by
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (field_four hq)
  let : IsSimpleGroup SL(2,F) := (longSLEquivPSL (F := F)).isSimpleGroup
  let x : SL(2,F) := ⟨!![0,-1;1,-1], by simp [Matrix.det_fin_two]⟩
  have hx : x ^ 3 = 1 := by
    apply Subtype.ext
    change (!![0,-1;1,-1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  have hxne : x ≠ 1 := by
    intro h
    have he := congrArg (fun a : SL(2,F) => a 0 1) h
    simp [x] at he
  rcases (inferInstance : (primeToResidual 3 SL(2,F)).Normal).eq_bot_or_eq_top with h | h
  · exact (hxne (h.le (mem_primeToResidual_of_pow (n := 1)
      (by simpa only [pow_one] using hx)))).elim
  · exact h

/-- For every nonbinary finite field of characteristic two, both full root
parabolics have nonsolvable prime-to-three residual. -/
theorem parabolic_primeToResidual_not_solvable (hq : 2 < Nat.card F) (i : Fin 2) :
    ¬ Group.IsSolvable (primeToResidual 3
      (if i = 0 then parabolic₁ (F := F) else parabolic₂ : Subgroup (Model F))) := by
  intro hs
  let P : Subgroup (Atlas.G2.Model F) := if i = 0 then parabolic₁ else parabolic₂
  let : Group.IsSolvable (primeToResidual 3 P) := hs
  let : Group.IsPerfect (local₁ (F := F)) := local₁_isPerfect hq
  let : Group.IsPerfect SL(2,F) := Group.IsPerfect.ofSurjective shortSLHom_surjective
  let : Nontrivial SL(2,F) := (longSLEquivPSL (F := F)).toEquiv.nontrivial
  apply Group.IsPerfect.not_isSolvable SL(2,F)
  fin_cases i
  · have hle : local₁ (F := F) ≤ P := by
      change local₁ ≤ parabolic₁
      rw [← local₁_sup_borel]
      exact le_sup_left
    let : Group.IsSolvable (primeToResidual 3 (local₁ (F := F))) :=
      residual_solvable_of_injective (inclusion hle) (inclusion_injective hle)
    exact residual_solvable_of_surjective shortSLHom shortSLHom_surjective (sl_threeResidual hq)
  · have hle : local₂ (F := F) ≤ P := by
      change local₂ ≤ parabolic₂
      rw [← local₂_sup_borel]
      exact le_sup_left
    let : Group.IsSolvable (primeToResidual 3 (local₂ (F := F))) :=
      residual_solvable_of_injective (inclusion hle) (inclusion_injective hle)
    exact residual_solvable_of_surjective longSLHom longSLHom_surjective (sl_threeResidual hq)

end Atlas.G2.LieParabolicSetup
