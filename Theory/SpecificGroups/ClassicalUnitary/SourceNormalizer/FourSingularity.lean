module
public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors
public import Theory.Representation.OrthogonalFourMinusRankOne.CartanFixed
public import Theory.SpecificGroups.SL2.UpperUnipotent

open Subgroup Matrix Matrix.SpecialLinearGroup
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Representation.OrthogonalFourMinus.CartanFixed
/-!
# The two Hermitian involution types under compatible automorphisms

A singular Hermitian two-by-two matrix is conjugate under SL₂ to the
upper diagonal line. That line is exactly the fixed space of the upper
Sylow two-subgroup. Thus singularity is characterized by fixation by some
Sylow two-subgroup, and is preserved by every compatible additive
normalizer automorphism, including field actors.

The prepared unitary-four application transports this characterization to
O₂(L) and uses ambient Thompson fusion control. It thereby separates the
singular and nonsingular involutions without assuming a realization of
the whole full-normalizer amalgam.

Source: Aschbacher–Smith F.4.35, printed p.292 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularity
variable (m : ℕ) [NeZero m]

private def swap : SpecialLinearGroup (Fin 2) (Field m) :=
  ⟨!![0,1;1,0], by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩

private theorem swap_apply (X : Space m) :
    (action m (swap m) X).val = !![X.val 1 1, X.val 1 0; X.val 0 1, X.val 0 0] := by
  rw [action_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

private theorem lower_apply (u : Field m) (X : Space m) :
    (action m (transvection (show (1:Fin 2) ≠ 0 by decide) u) X).val =
      !![X.val 0 0, X.val 0 0 * conjugation m u + X.val 0 1;
        u * X.val 0 0 + X.val 1 0,
        (u * X.val 0 0 + X.val 1 0) * conjugation m u +
          u * X.val 0 1 + X.val 1 1] := by
  rw [action_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transvection_coe,adjoint,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring

/-- A singular Hermitian matrix is SL₂-conjugate to the upper root line. -/
theorem singular_to_root (X : Space m) (hX : form m X = 0) :
    ∃ (g : SpecialLinearGroup (Fin 2) (Field m)) (a : fixedField m),
      action m g X = rootVector m a := by
  have hd : X.val 0 0 * X.val 1 1 = X.val 0 1 * X.val 1 0 := by
    have he := congrArg Subtype.val hX
    change X.val.det = 0 at he
    simpa only [Matrix.det_fin_two,sub_eq_zero] using he
  by_cases ha : X.val 0 0 = 0
  · have hz : X.val 0 1 = 0 := by
      have he : X.val 0 1 * conjugation m (X.val 0 1) = 0 := by
        rw [entry_conjugate]
        simpa [ha] using hd.symm
      exact (mul_eq_zero.mp he).elim id (fun h => (map_eq_zero (conjugation m)).mp h)
    refine ⟨swap m,⟨X.val 1 1,entry_fixed m X 1⟩,?_⟩
    apply Subtype.ext
    rw [swap_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootVector,coordinates_symm_val,ha,hz,←entry_conjugate m X 1 0]
  · let u := X.val 1 0 / X.val 0 0
    have hu : u * X.val 0 0 = X.val 1 0 := div_mul_cancel₀ _ ha
    have huc : conjugation m u = X.val 0 1 / X.val 0 0 := by
      simp only [u,map_div₀,entry_conjugate]
    have htop : X.val 0 0 * conjugation m u + X.val 0 1 = 0 := by
      rw [huc,mul_div_cancel₀ _ ha,CharTwo.add_self_eq_zero]
    have hbot : u * X.val 0 1 = X.val 1 1 := by
      apply (mul_right_cancel₀ ha)
      dsimp only [u]
      calc
        X.val 1 0 / X.val 0 0 * X.val 0 1 * X.val 0 0 =
            X.val 0 1 * (X.val 1 0 / X.val 0 0 * X.val 0 0) := by ring
        _ = X.val 0 1 * X.val 1 0 := by rw [div_mul_cancel₀ _ ha]
        _ = X.val 1 1 * X.val 0 0 := by rw [←hd,mul_comm]
    refine ⟨transvection (show (1:Fin 2) ≠ 0 by decide) u,
      ⟨X.val 0 0,entry_fixed m X 0⟩,?_⟩
    apply Subtype.ext
    rw [lower_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootVector,coordinates_symm_val,htop,hu,hbot,CharTwo.add_self_eq_zero]

private theorem upper_fixed_singular (X : Space m)
    (hX : ∀ u ∈ upperUnipotent (Field m), action m u X = X) : form m X = 0 := by
  let w : Representation.invariants
      ((action m).comp (upperUnipotent (Field m)).subtype) := ⟨X,fun u => hX u u.property⟩
  have he := congrArg Subtype.val ((upperFixedEquivK m).symm_apply_apply w)
  have hx : X = rootVector m (upperFixedEquivK m w) := he.symm
  rw [hx,rootVector,form_coordinates]
  simp

/-- A Hermitian vector fixed by an entire inner Sylow subgroup is singular. -/
theorem fixed_sylow_singular (P : Sylow 2 (SpecialLinearGroup (Fin 2) (Field m)))
    (X : Space m) (hX : ∀ u ∈ (P : Subgroup _), action m u X = X) : form m X = 0 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) (Field m))
    (upperUnipotentSylow (Field m) 2) P
  have hPe : (P : Subgroup _) = (upperUnipotent (Field m)).map (MulAut.conj g).toMonoidHom := by
    rw [←hg]; rfl
  have hh := upper_fixed_singular m (action m g⁻¹ X) (by
    intro u hu
    have hp := hX (g*u*g⁻¹) (hPe ▸ ⟨u,hu,rfl⟩)
    calc
      action m u (action m g⁻¹ X) = action m g⁻¹ (action m (g*u*g⁻¹) X) := by
        simp only [map_mul,Module.End.mul_apply,Representation.inv_self_apply]
      _ = action m g⁻¹ X := by rw [hp])
  rwa [form_preserved] at hh

/-- Singularity is intrinsically detected by the inner Sylow fixed spaces. -/
theorem singular_iff_fixed_sylow (X : Space m) :
    form m X = 0 ↔ ∃ P : Sylow 2 (SpecialLinearGroup (Fin 2) (Field m)),
      ∀ u ∈ (P : Subgroup _), action m u X = X := by
  constructor
  · intro hX
    obtain ⟨g,a,hg⟩ := singular_to_root m X hX
    refine ⟨g⁻¹ • upperUnipotentSylow (Field m) 2,?_⟩
    intro u hu
    change u ∈ (upperUnipotent (Field m)).map (MulAut.conj g⁻¹).toMonoidHom at hu
    obtain ⟨v,hv,rfl⟩ := hu
    have hroot : action m v (rootVector m a) = rootVector m a :=
      ((upperFixedEquivK m).symm a).property ⟨v,hv⟩
    change action m (g⁻¹*v*(g⁻¹)⁻¹) X = X
    rw [inv_inv,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hg,hroot,←hg]
    exact Representation.inv_self_apply _ _ _
  · rintro ⟨P,hP⟩
    exact fixed_sylow_singular m P X hP

/-- Compatible additive automorphisms preserve the singular locus. -/
theorem intertwiner_singular_iff
    (a : MulAut (SpecialLinearGroup (Fin 2) (Field m))) (t : Space m ≃+ Space m)
    (ht : ∀ g X, t (action m g X) = action m (a g) (t X)) (X : Space m) :
    form m (t X) = 0 ↔ form m X = 0 := by
  have forward (a : MulAut (SpecialLinearGroup (Fin 2) (Field m)))
      (t : Space m ≃+ Space m)
      (ht : ∀ g X, t (action m g X) = action m (a g) (t X))
      (X : Space m) (hX : form m X = 0) : form m (t X) = 0 := by
    obtain ⟨P,hP⟩ := (singular_iff_fixed_sylow m X).mp hX
    apply fixed_sylow_singular m (P.mapSurjective (f := a.toMonoidHom) a.surjective) (t X)
    rintro _ ⟨g,hg,rfl⟩
    exact (ht g X).symm.trans (congrArg t (hP g hg))
  constructor
  · intro hX
    have hinv (g) (Y) : t.symm (action m g Y) = action m (a.symm g) (t.symm Y) := by
      apply t.injective
      rw [t.apply_symm_apply,ht,a.apply_symm_apply,t.apply_symm_apply]
    simpa using forward a.symm t.symm hinv (t X) hX
  · exact forward a t ht X

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularity
