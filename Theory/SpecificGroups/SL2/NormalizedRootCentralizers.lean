module

public import Theory.SpecificGroups.SL2.ProjectiveBorelFrobenius
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.GroupTheory.NormalizedRootCentralizers
/-!
# Uniform root centralizers in PSL₂

The full center of the standard Sylow subgroup is the additive upper root
subgroup. Conjugation by an upper triangular matrix scales its parameter
by the square of the first diagonal entry. Fixing one nonzero parameter
therefore fixes the entire center, also after the actual central quotient.
The Sylow marking agrees with the projective image of the matrix Sylow.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, with
1.1.5(3a) and A.2.3–4 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Matrix BenderSuzuki.Converse
open scoped MatrixGroups IsMulCommutative
namespace Matrix.ProjectiveSpecialLinearGroup.NormalizedRootCentralizers
open OddBorel
variable (F : Type*) [Field F]

/-- The entire embedded center, with its injective additive parametrization. -/
theorem center_kernel : (center (kernel F)).map (kernel F).subtype = kernel F := by
  rw [center_eq_top (G := kernel F), ← MonoidHom.range_eq_map, range_subtype]

/-- Every nonidentity root element has the same centralizer in the actual Borel. -/
theorem uniform (r : PSL(2,F)) (hr : r ∈ (center (kernel F)).map (kernel F).subtype)
    (hne : r ≠ 1) :
    PBorel F ⊓ centralizer ({r} : Set PSL(2,F)) =
      PBorel F ⊓ centralizer (((center (kernel F)).map (kernel F).subtype : Subgroup PSL(2,F)) : Set PSL(2,F)) := by
  rw [center_kernel] at hr ⊢
  obtain ⟨t, rfl⟩ := hr
  have ht : t.toAdd ≠ 0 := fun he => hne (by rw [show t = 1 from he, map_one])
  apply le_antisymm
  · rintro g ⟨hg, hc⟩
    rw [PBorel_eq_map] at hg
    obtain ⟨A, hA, rfl⟩ := hg
    have hscale (b : Multiplicative F) :
        pi F A * unipotentHom F b * (pi F A)⁻¹ =
          unipotentHom F (.ofAdd (A.val 0 0 ^ 2 * b.toAdd)) := by
      change pi F A * pi F (uni b.toAdd) * (pi F A)⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, Borel_conj_uni hA]
      rfl
    have he' : unipotentHom F (.ofAdd (A.val 0 0 ^ 2 * t.toAdd)) =
        unipotentHom F t := by
      rw [← hscale t, mem_centralizer_singleton_iff.mp hc, mul_assoc,
        mul_inv_cancel, mul_one]
    have he : A.val 0 0 ^ 2 * t.toAdd = 1 * t.toAdd := by
      simpa only [one_mul, toAdd_ofAdd] using congrArg Multiplicative.toAdd (unipotentHom_injective F he')
    have hs : A.val 0 0 ^ 2 = 1 := mul_right_cancel₀ ht he
    refine ⟨?_, mem_centralizer_iff.mpr ?_⟩
    · rw [PBorel_eq_map]
      exact mem_map_of_mem _ hA
    · rintro _ ⟨b, rfl⟩
      have hh := hscale b
      rw [hs, one_mul] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ⟨t, rfl⟩))

variable [Finite F] [CharP F 2]
@[expose] noncomputable def rootSylow : Sylow 2 PSL(2,F) :=
  (SpecialLinearGroup.upperUnipotentSylow F 2).mapSurjective (pi_surjective (F := F))

/-- The coordinate subgroup is the actual projective Sylow subgroup. -/
theorem rootSylow_coe : (rootSylow F : Subgroup PSL(2,F)) = kernel F := by
  change (SpecialLinearGroup.upperUnipotent F).map (pi F) = _
  rw [SpecialLinearGroup.upperUnipotent, ← MonoidHom.range_comp]
  apply congrArg MonoidHom.range
  apply MonoidHom.ext
  intro t
  change pi F (SpecialLinearGroup.upperUnipotentHom F t) = pi F (uniHom F t)
  apply congrArg (pi F)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.upperUnipotentHom, SpecialLinearGroup.transvection_coe,
      uniHom, uni] <;> rfl
end Matrix.ProjectiveSpecialLinearGroup.NormalizedRootCentralizers
