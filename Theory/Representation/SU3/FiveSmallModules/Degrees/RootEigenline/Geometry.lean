module
public import Theory.Representation.SU3.FiveSmallModules.Degrees.Inputs
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# Canonical Borel geometry for rational SU₃(5) lines

The explicit Hermitian torus action normalizes the literal SU root image.
Its projective torus has order eight over the field of order 25, so eighth
powers lie in the central kernel of SU → PSU. These statements retain the
original field involution and the actual subgroup embeddings.

Source: Huppert II.10.12; the root-group route to Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, p.10.
-/

public section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.OddPrimeSylow.NormalizedOuter
open HermitianForm.BorelTorus
namespace Representation.SU3.FiveSmallModules.Degrees.RootEigenline

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The canonical torus normalizes the canonical root subgroup already in SU₃. -/
theorem specialTorus_normalizes_root
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    specialTorus J hJ ≤ Subgroup.normalizer (specialRoot J hJ : Set J.specialSubgroup) := by
  rintro t ⟨k, rfl⟩
  apply Subgroup.mem_normalizer_fintype
  rintro p ⟨z, rfl⟩
  refine ⟨hermitianTorusAction J k z, ?_⟩
  apply (eq_mul_inv_iff_mul_eq).mpr
  exact (Subtype.ext (hermitianTorusGL_mul_unipotent J k z)).symm

/-- The torus has projective order eight, so its eighth powers are central
in the literal special-unitary group. -/
theorem specialTorus_eighth_power_central
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    (t : J.specialSubgroup) (ht : t ∈ specialTorus J hJ) :
    t ^ 8 ∈ Subgroup.center J.specialSubgroup := by
  obtain ⟨k, rfl⟩ := ht
  have hcard : Nat.card (projectiveTorus J hJ) = 8 := by
    rw [projective_card J hJ hc hconj]
    norm_num
  let s : projectiveTorus J hJ := ⟨hermitianTorusPSU J hJ k, ⟨k, rfl⟩⟩
  have hs : s ^ 8 = 1 := by simpa only [hcard] using (pow_card_eq_one' (x := s))
  apply J.specialToProjective_ker_le_center
  rw [MonoidHom.mem_ker, map_pow]
  have he : J.specialToProjective (hermitianTorusSU J hJ k) =
      hermitianTorusPSU J hJ k := by
    apply Subtype.ext
    rw [J.specialToProjective_apply_val, hermitianTorusPSU_val]
    rfl
  rw [he]
  exact congrArg Subtype.val hs

end Representation.SU3.FiveSmallModules.Degrees.RootEigenline
