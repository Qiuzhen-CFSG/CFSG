module
public import Theory.Representation.SU3.ProjectiveBinaryDegree.DegreeGap
public import Theory.Representation.SU3.BinaryDegree.Perfectness
public import Theory.SpecificGroups.PSU3.UniversalCover.Kernel
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section

/-!
# The binary projective SU₃ degree bound in odd field degree

The characteristic-two tensor catalogue and its twisted Frobenius periods give
Fong--Seitz I (4D): every nontrivial irreducible SU₃ action below degree 8b
has degree 6b and is faithful. For odd b the literal SU₃-to-PSU₃ projection
has a cubic kernel, excluding this alternative for projective actions.
A nontrivial action of the perfect projective group survives on an actual
irreducible subquotient, so the same lower bound holds without irreducibility.

All representations use the original Hermitian form and the literal projective
matrix image. The hypothesis b ≥ 2 is essential here; the source's solvable
b = 1 section is handled separately by the octagon consumer.

Source: Fong--Seitz, Groups with a (B,N)-Pair of Rank 2, I (1973),
(4D), printed pp.21--23, applied in (6F), printed p.47.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups Representation
namespace Representation.SU3.ProjectiveBinaryDegree

/-- Odd field degree gives the actual scalar kernel order three. -/
theorem card_projection_kernel
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hodd : Odd b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b)) : Nat.card J.specialToProjective.ker=3 := by
  rw [HermitianForm.UniversalCover.card_kernel J hcard hconj, Nat.gcd_comm]
  apply Nat.gcd_eq_right_iff_dvd.mpr
  apply Nat.dvd_of_mod_eq_zero
  have hp := Nat.BinaryTorusParity.two_pow_mod_three b
  rw [if_neg (by have := Nat.odd_iff.mp hodd; omega)] at hp
  omega

/-- A nontrivial irreducible binary representation of PSU₃(2ᵇ), with odd
b ≥ 2, cannot be a natural SU₃ representation and has degree at least 8b. -/
theorem finrank_ge_of_irreducible
    {F V : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {b : ℕ} (hb : 2 ≤ b) (hodd : Odd b)
    (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    [IsIrreducible ρ] (hne : ∃ g,ρ g≠1) :
    8*b ≤ Module.finrank (ZMod 2) V := by
  by_contra! hd
  let σ := ρ.comp J.specialToProjective
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    J.specialToProjective J.specialToProjective_surjective ρ).mpr inferInstance
  have hnσ : ∃ g,σ g≠1 := by
    obtain ⟨g,hg⟩ := hne
    obtain ⟨x,rfl⟩ := J.specialToProjective_surjective g
    exact ⟨x,hg⟩
  have hi := (eq_minimum_and_injective_of_irreducible_finrank_lt
    J hb hcard hconj σ hnσ hd).2
  have hπ : Function.Injective J.specialToProjective := fun x y he => hi (congrArg ρ he)
  have hc : Nat.card J.specialToProjective.ker=1 :=
    (eq_bot_iff_card _).mp (J.specialToProjective.ker_eq_bot_iff.mpr hπ)
  have := card_projection_kernel J hodd hcard hconj
  omega

/-- Every nontrivial binary projective action in odd degree has a nontrivial
irreducible section; its degree bounds that of the entire original action. -/
theorem finrank_ge_of_nontrivial
    {F V : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {b : ℕ} (hb : 2 ≤ b) (hodd : Odd b)
    (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hne : ∃ g,ρ g≠1) : 8*b ≤ Module.finrank (ZMod 2) V := by
  let H := ProjectiveSpecialUnitaryMatrixGroup J
  let : Group.IsPerfect H := BinaryDegree.isPerfect_projective J hb hcard hconj
  let : Group.IsPerfect (⊤ : Subgroup H) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := H)).symm.toMonoidHom) topEquiv.symm.surjective
  have hker : ¬ (⊤ : Subgroup H) ≤ ρ.ker := by
    intro h
    obtain ⟨g,hg⟩ := hne
    exact hg (h (mem_top g))
  obtain ⟨U,N,hi,hN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) (⊤ : Subgroup H) hker
  let := hi
  have hnt : ∃ g,N.quotientRepresentation g≠1 := by
    by_contra! he
    exact hN (fun g _ => he g)
  exact (finrank_ge_of_irreducible J hb hodd hcard hconj N.quotientRepresentation hnt).trans
    ((Submodule.finrank_quotient_le _).trans (Submodule.finrank_le U.toSubmodule))

/-- The sharp binary bound needed for a faithful action of the actual projective
unitary group. No tensor model or classification premise is required. -/
theorem finrank_ge
    {F V : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {b : ℕ} (hb : 2 ≤ b) (hodd : Odd b)
    (hcard : Nat.card F=(2^b)^2) (hconj : ∀ x,J.conj x=x^(2^b))
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hρ : Function.Injective ρ) : 8*b ≤ Module.finrank (ZMod 2) V := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b
    (by omega) hcard hconj
  have hq : 2 < 2^b := (by decide : 2 < 2^2).trans_le
    (Nat.pow_le_pow_right (by decide) hb)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J (2^b) hq hcard hf
  obtain ⟨g,hg⟩ := exists_ne (1 : ProjectiveSpecialUnitaryMatrixGroup J)
  exact finrank_ge_of_nontrivial J hb hodd hcard hconj ρ
    ⟨g, fun he => hg (hρ (he.trans ρ.map_one.symm))⟩

end Representation.SU3.ProjectiveBinaryDegree
