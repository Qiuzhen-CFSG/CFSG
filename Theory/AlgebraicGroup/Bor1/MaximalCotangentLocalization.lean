module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.AtPrime.Basic

namespace Theory.AlgebraicGroup.Bor1

open IsLocalRing

universe u

variable (R : Type u) [CommRing R]
variable (p : Ideal R) [p.IsMaximal]
variable (Rₚ : Type u) [CommRing Rₚ] [Algebra R Rₚ]
variable [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]

/-- Localizing at a maximal ideal preserves the dimension of its cotangent
space, after identifying the two residue fields. -/
public theorem maximalCotangent_finrank_eq_localization :
    Module.finrank (R ⧸ p) p.Cotangent =
      Module.finrank (ResidueField Rₚ) (CotangentSpace Rₚ) := by
  change Module.finrank (R ⧸ p) p.Cotangent =
    Module.finrank (Rₚ ⧸ maximalIdeal Rₚ) (maximalIdeal Rₚ).Cotangent
  have hcomp : p ≤ (maximalIdeal Rₚ).comap (Algebra.ofId R Rₚ) := by
    change p ≤ (maximalIdeal Rₚ).comap (algebraMap R Rₚ)
    rw [← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal Rₚ p]
  let f := Ideal.mapCotangent p (maximalIdeal Rₚ) (Algebra.ofId R Rₚ) hcomp
  have hf_inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨x, rfl⟩ := p.toCotangent_surjective z
    change Ideal.mapCotangent p (maximalIdeal Rₚ) (Algebra.ofId R Rₚ) hcomp
      (p.toCotangent x) = 0 at hz
    rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq_zero] at hz
    rw [Ideal.toCotangent_eq_zero]
    rw [← IsLocalization.AtPrime.under_maximalIdeal_pow p Rₚ 2,
      Ideal.mem_under]
    exact hz
  have hf_surj : Function.Surjective f := by
    intro z
    obtain ⟨y, rfl⟩ := (maximalIdeal Rₚ).toCotangent_surjective z
    let E := IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ 2
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := p ^ 2)
      (E.symm ((maximalIdeal Rₚ ^ 2).mkQ y))
    have hE : Ideal.Quotient.mk (maximalIdeal Rₚ ^ 2) (algebraMap R Rₚ a) =
        Ideal.Quotient.mk (maximalIdeal Rₚ ^ 2) (y : Rₚ) := by
      have := congrArg E ha
      simpa [E] using this
    have hd : algebraMap R Rₚ a - y ∈ maximalIdeal Rₚ ^ 2 :=
      (Ideal.Quotient.eq (I := maximalIdeal Rₚ ^ 2)).mp hE
    have haMax : algebraMap R Rₚ a ∈ maximalIdeal Rₚ := by
      rw [show algebraMap R Rₚ a =
        (algebraMap R Rₚ a - y) + y by abel]
      exact (maximalIdeal Rₚ).add_mem
        (Ideal.pow_le_self two_ne_zero hd) y.2
    have hap : a ∈ p := by
      rw [← IsLocalization.AtPrime.under_maximalIdeal Rₚ p,
        Ideal.mem_under]
      exact haMax
    refine ⟨p.toCotangent ⟨a, hap⟩, ?_⟩
    change Ideal.mapCotangent p (maximalIdeal Rₚ) (Algebra.ofId R Rₚ) hcomp
      (p.toCotangent ⟨a, hap⟩) = (maximalIdeal Rₚ).toCotangent y
    rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq]
    exact hd
  let e := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  let eResidue := IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ
  have hrank := rank_eq_of_equiv_equiv eResidue e.toAddEquiv eResidue.bijective (by
    intro r z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    change f (a • z) = algebraMap R Rₚ a • f z
    rw [IsScalarTower.algebraMap_smul Rₚ a (f z)]
    exact f.map_smul a z)
  simpa only [Module.finrank] using congrArg Cardinal.toNat hrank

end Theory.AlgebraicGroup.Bor1
