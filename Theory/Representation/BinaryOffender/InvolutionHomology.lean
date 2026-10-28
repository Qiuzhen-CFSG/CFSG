module

public import Theory.Representation.BinaryOffender.FlagCodimension
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Fixed spaces through an involution's image and homology

For a binary involution t and a subgroup K of its centralizer, both
[V,t] and C_V(t) are K-invariant, and [V,t] lies in C_V(t).
The quotient C_V(t)/[V,t] is the actual homology of the square-zero
operator t-1. The submodule--quotient inequality bounds simultaneous
fixed vectors without splitting either extension. If t belongs to A,
any subgroup of K mapping into A may supply the two additional costs.

Application: the 6,8,6 filtration in Guralnick--Malle, Classification
of 2F-modules I, Proposition 5.1, HS paragraph, preprint pp.16--17.
This module proves only the general linear algebra, not that filtration.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.InvolutionHomology
noncomputable section
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (t : G)
  (K : Subgroup G) (hK : K ≤ centralizer {t})

/-- The literal fixed space, with its restricted centralizer action. -/
def fixed : Subrepresentation (ρ.comp K.subtype) where
  toSubmodule := fixedSpace ρ (zpowers t)
  apply_mem_toSubmodule c v hv := by
    rw [mem_fixedSpace_zpowers_iff] at hv ⊢
    change ρ t (ρ c v) = ρ c v
    rw [← Module.End.mul_apply, ← map_mul,
      ← mem_centralizer_singleton_iff.mp (hK c.property), map_mul, Module.End.mul_apply, hv]

/-- The literal image of t-1, with its restricted centralizer action. -/
def moved : Subrepresentation (ρ.comp K.subtype) where
  toSubmodule := LinearMap.range (ρ t - LinearMap.id)
  apply_mem_toSubmodule c := by
    rintro _ ⟨v, rfl⟩
    refine ⟨ρ c v, ?_⟩
    change ρ t (ρ c v) - ρ c v = ρ c (ρ t v - v)
    rw [map_sub, ← Module.End.mul_apply, ← map_mul,
      ← mem_centralizer_singleton_iff.mp (hK c.property), map_mul, Module.End.mul_apply]

/-- In characteristic two an involution has square-zero displacement. -/
theorem moved_le_fixed (ht : t ^ 2 = 1) : moved ρ t K hK ≤ fixed ρ t K hK := by
  rintro _ ⟨v, rfl⟩
  change ρ t v - v ∈ fixedSpace ρ (zpowers t)
  rw [mem_fixedSpace_zpowers_iff, map_sub]
  have he : ρ t (ρ t v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ht, map_one]
    rfl
  have hn (w : V) : -w = w := by
    apply neg_eq_iff_add_eq_zero.mpr
    have hh := @two_smul (ZMod 2) V _ _ _ w
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at hh
    exact hh.symm
  rw [he]
  simp only [sub_eq_add_neg, hn, add_comm]

/-- The actual quotient of the fixed space by its intersection with the image.
For a square-one element this is C_V(t)/[V,t]. -/
def homology := sectionRepresentation (ρ.comp K.subtype)
  (moved ρ t K hK) (fixed ρ t K hK)

variable [FiniteDimensional (ZMod 2) V]

/-- The image dimension is the displacement on the original module. -/
theorem moved_finrank :
    Module.finrank (ZMod 2) (moved ρ t K hK).toSubmodule =
      fixedCodim ρ (zpowers t) :=
  (fixedCodim_zpowers_eq_displacement_rank ρ t).symm

/-- The image, homology and outer displacement contribute simultaneously.
The subgroup acting on the two layers may be smaller than the original actor. -/
theorem codim_bound (ht : t ^ 2 = 1) (A : Subgroup G) (htA : t ∈ A)
    (B : Subgroup K) (hBA : B.map K.subtype ≤ A) :
    fixedCodim ρ (zpowers t) + fixedCodim (homology ρ t K hK) B +
      fixedCodim (moved ρ t K hK).toRepresentation B ≤ fixedCodim ρ A := by
  have hs := fixedCodim_section_add_lower_le (ρ.comp K.subtype)
    (moved ρ t K hK) (fixed ρ t K hK) (moved_le_fixed ρ t K hK ht) B
  change fixedCodim (homology ρ t K hK) B + _ ≤ _ at hs
  have he := (subrepresentationFixedEquiv (ρ.comp K.subtype) (fixed ρ t K hK) B).finrank_eq
  have hle : fixedSpace ρ A ≤
      (fixed ρ t K hK).toSubmodule ⊓ fixedSpace (ρ.comp K.subtype) B := by
    intro v hv
    refine ⟨?_, ?_⟩
    · exact (mem_fixedSpace_zpowers_iff ρ t v).mpr (hv ⟨t, htA⟩)
    · intro b
      exact hv ⟨b, hBA (Subgroup.mem_map_of_mem K.subtype b.property)⟩
  have hm := Submodule.finrank_mono hle
  have h₁ := fixedCodim_add_finrank (fixed ρ t K hK).toRepresentation B
  have h₂ := fixedCodim_add_finrank ρ (zpowers t)
  have h₃ := fixedCodim_add_finrank ρ A
  change _ + _ = Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) at h₁
  omega

end
end Representation.BinaryOffender.InvolutionHomology
