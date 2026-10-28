module
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage

/-!
# Lifting an invariant complement through a binary group section

An invariant complement to the image of V in Q/Z pulls back to a subgroup
W of the original Q. The pullback satisfies W∩V=Z and W∨V=Q, and its
coordinates agree with the original quotient coordinates after the supplied
natural-factor identification. Normalization is retained for the same actor.

This is the subgroup construction after DGS, *Groups and Graphs* (1985),
9.10(6), printed p.150. The invariant complement is an input here; the
representation-theoretic splitting must construct it independently.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G J Y N : Type*} [Group G] [Group J]
  [AddCommGroup Y] [Module (ZMod 2) Y] [AddCommGroup N] [Module (ZMod 2) N]

/-- Lift a complement of the specified image to the original group section. -/
theorem exists_complementary_section
    (H Q V Z : Subgroup G) (hVQ : V ≤ Q) (hZV : Z ≤ V)
    (π : H →* J) (ρ : Representation (ZMod 2) J Y)
    (σ : Representation (ZMod 2) J N)
    (c : BinaryConjugationSection H Q Z (ρ.comp π))
    (X K : Subrepresentation ρ) (hX : X.toSubmodule = c.imageSpace V)
    (hK : IsCompl X.toSubmodule K.toSubmodule)
    (eK : K.toSubmodule ≃ₗ[ZMod 2] N)
    (heK : ∀ g k, eK (K.toRepresentation g k) = σ g (eK k)) :
    ∃ (W : Subgroup G) (hWQ : W ≤ Q),
      W ⊓ V = Z ∧ W ⊔ V = Q ∧
      ∃ cW : BinaryConjugationSection H W Z (σ.comp π),
        ∀ w : W, (eK.symm (cW.coordinates w).toAdd : Y) =
          (c.coordinates (inclusion hWQ w)).toAdd := by
  let XH : Subrepresentation (ρ.comp π) := {
    toSubmodule := X.toSubmodule
    apply_mem_toSubmodule h := X.apply_mem_toSubmodule (π h) }
  let KH : Subrepresentation (ρ.comp π) := {
    toSubmodule := K.toSubmodule
    apply_mem_toSubmodule h := K.apply_mem_toSubmodule (π h) }
  have hXV : c.invariantPreimage XH = V := by
    ext v
    rw [c.mem_invariantPreimage]
    constructor
    · rintro ⟨hv,hx⟩
      change (c.coordinates ⟨v,hv⟩).toAdd ∈ X.toSubmodule at hx
      rw [hX,c.coordinates_mem_imageSpace_iff V hVQ, sup_eq_left.mpr hZV] at hx
      exact hx
    · intro hv
      refine ⟨hVQ hv,?_⟩
      change (c.coordinates ⟨v,hVQ hv⟩).toAdd ∈ X.toSubmodule
      rw [hX]
      exact (c.mem_imageSpace_iff V _).mpr ⟨⟨v,hVQ hv⟩,hv,rfl⟩
  let W := c.invariantPreimage KH
  let d := c.invariantSection KH
  let cW : BinaryConjugationSection H W Z (σ.comp π) := {
    section_le := d.section_le
    kernel_le := d.kernel_le
    normalized := d.normalized
    coordinates := eK.toAddEquiv.toMultiplicative.toMonoidHom.comp d.coordinates
    onto := eK.toAddEquiv.toMultiplicative.surjective.comp d.onto
    kernel_eq := by
      ext w
      change eK (d.coordinates w).toAdd = 0 ↔ (w:G) ∈ Z
      rw [eK.map_eq_zero_iff]
      exact d.coordinates_eq_one_iff w
    equivariant h w := by
      change eK (d.coordinates _).toAdd = σ (π h) (eK (d.coordinates w).toAdd)
      rw [d.equivariant]
      exact heK _ _ }
  refine ⟨W,c.invariantPreimage_le KH,?_,?_,cW,?_⟩
  · rw [←hXV]
    exact c.invariantPreimage_inf KH XH hK.symm.disjoint
  · rw [←hXV]
    exact c.invariantPreimage_sup KH XH hK.symm.sup_eq_top
  · intro w
    change (eK.symm (eK (d.coordinates w).toAdd) : Y) = _
    rw [eK.symm_apply_apply]
    rfl
end Representation.BinaryConjugationSection
