module
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Basic
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# Point quotients of marked binary sections

Quotient the original section coordinates by the marked point, then transport
the quotient to supplied linear coordinates. The resulting section has the
literal point preimage as denominator and retains ambient conjugation. The
point-stabilizer action is the same action on the linear quotient.

Source application: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(3), printed p.964, the natural K₂-module U_H/V₂.
-/

public noncomputable section
open Subgroup Representation
open BinaryLinear.SmallParabolicLevi
open Theory.LinearAlgebra BinaryFivePointStabilizer
namespace Representation.BinaryConjugationSection
variable {G W Y : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- Quotient the given coordinates by the point, retaining the actual kernel and action. -/
@[expose] def pointQuotientSection
    (d : BinaryConjugationSection H U Z ρ)
    (P B : Subgroup G) (hPH : P ≤ H) (hUP : U ≤ P) (hBU : B ≤ U) (hZB : Z ≤ B)
    (v : W) (hpoint : d.imageSpace B = line v)
    (α : P →* stabilizer v) (e : QuotientSpace v ≃ₗ[ZMod 2] Y)
    (hact : ∀ a w, ρ (inclusion hPH a) w = (α a).val w) :
    BinaryConjugationSection P U B
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
        ((linearGroupCongr e).toMonoidHom.comp ((BinaryFivePointStabilizer.quotientAction v).comp α))) where
  section_le := hUP
  kernel_le := hBU
  normalized := hPH.trans d.normalized
  coordinates := e.toAddEquiv.toMultiplicative.toMonoidHom.comp
    ((line v).mkQ.toAddMonoidHom.toMultiplicative.comp d.coordinates)
  onto := e.surjective.comp ((line v).mkQ_surjective.comp d.onto)
  kernel_eq := by
    ext u
    change e ((line v).mkQ (d.coordinates u).toAdd) = 0 ↔ (u:G) ∈ B
    rw [e.map_eq_zero_iff,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,←hpoint]
    exact d.coordinates_mem_imageSpace_iff_of_kernel_le B hZB u
  equivariant := by
    intro a u
    dsimp only [MonoidHom.comp_apply, LinearEquiv.automorphismGroup.toLinearMapMonoidHom]
    change e ((line v).mkQ (d.coordinates
      ⟨(a:G)*(u:G)*(a:G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized (hPH a.property)) u).mp u.property⟩).toAdd) =
      linearGroupCongr e (BinaryFivePointStabilizer.quotientAction v (α a)) (e ((line v).mkQ (d.coordinates u).toAdd))
    rw [linearGroupCongr_apply,e.symm_apply_apply,BinaryFivePointStabilizer.quotientAction_mk]
    exact congrArg (fun w => e ((line v).mkQ w))
      ((d.equivariant (inclusion hPH a) u).trans (hact _ _))

end Representation.BinaryConjugationSection
