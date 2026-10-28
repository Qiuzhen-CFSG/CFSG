module

public import Theory.Representation.OrthogonalFourPlusMatrix.SylowFixedDimension
public import Theory.Representation.SubspaceQuotient
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Excluding the tensor alternative on the source quotient

The original homomorphism H → H/O₂(H) marks K₀* as SL₂(4) × SL₂(4).
The supplied linear equivalence intertwines its matrix action with the
literal action on U_H/V₁. A Sylow subgroup of K₀ whose image is contained in R₁* therefore
fixes at most a binary 2-space. The original commutator containment
[V₅,R₁] ≤ V₁ makes the image of V₅ fixed, contradicting its binary dimension
at least four. The action is required to factor through the original
H/O₂(H); thus only containment of Sylow images is needed. The conjugation
convention and the original quotient map
are retained throughout.

This excludes case (b) in the proof of 12.6.33 once the source module
identification has been constructed; it does not construct that identification.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed p.838.
-/

@[expose] public section
open Module Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06.LocalAlternatives
namespace Tensor
open ClassicalOrthogonal.FourPlusMatrix
variable {H : Type*} [Group H] [Finite H]

/-- The tensor alternative in 12.6.33 is impossible on the literal U/V₁
quotient when R₁* contains the image of a component Sylow subgroup and fixes
an E₁₆ there. Both the group marking and the equivariant linear marking are
explicit. No abstract group-family label is used as a representation. -/
theorem impossible_on_source_quotient
    (U : Subgroup H) [IsElementaryAbelian 2 U]
    (ρ : Representation (ZMod 2) H (Additive U))
    (hρ : ∀ (h : H) (u : Additive U),
      ((ρ h u).toMul : H) = h * (u.toMul : H) * h⁻¹)
    (Z : Subrepresentation ρ)
    (ρstar : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive U ⧸ Z.toSubmodule))
    (hstar : ∀ (h : H) (u : Additive U ⧸ Z.toSubmodule),
      ρstar (QuotientGroup.mk' (pCore 2 H) h) u = Z.quotientRepresentation h u)
    (V₁ V₅ : Subgroup U)
    (hZ : Z.toSubmodule = AddSubgroup.toZModSubmodule 2 V₁.toAddSubgroup)
    (K₀ R₁ : Subgroup H)
    (eK : K₀.map (QuotientGroup.mk' (pCore 2 H)) ≃* Binary.G)
    (eU : (Additive U ⧸ Z.toSubmodule) ≃ₗ[ZMod 2] Binary.V)
    (he : ∀ (k : K₀) (u : Additive U ⧸ Z.toSubmodule),
      eU (Z.quotientRepresentation k.val u) =
        Binary.action (eK ((QuotientGroup.mk' (pCore 2 H)).subgroupMap K₀ k)) (eU u))
    (S : Sylow 2 K₀)
    (hS : ((S : Subgroup K₀).map K₀.subtype).map (QuotientGroup.mk' (pCore 2 H)) ≤
      R₁.map (QuotientGroup.mk' (pCore 2 H)))
    (hcomm : ⁅V₅.map U.subtype, R₁⁆ ≤ V₁.map U.subtype)
    (hdim : 4 ≤ finrank (ZMod 2)
      ((AddSubgroup.toZModSubmodule 2 V₅.toAddSubgroup).map Z.toSubmodule.mkQ)) : False := by
  let κ := eK.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 H)).subgroupMap K₀)
  have hκ : Function.Surjective κ :=
    eK.surjective.comp ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective K₀)
  have hbound := Binary.finrank_le_two_of_equivariant_sylow_fixed
    (Z.quotientRepresentation.comp K₀.subtype) κ hκ eU he S
    ((AddSubgroup.toZModSubmodule 2 V₅.toAddSubgroup).map Z.toSubmodule.mkQ) (by
      intro k hk v hv
      obtain ⟨u, hu, rfl⟩ := hv
      obtain ⟨r, hr, heq⟩ := hS (mem_map_of_mem (QuotientGroup.mk' (pCore 2 H))
        (mem_map_of_mem K₀.subtype hk))
      change QuotientGroup.mk' (pCore 2 H) r = QuotientGroup.mk' (pCore 2 H) k.val at heq
      change Z.quotientRepresentation k.val (Z.toSubmodule.mkQ u) = Z.toSubmodule.mkQ u
      rw [← hstar, ← heq, hstar, Subrepresentation.quotientRepresentation_mk]
      apply (Submodule.Quotient.eq Z.toSubmodule).mpr
      rw [hZ]
      change (ρ r u - u).toMul ∈ V₁
      have hc : ⁅r, (u.toMul : H)⁆ ∈ V₁.map U.subtype := by
        rw [commutator_comm] at hcomm
        exact hcomm (commutator_mem_commutator
          hr ⟨u.toMul, hu, rfl⟩)
      obtain ⟨a, ha, haeq⟩ := hc
      have ha' : a = (ρ r u - u).toMul := by
        apply Subtype.ext
        calc
          (a : H) = ⁅r, (u.toMul : H)⁆ := haeq
          _ = ((ρ r u - u).toMul : H) := by
            simp only [commutatorElement_def, toMul_sub, div_eq_mul_inv,
              Subgroup.coe_mul, Subgroup.coe_inv, hρ]
      rwa [← ha'])
  omega
end Tensor
end CFSG.Quasithin.Chapter12.Section06.LocalAlternatives
