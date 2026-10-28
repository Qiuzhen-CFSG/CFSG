module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.Janko1.Model.Certification.InvolutionFusion
-- Internal proof extension: reuse the checked eight-element subgroup and its
-- inverse identities, preserving the original certificate's public boundary.
import all Theory.SpecificGroups.Janko1.Model.Certification.InvolutionFusion

/-!
# Abelian two-subgroups of the explicit J₁ model

The eight-element subgroup in the involution-fusion certificate has exponent
two, hence is abelian. Its odd index makes it Sylow, and Sylow conjugacy
transports commutativity to every two-subgroup of the actual matrix model.
No new matrix table or group-order certificate is needed.

This is the local J₁ fact used in Aschbacher–Smith, proof of Lemma 1.3.9,
printed p.514, for the A₅ inclusion in Proposition A.3.12(15), printed p.47.
The concrete generators and certificates have their ATLAS attribution in
`Model.Basic` and `Model.Certification.InvolutionFusion`.
-/

namespace Janko1
open Subgroup

private theorem eight_comm : IsMulCommutative InvolutionFusion.eight := by
  have hinv (x : InvolutionFusion.eight) : x⁻¹ = x := by
    apply Subtype.ext
    obtain ⟨i, hi⟩ := x.property
    change (x : Model)⁻¹ = x
    rw [← hi, InvolutionFusion.e_inv]
  exact ⟨⟨fun x y => by rw [← hinv (x*y), mul_inv_rev, hinv x, hinv y]⟩⟩

private theorem sylow_comm (Q : Sylow 2 Model) : IsMulCommutative Q := by
  have hindex : InvolutionFusion.eight.index = 21945 := by
    have h := InvolutionFusion.eight.card_mul_index
    rw [InvolutionFusion.card_eight, card_model] at h
    omega
  let P : Sylow 2 Model := (IsPGroup.of_card
    (p := 2) (n := 3) InvolutionFusion.card_eight).toSylow (by
      rw [hindex]
      decide)
  let e := Q.equiv P
  let : IsMulCommutative P := eight_comm
  exact ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm'])⟩⟩

/-- Every two-subgroup of the actual J₁ matrix model is abelian. -/
public theorem two_subgroup_isMulCommutative (R : Subgroup Model) (hR : IsPGroup 2 R) :
    IsMulCommutative R := by
  obtain ⟨Q, hQ⟩ := hR.exists_le_sylow
  let : IsMulCommutative Q := sylow_comm Q
  exact ⟨⟨fun x y => (Subgroup.inclusion_injective hQ)
    (by simp only [map_mul, mul_comm'])⟩⟩

end Janko1
