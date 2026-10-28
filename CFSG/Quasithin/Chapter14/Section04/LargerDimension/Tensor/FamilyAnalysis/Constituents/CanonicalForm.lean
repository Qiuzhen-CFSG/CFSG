module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.EarlierGeometry
public import Theory.GroupTheory.PGroup.SmallFrattiniLinearForms
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# The canonical form in the published tensor coordinates

Extraspeciality gives Φ(U) = Z(U) of order two. The existing central
commutator construction therefore supplies a binary bilinear form on the
literal U/Z(U). Transport through the inverse of the published space
isomorphism gives the form in the tensor coordinates. Its zero test on
actual lifts is exactly commutation in U, so it supplies CanonicalForm
without an additional form hypothesis.

Source: Aschbacher–Smith, Lemma 12.8.8(2), printed pp.851–852, used in
14.4.10 on printed p.1010, combined manuscript of 1 March 2004.
-/

public section

open Subgroup TensorProduct
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.CaseFiveCoordinates
variable {G : Type*} [Group G] [Finite G]
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {H U : Subgroup G} (c : CaseFiveCoordinates hAD (V := V) H U)
  [IsExtraspecial 2 U]

/-- The extraspecial commutator form transported along the actual U/Z(U) coordinates. -/
noncomputable def canonicalForm : c.CanonicalForm := by
  have htwo : IsPGroup 2 U := IsExtraspecial.isPGroup 2 U
  have hphi : Nat.card (frattini U) = 2 := by
    rw [IsExtraspecial.frattini_eq_center (p := 2), IsExtraspecial.center_order_p 2 U]
  let : IsElementaryAbelian 2 (U ⧸ center U) := SmallFrattini.centralElementary htwo hphi
  let f : (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V) →ₗ[ZMod 2]
      Additive (U ⧸ center U) :=
    c.space.symm.toMonoidHom.toAdditiveRight.toZModLinearMap 2
  refine ⟨(SmallFrattini.centralBilinearForm htwo hphi).compl₁₂ f f, ?_⟩
  intro u v
  have hf (u : U) : f (c.quotientMap u).toAdd =
      Additive.ofMul (QuotientGroup.mk' (center U) u) := by
    change Additive.ofMul (c.space.symm (c.space (QuotientGroup.mk' (center U) u))) = _
    rw [c.space.symm_apply_apply]
  change SmallFrattini.centralBilinearForm htwo hphi
    (f (c.quotientMap u).toAdd) (f (c.quotientMap v).toAdd) = 0 ↔ _
  rw [hf, hf, SmallFrattini.centralBilinearForm_apply]
  change SmallFrattini.binaryMark hphi
    (SmallFrattini.centralCommutator htwo (QuotientGroup.mk' (center U) u)
      (QuotientGroup.mk' (center U) v)) = 1 ↔ _
  rw [(SmallFrattini.binaryMark hphi).map_eq_one_iff]
  change (⟨⁅u,v⁆, _⟩ : frattini U) = 1 ↔ Commute u v
  rw [Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.CaseFiveCoordinates
