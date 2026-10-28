module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Inputs

/-!
# The literal code quotient and its dual axis

Restriction of the coordinate pairing identifies code/V4 with the dual of
cocode V6. This equivalence intertwines the quotient action. It carries the
literal image V9/V4 to the annihilator of V1 inside V6, so it retains the axis
needed for transferring the full transvection group in H.16.3(3).

Source: Aschbacher--Smith, H.15.4(2) and H.16.3(3), pp.400,403,
combined manuscript of 1 March 2004.
-/

public section
noncomputable section
namespace MathieuCode.M22Quintet.DualAction

private def restrictPairing : M22Code →ₗ[ZMod 2] Module.Dual (ZMod 2) V6 :=
  V6.dualRestrict.comp m22CodeCocodeDuality.toLinearMap

private theorem restrictPairing_ker : restrictPairing.ker = V4 := by
  ext v
  change restrictPairing v = 0 ↔ v ∈ V4
  rw [LinearMap.ext_iff]
  change (∀ u : V6, m22CodeCocodeDuality v u.val = 0) ↔ v ∈ annihilator V6
  rw [mem_annihilator]
  exact ⟨fun h u hu => h ⟨u, hu⟩, fun h u => h u.val u.property⟩

/-- Duality on the actual quotient, induced by the coordinate pairing. -/
def quotientDuality : (M22Code ⧸ V4) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V6 :=
  (Submodule.quotEquivOfEq V4 restrictPairing.ker restrictPairing_ker.symm).trans
    (restrictPairing.quotKerEquivOfSurjective
      (Subspace.dualRestrict_surjective.comp m22CodeCocodeDuality.surjective))

@[simp] theorem quotientDuality_mk (v : M22Code) (u : V6) :
    quotientDuality (V4.mkQ v) u = m22CodeCocodeDuality v u.val := by
  rfl

/-- The equivalence retains the actual quotient representation. -/
theorem quotientDuality_equivariant (g : Q) (v : M22Code ⧸ V4) :
    quotientDuality (V4Subrepresentation.quotientRepresentation g v) =
      V6Subrepresentation.toRepresentation.dual g (quotientDuality v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    ext u
    change m22CodeCocodeDuality (m22OuterCodeRepresentation g.val v) u.val =
      m22CodeCocodeDuality v (m22OuterCocodeRepresentation g.val⁻¹ u.val)
    exact LinearMap.congr_fun (m22CodeCocodeDuality_equivariant g.val v) u.val

/-- The literal code axis becomes the annihilator of the literal cocode center. -/
theorem quotientDuality_axis (F : CocodeFlag) :
    codeAxis.map quotientDuality.toLinearMap = F.center.toSubmodule.dualAnnihilator := by
  ext f
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro u hu
    exact (mem_annihilator V1 v).mp hv u.val hu
  · intro hf
    obtain ⟨w, rfl⟩ := quotientDuality.surjective f
    induction w using Submodule.Quotient.induction_on with
    | _ v =>
      refine ⟨V4.mkQ v, ⟨v, ?_, rfl⟩, rfl⟩
      apply (mem_annihilator V1 v).mpr
      intro u hu
      exact (Submodule.mem_dualAnnihilator _).mp hf
        ⟨u, F.one_le_six hu⟩ hu

end MathieuCode.M22Quintet.DualAction
