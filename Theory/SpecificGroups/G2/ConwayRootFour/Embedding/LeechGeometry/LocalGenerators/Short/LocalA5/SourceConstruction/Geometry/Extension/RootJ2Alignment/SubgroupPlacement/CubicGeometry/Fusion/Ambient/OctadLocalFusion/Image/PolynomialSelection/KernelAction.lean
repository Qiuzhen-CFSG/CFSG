module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SourceClass
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The literal action on the octad kernel's central quotient

Conjugation in the integral octad centralizer restricts to its actual restriction
kernel. We pass this action to the quotient by the kernel's center and name its
fixed subgroup. Under the extraspecial and order hypotheses from the independent
kernel construction, the quotient has order 256.

These are the shared action and counting conventions for polynomial class
selection. In particular, fixed points here are cosets of the integral kernel,
not elements of an unrelated orthogonal group.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.2 and §46, p.251.
-/

@[expose] public noncomputable section

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.PolynomialSelection

def kernelSign : action.ker := ⟨complementSign, complementSign_mem_kernel⟩

theorem kernelSign_ne_one : kernelSign ≠ 1 :=
  fun h => complementSign_ne_one (congrArg Subtype.val h)

theorem kernelSign_mem_center : kernelSign ∈ Subgroup.center action.ker := by
  apply Subgroup.mem_center_iff.mpr
  intro q
  exact Subtype.ext (Subgroup.mem_center_iff.mp complementSign_mem_center q.val)

theorem kernel_center_cases (hQ : IsExtraspecial 2 action.ker)
    (z : Subgroup.center action.ker) : z.val = 1 ∨ z.val = kernelSign := by
  let := hQ
  obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center action.ker)).mp
    (IsExtraspecial.center_order_p 2 action.ker)
  by_cases hz : z = 1
  · exact Or.inl (congrArg Subtype.val hz)
  · right
    exact congrArg Subtype.val ((hw z hz).trans
      (hw ⟨kernelSign, kernelSign_mem_center⟩ (fun h =>
        kernelSign_ne_one (congrArg Subtype.val h))).symm)

theorem kernel_center_fixed (hQ : IsExtraspecial 2 action.ker)
    (g : centralizer) (z : Subgroup.center action.ker) :
    MulAut.conjNormal g z.val = z.val := by
  rcases kernel_center_cases hQ z with hz | hz
  · rw [hz, map_one]
  · rw [hz]
    apply Subtype.ext
    change g * complementSign * g⁻¹ = complementSign
    rw [Subgroup.mem_center_iff.mp complementSign_mem_center, mul_inv_cancel_right]

abbrev KernelQuotient := action.ker ⧸ Subgroup.center action.ker

def kernelConjugation : centralizer →* MulAut action.ker := MulAut.conjNormal

def kernelQuotientAction : centralizer →* MulAut KernelQuotient :=
  (Subgroup.quotientAut (Subgroup.center action.ker)).comp kernelConjugation

theorem kernelQuotientAction_mk (r : centralizer) (q : action.ker) :
    kernelQuotientAction r (QuotientGroup.mk' (Subgroup.center action.ker) q) =
      QuotientGroup.mk' (Subgroup.center action.ker) (kernelConjugation r q) :=
  Subgroup.quotientAut_apply_mk _ _ _

def kernelQuotientFixed (r : centralizer) : Subgroup KernelQuotient :=
  (kernelQuotientAction r).toMonoidHom.eqLocus (MonoidHom.id _)

theorem mem_kernelQuotientFixed (r : centralizer) (q : KernelQuotient) :
    q ∈ kernelQuotientFixed r ↔ kernelQuotientAction r q = q := Iff.rfl

theorem kernelQuotient_card (hQ : IsExtraspecial 2 action.ker)
    (hcard : Nat.card action.ker = 512) : Nat.card KernelQuotient = 256 := by
  let := hQ
  have h := (Subgroup.center action.ker).card_eq_card_quotient_mul_card_subgroup
  rw [IsExtraspecial.center_order_p 2 action.ker, hcard] at h
  change 512 = Nat.card KernelQuotient * 2 at h
  omega

theorem kernelConjugation_cube {r : centralizer} (hr : orderOf r = 3) :
    kernelConjugation r ^ 3 = 1 := by
  rw [← map_pow, ← hr, pow_orderOf_eq_one, map_one]

theorem kernelQuotientAction_cube {r : centralizer} (hr : orderOf r = 3) :
    kernelQuotientAction r ^ 3 = 1 := by
  rw [← map_pow, ← hr, pow_orderOf_eq_one, map_one]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.PolynomialSelection
