module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.NonsplitStructure.Action

/-!
# Structure of the concrete nonsplit first-parabolic core

This interface exports the center of order two, the counts of square-one
elements distinguishing the actual core from the split quaternion-swap model,
the marked equivalence outerCore/⟨z⟩ ≃ E4 wr C2, and the actual conjugation
action. First-parabolic normalization remains explicit only in the action API.

The theorem below rules out a central-product presentation with a cyclic
factor of order four. Such a factor commutes with itself and the other factor,
so it would lie in the center, contradicting the proved center exponent two.
Thus the C4 * Q8² description printed in F.1.12(I)(13), using the central-product
convention of E.2.16, cannot describe this marked concrete subgroup. The
quotient assertion in 14.2.21 is separately proved and remains valid.

Sources: Aschbacher--Smith, E.2.16 (p.228), F.1.12(I)(13) (p.263), and
14.2.21 (p.988), refs/quasithin.pdf. Identification with the intrinsic two-core
and assembly of the complete source statements belong to FirstParabolic.
-/

public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic

/-- A central product with a faithfully embedded C4 factor is impossible, regardless of the other factor. -/
theorem no_cyclic_four_central_product (m : InnerModel) (C D : Subgroup outerCore)
    (e : C ≃* Multiplicative (ZMod 4))
    (hcomm : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c) (hspan : C ⊔ D = ⊤) : False := by
  have hc : C ≤ Subgroup.center outerCore := by
    intro c hc
    have hle : C ⊔ D ≤ Subgroup.centralizer ({c} : Set outerCore) := by
      apply sup_le
      · intro b hb
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have he : (⟨b,hb⟩ : C) * ⟨c,hc⟩ = ⟨c,hc⟩ * ⟨b,hb⟩ := by
          apply e.injective
          rw [map_mul, map_mul, mul_comm]
        exact congrArg (fun x : C => x.val) he
      · intro d hd
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c hc d hd).symm
    apply Subgroup.mem_center_iff.mpr
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hspan ▸ Subgroup.mem_top g))
  let f : Multiplicative (ZMod 4) →* outerCore := C.subtype.comp e.symm.toMonoidHom
  exact no_central_cyclic_four_embedding m f
    (Subtype.val_injective.comp e.symm.injective)
    (by rintro _ ⟨a,rfl⟩; exact hc (e.symm a).property)
end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
