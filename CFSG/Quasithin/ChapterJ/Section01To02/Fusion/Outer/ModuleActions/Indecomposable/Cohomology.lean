module

public import CFSG.Quasithin.ChapterJ.Defs
public import Theory.Representation.SL2NaturalFirstCohomology.FourOuter.Dual

/-!
# Natural S₅ cohomology from explicit Frobenius coordinates

For any marking of the actual restricted natural SL₂(4) module, an involution
whose coordinates are an F₄-linear map followed by Frobenius gives
`dim H¹(S₅, V*) ≤ 1` over F₂. Conjugation on the literal alternating subgroup
supplies the normality and outer-action maps for the reusable restriction
calculation; trace-determinant self-duality handles the contragredient.

The coordinate witness remains explicit. The semilinear normalizer theorem
must supply it in the final J.2.5 assembly. This bound is precisely the premise
of `Fusion.Outer.kernel_moved_of_H1_bound` and its specialization to the literal
Q/U → Q/HC projection; this module does not import that assembly module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(3) and J.2.5, printed pp.432 and 434 (PDF pp.443 and 445).
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.L2FourAction
open Representation Representation.OneCohomology Representation.SL2FourNatural
/-- The bound used for the natural head of the six-dimensional indecomposable module. -/
theorem finrank_dual_H1_le_one_of_frobenius (r : L2FourAction)
    (t : S5) (_htodd : t ∉ alternatingGroup (Fin 5)) (ht : t * t = 1)
    (A : V ≃ₗ[F] V) (hA : ∀ v, r.action t v = A (frobeniusLinear v)) :
    Module.finrank (ZMod 2) (H1 r.action.dual) ≤ 1 := by
  let ι : SL →* S5 := (alternatingGroup (Fin 5)).subtype.comp r.marking.toMonoidHom
  let σ : SL →* SL := r.marking.symm.toMonoidHom.comp
    ((MulAut.conjNormal t⁻¹).toMonoidHom.comp r.marking.toMonoidHom)
  have hc (g : SL) : t * ι (σ g) = ι g * t := by
    change t * (r.marking (r.marking.symm (MulAut.conjNormal t⁻¹ (r.marking g))) : alternatingGroup (Fin 5)) = _
    rw [r.marking.apply_symm_apply]
    change t * (t⁻¹ * (r.marking g : S5) * (t⁻¹)⁻¹) = _
    simp [ι, mul_assoc]
  have hn (g : S5) (x : SL) : ∃ y : SL, ι x * g = g * ι y := by
    refine ⟨r.marking.symm (MulAut.conjNormal g⁻¹ (r.marking x)), ?_⟩
    change (r.marking x : S5) * g =
      g * (r.marking (r.marking.symm (MulAut.conjNormal g⁻¹ (r.marking x))) : alternatingGroup (Fin 5))
    rw [r.marking.apply_symm_apply]
    change (r.marking x : S5) * g = g * (g⁻¹ * (r.marking x : S5) * (g⁻¹)⁻¹)
    simp [mul_assoc]
  apply Representation.SL2NaturalH1.FourOuter.finrank_dual_le_one
    r.action ι r.restriction hn t ht σ hc
  intro a v
  rw [hA, frobeniusLinear_smul, map_smul, hA]
end CFSG.Quasithin.ChapterJ.L2FourAction
