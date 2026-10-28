module
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinary
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces.Certificates
/-!
# Detecting natural binary SL3 cohomology on an involution

The explicit normal form of a natural cocycle is a principal cocycle plus
a scalar multiple of the exceptional cocycle. Conjugating an involution
to an elementary transvection shows that a cocycle vanishing there has
zero spare coordinate. The exceptional coefficient is therefore zero.
This proves the fixed-involution exclusion on the actual matrix action,
without assuming an extension or indecomposability witness.

Source: Aschbacher--Smith B.4.8(3), printed p.91, and its use in original
12.2.25, printed p.805. The submodule convention is retained.
-/

public section
open Matrix Matrix.SpecialLinearGroup
namespace Representation.OneCohomology.SLHigherNatural.SLThreeBinary

/-- The exceptional natural cocycle stays nonprincipal on every involution. -/
theorem principal_of_zero_involution
    (f : cocycles (specialLinearNatural (k := ZMod 2) 3))
    (a : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (ha : a ≠ 1) (ha2 : a * a = 1) (hz : f.val a = 0) :
    ∃ v : Fin 3 → ZMod 2, principal (specialLinearNatural (k := ZMod 2) 3) v = f := by
  let t := transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 2)
  have ht : BinaryLinearThree.FourGroupGeometry.FixedSpaces.involution = t := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨k,hk⟩ := BinaryLinearThree.FourGroupGeometry.FixedSpaces.exists_involution_conjugator a ha ha2
  rw [ht] at hk
  have hfk := congrArg f.val hk
  rw [f.property,f.property,hz,add_zero] at hfk
  let ρ := specialLinearNatural (k := ZMod 2) 3
  have hkrel : ρ k⁻¹ * ρ a = ρ t * ρ k⁻¹ := by
    rw [← map_mul,← map_mul]
    apply congrArg ρ
    calc
      k⁻¹*a = k⁻¹*(a*k)*k⁻¹ := by group
      _ = k⁻¹*(k*t)*k⁻¹ := by rw [hk]
      _ = t*k⁻¹ := by group
  have hcancel : ρ k⁻¹ * ρ k = 1 := by rw [← map_mul,inv_mul_cancel,map_one]
  have he := congrArg (ρ k⁻¹) hfk
  change ρ k⁻¹ (ρ a (f.val k)) = ρ k⁻¹ (ρ k (f.val t) + f.val k) at he
  rw [map_add,← Module.End.mul_apply,← Module.End.mul_apply,hkrel,
    hcancel,Module.End.one_apply,Module.End.mul_apply] at he
  have hsp := congrFun he 1
  rw [action_transvection] at hsp
  simp only [Pi.add_apply,Pi.single_eq_of_ne (show (1 : Fin 3) ≠ 0 by decide),add_zero] at hsp
  have hzsp : f.val t 1 = 0 := by exact add_right_cancel (hsp.symm.trans (zero_add _).symm)
  obtain ⟨c,v,hform⟩ := normal_form f
  have hh := congrArg (fun z : cocycles (specialLinearNatural (k := ZMod 2) 3) => z.val t 1) hform
  change f.val t 1 = c * exceptional.val t 1 + (principal (specialLinearNatural 3) v).val t 1 at hh
  dsimp only [t] at hh hzsp
  rw [exceptional_spare 0 2 1 (by decide) (by decide) (by decide),principal_transvection] at hh
  simp only [Pi.single_eq_of_ne (show (1 : Fin 3) ≠ 0 by decide),mul_one,add_zero,hzsp] at hh
  refine ⟨v,?_⟩
  rw [← hh,zero_smul,zero_add] at hform
  exact hform.symm
end Representation.OneCohomology.SLHigherNatural.SLThreeBinary
