module
public import Theory.Representation.SL3.NaturalParabolicFixed
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.GroupAction.CentralElementaryLift

/-!
# Elementary lifts of proportional dual vectors

The stabilizer of a nonzero covector in SL₃(F) fixes no natural vector.
An explicit special-linear change of coordinates reduces this to the
line-parabolic transvection calculation. In characteristic two, consider
a central extension with natural kernel and a quotient of two dual copies.
The square of a lift of proportional dual vectors is fixed by that covector
stabilizer, hence is trivial. Every diagonal dual summand therefore has an
elementary abelian full preimage, including both coordinate summands.

Source: Aschbacher--Smith, C.1.35(2), printed pp.137--138. The source
application to the original Q and Z(Q) is in NonblockMSElementaryLifts.
-/

@[expose] public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.SL3ParabolicNatural
variable {F : Type*} [Field F]
private theorem dual_coordinate (f : Module.Dual F (Fin 3 → F)) (hf : f ≠ 0) :
    ∃ b : SL(3,F), ∀ v, f (specialLinearNatural 3 b v) = v 2 := by
  let w : Fin 3 → F := fun i => f (Pi.single i 1)
  have hform (v : Fin 3 → F) : f v = w ⬝ᵥ v := by
    have hv : v = ∑ i : Fin 3, v i • Pi.single i (1 : F) := by
      ext j
      fin_cases j <;> simp [Fin.sum_univ_three]
    conv_lhs => rw [hv]
    simp only [map_sum,map_smul,smul_eq_mul,dotProduct,w]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hw : w ≠ 0 := by
    intro he
    apply hf
    apply LinearMap.ext
    intro v
    rw [hform,he,zero_dotProduct]
    rfl
  obtain ⟨g,hg⟩ := exists_mulVec_eq_three w (![0,0,1] : Fin 3 → F) hw (by
    intro hh
    have := congrFun hh 2
    simp at this)
  refine ⟨g.transpose,?_⟩
  intro v
  rw [hform,specialLinearNatural_apply]
  change w ⬝ᵥ g.valᵀ *ᵥ v = v 2
  rw [dotProduct_mulVec,vecMul_transpose,hg]
  simp [dotProduct,Fin.sum_univ_three]

/-- The stabilizer of a nonzero dual vector has no fixed natural vector. -/
theorem dual_stabilizer_fixed_zero (f : Module.Dual F (Fin 3 → F)) (hf : f ≠ 0)
    (v : Fin 3 → F)
    (hv : ∀ g : SL(3,F), (specialLinearNatural 3).dual g f = f →
      specialLinearNatural 3 g v = v) : v = 0 := by
  let ρ := specialLinearNatural (k := F) 3
  obtain ⟨b,hb⟩ := dual_coordinate f hf
  have hh : ρ b⁻¹ v = 0 := by
    apply line_fixed_zero
    intro a ha
    have hfix : ρ.dual (b*a*b⁻¹) f = f := by
      apply LinearMap.ext
      intro w
      change f (ρ (b*a*b⁻¹)⁻¹ w) = f w
      simp only [ _root_.mul_inv_rev,inv_inv,map_mul,Module.End.mul_apply]
      rw [hb]
      have hai := (Matrix.PSL3.LinearThree.lineLocalSL F).inv_mem ha
      have hai' := (Matrix.PSL3.LinearThree.mem_lineLocalSL_iff F a⁻¹).mp hai
      have he (z : Fin 3 → F) : ρ a⁻¹ z 2 = z 2 := by
        change (a⁻¹.val.mulVec z) 2 = z 2
        simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_three,
          hai'.1,hai'.2.1,hai'.2.2,zero_mul,one_mul,zero_add]
      rw [he]
      have h := hb (ρ b⁻¹ w)
      rw [show specialLinearNatural 3 b (ρ b⁻¹ w) = w from ρ.self_inv_apply b w] at h
      exact h.symm
    have h := congrArg (ρ b⁻¹) (hv (b*a*b⁻¹) hfix)
    change ρ b⁻¹ (ρ (b*a*b⁻¹) v) = ρ b⁻¹ v at h
    simpa only [map_mul,Module.End.mul_apply,ρ.inv_self_apply] using h
  have h := congrArg (ρ b) hh
  simpa only [ρ.self_inv_apply,map_zero] using h
end Representation.SL3ParabolicNatural

open Subgroup
namespace Representation.SL3ParabolicNatural
variable {F A Q : Type*} [Field F] [CharP F 2] [Group A] [Group Q]
  [MulDistribMulAction A Q]

/-- In a central natural extension of two dual modules, every lift of a
pair of proportional dual vectors has order at most two. -/
theorem proportional_dual_lift_square
    (α : A →* SL(3,F)) (hα : Function.Surjective α)
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hc : p.ker ≤ center Q)
    (u : p.ker ≃* Multiplicative (Fin 3 → F))
    (hp : ∀ a q, (p (a • q)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (p q).toAdd)
    (hu : ∀ (a : A) (x y : p.ker), (y : Q) = a • (x : Q) →
      (u y).toAdd = specialLinearNatural 3 (α a) (u x).toAdd)
    (q : Q) (f : Module.Dual F (Fin 3 → F)) (a b : F)
    (hq : (p q).toAdd = (a • f,b • f)) : q ^ 2 = 1 := by
  have hexp (z : p.ker) : (z : Q)^2 = 1 := by
    have he : u (z^2) = 1 := by
      rw [map_pow,pow_two]
      apply Multiplicative.toAdd.injective
      change (u z).toAdd + (u z).toAdd = 0
      rw [←two_smul F,CharTwo.two_eq_zero,zero_smul]
    exact congrArg Subtype.val (u.injective (he.trans u.map_one.symm))
  have hs : q^2 ∈ p.ker := by
    change p (q^2) = 1
    rw [map_pow,pow_two]
    apply Multiplicative.toAdd.injective
    change (p q).toAdd + (p q).toAdd = 0
    rw [←two_smul F,CharTwo.two_eq_zero,zero_smul]
  by_cases hf : f = 0
  · have hqker : q ∈ p.ker := by
      change p q = 1
      apply Multiplicative.toAdd.injective
      change (p q).toAdd = 0
      rw [hq,hf,smul_zero,smul_zero]
      rfl
    exact hexp ⟨q,hqker⟩
  let z : p.ker := ⟨q^2,hs⟩
  have hz : (u z).toAdd = 0 := by
    apply dual_stabilizer_fixed_zero f hf
    intro g hg
    obtain ⟨k,rfl⟩ := hα g
    have hd : (k • q)/q ∈ p.ker := by
      apply p.div_mem_ker_iff.mpr
      apply Multiplicative.toAdd.injective
      rw [hp,hq]
      change (((specialLinearNatural 3).dual (α k)) (a • f),
        ((specialLinearNatural 3).dual (α k)) (b • f)) = (a • f,b • f)
      rw [map_smul,map_smul,hg]
    have hdcomm : Commute ((k • q)/q) q := (mem_center_iff.mp (hc hd) q).symm
    have hzfix : k • (q^2) = q^2 := by
      rw [smul_pow']
      calc
        (k • q)^2 = (((k • q)/q)*q)^2 := by rw [div_mul_cancel]
        _ = ((k • q)/q)^2*q^2 := hdcomm.mul_pow 2
        _ = q^2 := by rw [hexp ⟨_,hd⟩,one_mul]
    exact (hu k z z hzfix.symm).symm
  have he : u z = 1 := Multiplicative.toAdd.injective hz
  exact congrArg Subtype.val (u.injective (he.trans u.map_one.symm))
end Representation.SL3ParabolicNatural

namespace Representation.SL3ParabolicNatural
open Subgroup
variable {F : Type*} [Field F]
/-- A diagonal copy of the dual module, including the two coordinate axes. -/
def dualDiagonal (a b : F) : Multiplicative (Module.Dual F (Fin 3 → F)) →*
    Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)) where
  toFun f := Multiplicative.ofAdd (a • f.toAdd,b • f.toAdd)
  map_one' := by apply Multiplicative.toAdd.injective; exact Prod.ext (smul_zero _) (smul_zero _)
  map_mul' f g := by
    apply Multiplicative.toAdd.injective
    exact Prod.ext (smul_add a _ _) (smul_add b _ _)

theorem dualDiagonal_injective {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    Function.Injective (dualDiagonal a b) := by
  intro f g he
  have hh := congrArg Multiplicative.toAdd he
  change (a • f.toAdd,b • f.toAdd) = (a • g.toAdd,b • g.toAdd) at hh
  apply Multiplicative.toAdd.injective
  rcases hab with ha | hb
  · exact (smul_right_injective _ ha) (congrArg Prod.fst hh)
  · exact (smul_right_injective _ hb) (congrArg Prod.snd hh)

variable {A Q : Type*} [Group A] [Group Q] [CharP F 2] [MulDistribMulAction A Q]

/-- Every diagonal dual summand has an elementary abelian full preimage. -/
theorem dualDiagonal_preimage_elementary
    (α : A →* SL(3,F)) (hα : Function.Surjective α)
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hc : p.ker ≤ center Q) (u : p.ker ≃* Multiplicative (Fin 3 → F))
    (hp : ∀ a q, (p (a • q)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (p q).toAdd)
    (hu : ∀ (a : A) (x y : p.ker), (y : Q) = a • (x : Q) →
      (u y).toAdd = specialLinearNatural 3 (α a) (u x).toAdd)
    (a b : F) : IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p) := by
  let W := (dualDiagonal a b).range.comap p
  have hs (w : W) : w^2 = 1 := by
    obtain ⟨f,hf⟩ := w.property
    apply Subtype.ext
    exact proportional_dual_lift_square α hα p hc u hp hu w f.toAdd a b
      (congrArg Multiplicative.toAdd hf).symm
  have hi (w : W) : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs w)
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro x y
  calc
    x*y = (x*y)⁻¹ := (hi _).symm
    _ = y*x := by rw [_root_.mul_inv_rev,hi,hi]
end Representation.SL3ParabolicNatural
