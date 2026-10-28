module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Basic
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

/-!
# Involution fusion in the natural split A₆ block

For a double transposition on the six letters, the fixed vectors in the
natural module are exactly its displacement space. Conjugating the actor
reduces every nonidentity involution to this calculation. Consequently every
involution outside the normal sixteen-group is conjugate to an actor lift,
and all such involutions form one class in the literal split group.

Source: Aschbacher–Smith 14.3.21(3), the fusion assertion used with 14.3.19(9).
-/

@[expose] public noncomputable section
namespace BinaryPermutation.SixNaturalSplit
open SemidirectProduct
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

private def doubleSwap : Actor :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩

private theorem doubleSwap_order : orderOf doubleSwap=2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide
  · decide

private theorem doubleSwap_fixed (v : natural (Fin 6))
    (hv : naturalRepresentation (Fin 6) doubleSwap.val v = v) :
    v=0 ∨ v=pairVector 0 1 ∨ v=pairVector 2 3 ∨ v=pairVector 4 5 := by
  rcases vector_cases v with rfl | ⟨⟨⟨i,j⟩,hij⟩,rfl⟩
  · exact Or.inl rfl
  change naturalRepresentation (Fin 6) doubleSwap.val (pairVector i j)=pairVector i j at hv
  change pairVector i j=0 ∨ pairVector i j=pairVector 0 1 ∨ pairVector i j=pairVector 2 3 ∨ pairVector i j=pairVector 4 5
  rw [pairVector_map] at hv
  have hh := (pairVector_eq_iff (doubleSwap.val.injective.ne hij.ne) hij.ne).mp hv
  have hp : (i=0 ∧ j=1) ∨ (i=2 ∧ j=3) ∨ (i=4 ∧ j=5) := by
    revert hij hh
    fin_cases i <;> fin_cases j <;> decide
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

private theorem doubleSwap_displacement (v : natural (Fin 6))
    (hv : naturalRepresentation (Fin 6) doubleSwap.val v = v) :
    ∃ w : natural (Fin 6), w + naturalRepresentation (Fin 6) doubleSwap.val w = v := by
  rcases doubleSwap_fixed v hv with rfl | rfl | rfl | rfl
  · exact ⟨0,by simp⟩
  · refine ⟨pairVector 0 4,?_⟩
    rw [pairVector_map]
    apply Subtype.ext
    change (constants (Fin 6)).mkQ _ + (constants (Fin 6)).mkQ _ = _
    rw [←map_add]
    apply congrArg (constants (Fin 6)).mkQ
    ext i
    fin_cases i <;> decide
  · refine ⟨pairVector 2 4,?_⟩
    rw [pairVector_map]
    apply Subtype.ext
    change (constants (Fin 6)).mkQ _ + (constants (Fin 6)).mkQ _ = _
    rw [←map_add]
    apply congrArg (constants (Fin 6)).mkQ
    ext i
    fin_cases i <;> decide
  · refine ⟨pairVector 0 2,?_⟩
    rw [pairVector_add,pairVector_map]
    apply Subtype.ext
    change (constants (Fin 6)).mkQ _ + (constants (Fin 6)).mkQ _ =
      (constants (Fin 6)).mkQ _ + (constants (Fin 6)).mkQ _
    rw [←map_add,←map_add]
    apply congrArg (constants (Fin 6)).mkQ
    ext i
    fin_cases i <;> decide

theorem involution_fixed_displacement (g : Actor) (hg : orderOf g=2)
    (a : Vector) (ha : action g a=a) : ∃ b : Vector, b * action g b=a := by
  obtain ⟨t,ht⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj doubleSwap g doubleSwap_order hg)
  have hc : action t * action doubleSwap = action g * action t := by
    rw [←map_mul,←map_mul]
    congr 1
    rw [←ht]
    group
  have hf : action doubleSwap (action t⁻¹ a)=action t⁻¹ a := by
    apply (action t).injective
    have hh := MulEquiv.congr_fun hc (action t⁻¹ a)
    simpa only [MulAut.mul_apply,map_inv,MulAut.apply_inv_self,ha] using hh
  obtain ⟨w,hw⟩ := doubleSwap_displacement (action t⁻¹ a).toAdd
    (show naturalRepresentation (Fin 6) doubleSwap.val (action t⁻¹ a).toAdd =
      (action t⁻¹ a).toAdd from congrArg Multiplicative.toAdd hf)
  let b : Vector := Multiplicative.ofAdd w
  have hb : b * action doubleSwap b=action t⁻¹ a := hw
  refine ⟨action t b,?_⟩
  have hh := MulEquiv.congr_fun hc b
  change action t (action doubleSwap b)=action g (action t b) at hh
  rw [←hh,←map_mul,hb]
  simp

private theorem vector_inv (a : Vector) : a⁻¹=a := by
  apply inv_eq_of_mul_eq_one_right
  apply Multiplicative.toAdd.injective
  change a.toAdd + a.toAdd = 0
  rw [←two_nsmul,←Nat.cast_smul_eq_nsmul (ZMod 2) 2]
  exact zero_smul (ZMod 2) _

/-- An involution outside the vector subgroup is conjugate to its actor lift. -/
theorem involution_conjugate_actor (x : Model) (hx : x^2=1) (hr : x.right≠1) :
    IsConj (inr x.right : Model) x := by
  have hg2 : x.right^2=1 := congrArg SemidirectProduct.right hx
  have hgo : orderOf x.right=2 := orderOf_eq_prime hg2 hr
  have hv : x.left * action x.right x.left=1 := by simpa only [pow_two,mul_left,one_left] using congrArg SemidirectProduct.left hx
  have hf : action x.right x.left=x.left := by
    calc action x.right x.left = x.left⁻¹ := eq_inv_of_mul_eq_one_right hv
         _ = x.left := vector_inv _
  obtain ⟨b,hb⟩ := involution_fixed_displacement x.right hgo x.left hf
  apply isConj_iff.mpr
  refine ⟨inl b,?_⟩
  apply SemidirectProduct.ext
  · simpa only [mul_left,mul_right,left_inl,right_inl,left_inr,right_inr,inv_left,
      map_one,MulAut.one_apply,one_mul,mul_one,inv_one,vector_inv] using hb
  · simp

/-- The involutions outside the normal sixteen-group form one class. -/
theorem outside_involutions_isConj (x y : Model) (hx : x^2=1) (hy : y^2=1)
    (hxout : x.right≠1) (hyout : y.right≠1) : IsConj x y := by
  have hxord : orderOf x.right=2 := orderOf_eq_prime (congrArg SemidirectProduct.right hx) hxout
  have hyord : orderOf y.right=2 := orderOf_eq_prime (congrArg SemidirectProduct.right hy) hyout
  exact (involution_conjugate_actor x hx hxout).symm.trans
    (((inr : Actor →* Model).map_isConj
      (AlternatingSix.ShadowLocal.involutions_isConj x.right y.right hxord hyord)).trans
        (involution_conjugate_actor y hy hyout))

end BinaryPermutation.SixNaturalSplit
