module
public import Theory.SpecificGroups.MinusExtraspecial.FivePointLifts
public import Theory.Representation.BinaryAlternatingNaturalCohomology
import Mathlib.Tactic.LinearCombination

/-!
# Conjugacy of faithful alternating actions on the minus extraspecial core

The difference between two actions with the same five-point marking is a
binary permutation-module cocycle. Its vanishing gives five sign changes.
Adding the constant vector makes their sum zero, and the commutator pairing
realizes these changes by an inner automorphism of the actual core.

Source: DGS, Groups and Graphs (1985), (5.14)--(5.16), pp.116--117;
the action comparison in the J₂ exercise following (10.9), p.163.
-/

public noncomputable section
open scoped BigOperators
namespace MinusExtraspecial.ActionConjugacy
open FivePointLifts FixedFourCalculation.Outside
open Representation.OneCohomology

private def bit (c : ZMod 2) : Model := if c = 0 then 1 else quaternion z

private theorem bit_add (c d : ZMod 2) : bit (c+d) = bit c * bit d := by
  revert c d; decide +kernel

private theorem bit_injective : Function.Injective bit := by decide +kernel

private theorem bit_apply (a : MulAut Model) (c : ZMod 2) : a (bit c) = bit c := by
  unfold bit
  split_ifs <;> simp only [map_one,central_fixed]

private def signs (a : MulAut Model) (i : Fin 5) : ZMod 2 :=
  if a (lift ((fivePointAction a).symm i)) = lift i then 0 else 1

private theorem signs_spec (a : MulAut Model) (i : Fin 5) :
    a (lift ((fivePointAction a).symm i)) =
      bit (signs a i) * lift i := by
  rcases lift_image a ((fivePointAction a).symm i) with h | h
  · simp only [Equiv.apply_symm_apply] at h
    simp only [signs,h,↓reduceIte]
    exact (one_mul _).symm
  · simp only [Equiv.apply_symm_apply] at h
    have hn : a (lift ((fivePointAction a).symm i)) ≠ lift i := by
      rw [h]
      intro he
      have hz := mul_right_cancel (he.trans (one_mul _).symm)
      exact (show quaternion z ≠ 1 by decide +kernel) hz
    simp only [signs,if_neg hn]
    exact h

private theorem signs_mul (a b : MulAut Model) (i : Fin 5) :
    signs (a*b) i = signs b ((fivePointAction a).symm i) + signs a i := by
  apply bit_injective
  apply mul_right_cancel (b := lift i)
  rw [←signs_spec]
  change a (b (lift ((fivePointAction (a*b)).symm i))) = _
  rw [map_mul]
  change a (b (lift ((fivePointAction b).symm ((fivePointAction a).symm i)))) = _
  rw [signs_spec,map_mul,bit_apply,signs_spec,←mul_assoc]
  rw [←bit_add]

private theorem ext_lifts {a b : MulAut Model} (h : ∀ i, a (lift i) = b (lift i)) : a = b := by
  have hc : ∀ x : Model, ∃ i j k l : Fin 5, lift i * lift j * lift k * lift l = x := by
    decide +kernel
  apply MulEquiv.ext
  intro x
  obtain ⟨i,j,k,l,rfl⟩ := hc x
  simp only [map_mul,h]

private theorem inner_signs (w : Fin 5 → ZMod 2) (hw : ∑ i, w i = 0) :
    ∃ n : Model, ∀ i, MulAut.conj n (lift i) =
      bit (w i) * lift i := by
  revert w
  decide +kernel

/-- Actions with the same alternating permutation marking differ by an inner
change of core coordinates. The actor itself is unchanged. -/
theorem exists_inner_conjugacy
    (φ ψ : alternatingGroup (Fin 5) →* MulAut Model)
    (hφ : ∀ g, fivePointAction (φ g) = (g : Equiv.Perm (Fin 5)))
    (hψ : ∀ g, fivePointAction (ψ g) = (g : Equiv.Perm (Fin 5))) :
    ∃ n : Model, ∀ g, MulAut.conj n * φ g = ψ g * MulAut.conj n := by
  let f : cocycles (BinaryPermutation.alternatingRepresentation (Fin 5)) :=
    ⟨fun g i => signs (φ g) i - signs (ψ g) i, by
      intro g h
      funext i
      change signs (φ (g*h)) i - signs (ψ (g*h)) i =
        (signs (φ h) (g.val.symm i) - signs (ψ h) (g.val.symm i)) +
          (signs (φ g) i - signs (ψ g) i)
      rw [map_mul,map_mul,signs_mul,signs_mul,hφ,hψ]
      abel⟩
  obtain ⟨v,hv⟩ := BinaryPermutation.alternating_principal_surjective (Fin 5) (by simp) f
  let w : Fin 5 → ZMod 2 := fun i => v i - ∑ j, v j
  have hw : ∑ i, w i = 0 := by
    simp only [w,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [show ((5 : ℕ) : ZMod 2) = 1 by decide,one_mul,sub_self]
  obtain ⟨n,hn⟩ := inner_signs w hw
  refine ⟨n,fun g => ext_lifts (fun i => ?_)⟩
  have hd := congrArg (fun c : cocycles (BinaryPermutation.alternatingRepresentation (Fin 5)) =>
    c.val g (g.val i)) hv
  change v (g.val.symm (g.val i)) - v (g.val i) = signs (φ g) (g.val i) - signs (ψ g) (g.val i) at hd
  rw [g.val.symm_apply_apply] at hd
  have hsφ := signs_spec (φ g) (g.val i)
  have hsψ := signs_spec (ψ g) (g.val i)
  rw [hφ,g.val.symm_apply_apply] at hsφ
  rw [hψ,g.val.symm_apply_apply] at hsψ
  change MulAut.conj n (φ g (lift i)) = ψ g (MulAut.conj n (lift i))
  rw [hsφ,map_mul,bit_apply,hn,hn,map_mul,bit_apply,hsψ,←mul_assoc,←mul_assoc]
  congr 1
  rw [←bit_add,←bit_add]
  congr 1
  dsimp [w]
  linear_combination -hd

/-- Faithful A₅ actions have conjugate images, with the quotient relabeling
recorded explicitly and the conjugator inside the core. -/
theorem exists_faithful_conjugacy
    (φ ψ : alternatingGroup (Fin 5) →* MulAut Model)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    ∃ (d : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5)) (n : Model),
      ∀ g, MulAut.conj n * φ g = ψ (d g) * MulAut.conj n := by
  obtain ⟨dφ,hdφ⟩ := FivePointLifts.exists_marking φ hφ
  obtain ⟨dψ,hdψ⟩ := FivePointLifts.exists_marking ψ hψ
  obtain ⟨n,hn⟩ := exists_inner_conjugacy
    (φ.comp dφ.symm.toMonoidHom) (ψ.comp dψ.symm.toMonoidHom)
    (fun g => by
      simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,dφ.apply_symm_apply]
        using hdφ (dφ.symm g))
    (fun g => by
      simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,dψ.apply_symm_apply]
        using hdψ (dψ.symm g))
  exact ⟨dφ.trans dψ.symm,n,fun g => by
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,dφ.symm_apply_apply,
      MulEquiv.trans_apply] using hn (dφ g)⟩

end MinusExtraspecial.ActionConjugacy
