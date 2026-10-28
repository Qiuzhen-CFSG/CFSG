module
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements
public import Theory.Representation.BinaryAlternatingSevenFixedPoints

/-!
# Recognizing three-cycles on faithful binary A₇ four-spaces

An element of order three in A₇ is a three-cycle or a product of two
three-cycles. The latter fixes a plane in every faithful binary four-space:
conjugate to the explicit double cycle and apply the fixed-space calculation.
Thus an element of order three with no nonzero fixed vectors is a three-cycle.
No coordinates for the given representation are assumed.

Source: Aschbacher–Smith 5.1.13, printed p.638, refs/quasithin.pdf,
the cubic chief-factor calculation in the four-dimensional block.
-/

public noncomputable section
open Subgroup Equiv Representation.BinaryOffender
namespace Representation
/-- Only a three-cycle can act fixed-point freely on a faithful binary A7 four-space. -/
theorem binaryAlternatingSeven_threeCycle_of_fixedPointFree
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (a : alternatingGroup (Fin 7)) (ha : orderOf a = 3)
    (hfree : ∀ v, ρ a v = v → v = 0) : a.val.IsThreeCycle := by
  classical
  have hoa : orderOf a.val = 3 := (Subgroup.orderOf_coe a).trans ha
  obtain ⟨n,hn⟩ := Equiv.Perm.cycleType_prime_order
    (show (orderOf a.val).Prime by rw [hoa]; decide)
  have hs := a.val.sum_cycleType_le
  rw [hn,hoa,Multiset.sum_replicate,nsmul_eq_mul] at hs
  have hn01 : n = 0 ∨ n = 1 := by norm_num at hs; omega
  rcases hn01 with rfl | rfl
  · change a.val.cycleType = {3}
    simpa [hoa] using hn
  · have htype : a.val.cycleType = {3,3} := by simpa [hoa] using hn
    let b := AlternatingSevenConjugatePair.Model.doubleThreeCycle
    obtain ⟨s,hs⟩ := isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq
      (AlternatingSevenConjugatePair.Model.doubleThreeCycle_cycleType.trans htype.symm))
    let f : MulAut (alternatingGroup (Fin 7)) := MulAut.conjNormal s
    have he : f b = a := Subtype.ext hs
    let σ := ρ.comp f.toMonoidHom
    have hfix : fixedSpace σ (zpowers b) = ⊥ := by
      apply bot_unique
      intro v hv
      apply hfree v
      have hh := (mem_fixedSpace_zpowers_iff σ b v).mp hv
      change ρ (f b) v = v at hh
      rwa [he] at hh
    have hh := AlternatingSevenConjugatePair.Model.doubleThreeCycle_fixed_finrank σ hd
      (binaryAlternatingSeven_threeCycle_fixedPointFree σ (hf.comp f.injective) hd)
    change Module.finrank (ZMod 2) (fixedSpace σ (zpowers b)) = 2 at hh
    rw [hfix,finrank_bot] at hh
    contradiction

end Representation
