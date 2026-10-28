module

public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FieldDescent
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement

/-!
# No binary transvections in the natural SL₂(4) normalizer

A rank-one binary linear automorphism is an involution. An element of the
natural SL₂(4) image has even displacement rank by restriction of scalars.
Every other involution in the normalizer has four fixed vectors by field
descent, whereas a binary transvection on this four-space would fix eight.
Thus the entire actual normalizer contains no binary transvections.

This supplies the model exclusion in Aschbacher–Smith, J.2.2(5), printed
pp.432–433 (combined manuscript of 1 March 2004), using the semilinear
normalizer and field-involution facts of 6.2.5, printed pp.680–681.
-/

public section
namespace Representation.SL2FourNatural
open SemilinearNormalizer

private theorem square_eq_one_of_rank_one (e : V ≃ₗ[ZMod 2] V)
    (h : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) = 1) :
    e ^ 2 = 1 := by
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr h.le
  have he' (x : V) : e x = x + f x • v :=
    congrArg (fun l : V →ₗ[ZMod 2] V => l x) he
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with hz | ho
    · exact hz
    have hev : e v = 0 := by rw [he', ho, one_smul, ZModModule.add_self]
    have hv := e.map_eq_zero_iff.mp hev
    rw [hv, map_zero] at ho
    exact (zero_ne_one ho).elim
  apply LinearEquiv.ext
  intro x
  change e (e x) = x
  rw [he', he', map_add, map_smul, hfv, smul_zero, add_zero]
  simp only [add_assoc, ZModModule.add_self, add_zero]

/-- The binary normalizer of the actual natural SL₂(4) group has no transvections. -/
theorem normalizer_no_rank_one (e : V ≃ₗ[ZMod 2] V)
    (he : e ∈ SemilinearNormalizer.normalizer) :
    Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≠ 1 := by
  intro hr
  by_cases hs : e ∈ action.range
  · obtain ⟨g, rfl⟩ := hs
    have h : Module.finrank (ZMod 2)
        (LinearMap.range ((action g).toLinearMap - LinearMap.id)) =
        Module.finrank (ZMod 2) F * Module.finrank F
          (LinearMap.range ((Matrix.SpecialLinearGroup.toLin' g).toLinearMap - LinearMap.id)) :=
      QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2)
        (Matrix.SpecialLinearGroup.toLin' g)
    rw [QuadraticAlgebra.finrank_eq_two, hr] at h
    omega
  · have hc := card_normalizer_involution_fixed e he (square_eq_one_of_rank_one e hr) hs
    have hd := (e.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
    rw [hr, ← LinearMap.fixedSubmodule_eq_ker, finrank_vector] at hd
    have hdim : Module.finrank (ZMod 2) e.toLinearMap.fixedSubmodule = 3 := by omega
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := e.toLinearMap.fixedSubmodule)
    rw [hc, Nat.card_zmod, hdim] at hcard
    norm_num at hcard

end Representation.SL2FourNatural
