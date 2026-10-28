module
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.InvolutionNormalForm
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Involution fixed-space bounds on irreducible binary SL₅ modules

The two involution classes have exterior displacement ranks three and four.
Conjugacy preserves those ranks, so every nonidentity involution fixes at
most seven dimensions. The proved ten-dimensional recognition, retaining
the original actor marking up to inverse transpose, transfers this bound to
every irreducible ten-dimensional module. Cauchy's theorem gives the same
bound for each even-order subgroup.

Source: Aschbacher--Smith I.1.6(7), 12.5.5 and the endpoint restriction in
C.4.8, printed pp.408,819,154. NormalizerFourModuleExclusion applies this to
the literal star radical and moved central quotient.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- Every nonidentity involution fixes at most seven dimensions on the exterior square. -/
theorem finrank_fixedSpace_involution_le_seven (g : Group) (hne : g ≠ 1) (hg : g*g = 1) :
    Module.finrank (ZMod 2) (fixedSpace g) ≤ 7 := by
  have hd := (displacement g).finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2) (displacement g).range +
    Module.finrank (ZMod 2) (fixedSpace g) = Module.finrank (ZMod 2) V at hd
  rw [finrank_exteriorModule_two] at hd
  rcases involution_conjugacy_exhaustion g hne hg with hc | hc
  · have he := finrank_displacement_eq_of_isConj hc
    rw [finrank_displacement_j₁] at he
    omega
  · have he := finrank_displacement_eq_of_isConj hc
    rw [finrank_displacement_j₂] at he
    omega

/-- The literal fixed space of any even-order subgroup has dimension at most
seven in every irreducible ten-dimensional binary SL₅(2) module. -/
theorem fixed_finrank_le_seven_of_even
    {D Y : Type*} [_root_.Group D] [Finite D]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (ρ : Representation (ZMod 2) D Y) [IsIrreducible ρ]
    (mark : D ≃* Group) (hd : Module.finrank (ZMod 2) Y = 10)
    (A : Subgroup D) (hA : 2 ∣ Nat.card A) :
    Module.finrank (ZMod 2) (BinaryOffender.fixedSpace ρ A) ≤ 7 := by
  obtain ⟨actor,c,_,hc⟩ := square_coordinates_of_finrank_ten ρ mark hd
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 2 hA
  have hne : actor (a : D) ≠ 1 := by
    intro he
    have ha1 : a = 1 := Subtype.ext (actor.injective (he.trans actor.map_one.symm))
    simp [ha1] at ha
  have hg : actor (a : D) * actor (a : D) = 1 := by
    rw [←map_mul]
    have he : a*a = 1 := by simpa [ha,pow_two] using pow_orderOf_eq_one a
    exact (congrArg (fun x : A => actor (x : D)) he).trans actor.map_one
  let f : BinaryOffender.fixedSpace ρ A →ₗ[ZMod 2] fixedSpace (actor (a : D)) :=
    (c.toLinearMap.comp (BinaryOffender.fixedSpace ρ A).subtype).codRestrict _ (fun y => by
      apply (mem_fixedSpace _ _).mpr
      change exteriorAction 2 (actor (a : D)) (c y.val) = c y.val
      rw [←hc]
      exact congrArg c (y.property a))
  have hf : Function.Injective f := fun x y he =>
    Subtype.ext (c.injective (congrArg Subtype.val he))
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans
    (finrank_fixedSpace_involution_le_seven _ hne hg)
end Representation.SL5ExteriorSquare
