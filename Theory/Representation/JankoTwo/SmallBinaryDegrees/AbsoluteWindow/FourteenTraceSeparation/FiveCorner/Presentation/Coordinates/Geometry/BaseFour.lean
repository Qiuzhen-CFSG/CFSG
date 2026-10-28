module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Geometry.Contracts
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# Four-point equality checks in the actual J₂ carrier

The certified normal forms use successive transversals at points 0, 1, 2, 3.
Their existing decoders show that agreement on these four points determines
an element of the actual carrier. Thus literal Schreier edges need only four
point checks each. This uses the proved normal-form coverage, not an assumed
base or a permutation-group order inferred from discovery.

Source: the ATLAS J2G1-p100B0 data and the existing FirstParabolic.OrderData
normal-form separation; application: the literal five-corner coset geometry.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry
open Sporadic.LeechRelated.J2
open GeneratorPair.SecondOrbitCertificate ExceptionalParabolics.FirstParabolic.OrderData

def basePoint (i : Fin 4) : Fin 100 := i.castLE (by decide)

private theorem normalForm_eq_of_base {i j : Index}
    (h : ∀ x : Fin 4, normalForm i (basePoint x) = normalForm j (basePoint x)) : i = j := by
  rcases i with ⟨i₀, i₁, i₂, i₃⟩
  rcases j with ⟨j₀, j₁, j₂, j₃⟩
  have h₀ := congrArg decode0 (h 0)
  simp only [show basePoint 0 = 0 from rfl, normalForm, Equiv.Perm.mul_apply,
    rep3_fix0, rep2_fix0, rep1_fix0, decode0_spec] at h₀
  subst j₀
  have h₁ := h 1
  simp only [show basePoint 1 = 1 from rfl, normalForm, Equiv.Perm.mul_apply,
    rep3_fix1, rep2_fix1] at h₁
  have h₁' := congrArg decode1 ((rep0 i₀).injective h₁)
  simp only [decode1_spec] at h₁'
  subst j₁
  have h₂ := h 2
  simp only [show basePoint 2 = 2 from rfl, normalForm, Equiv.Perm.mul_apply, rep3_fix2] at h₂
  have h₂' := congrArg decode2 ((rep1 i₁).injective ((rep0 i₀).injective h₂))
  simp only [decode2_spec] at h₂'
  subst j₂
  have h₃ := h 3
  simp only [show basePoint 3 = 3 from rfl, normalForm, Equiv.Perm.mul_apply] at h₃
  have h₃' := congrArg decode3
    ((rep2 i₂).injective ((rep1 i₁).injective ((rep0 i₀).injective h₃)))
  simp only [decode3_spec] at h₃'
  subst j₃
  rfl

theorem carrier_ext_baseFour {g h : Carrier}
    (he : ∀ x : Fin 4, inclusion g (basePoint x) = inclusion h (basePoint x)) : g = h := by
  obtain ⟨i, hi⟩ := normalForm_cover g
  obtain ⟨j, hj⟩ := normalForm_cover h
  apply inclusion_injective
  rw [hi, hj]
  have he' : i = j := normalForm_eq_of_base (by simpa only [← hi, ← hj] using he)
  rw [he']

/-- Turn four-point checks with the literal subgroup powers into actual carrier
edge equations. This is the finite-check consumer used by SchreierData. -/
def schreierCertificate_of_baseFour (r : Point → Carrier) (hzero : r 0 = 1)
    (powers : Point → Fin 4 → CoefficientTheory.PowerIndex)
    (hcheck : ∀ x l j,
      inclusion (r x) (tableLetter l (basePoint j)) =
        (leftTable ^ (powers x l).1.val * rightTable ^ (powers x l).2.val)
          (inclusion (r (step l x)) (basePoint j))) : SchreierCertificate where
  repr := r
  at_zero := hzero
  edge x l := by
    refine ⟨CoefficientTheory.subgroupElement (powers x l), ?_⟩
    apply carrier_ext_baseFour
    intro j
    simpa only [CoefficientTheory.subgroupElement, map_mul, map_pow,
      inclusion_letter, inclusion_leftGenerator, inclusion_rightGenerator,
      Equiv.Perm.mul_apply] using hcheck x l j

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Geometry
