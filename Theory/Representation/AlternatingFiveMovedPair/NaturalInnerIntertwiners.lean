module
public import Theory.Representation.AlternatingFiveMovedPair.NaturalSwapIntertwiners

/-!
# Unique involutory lifts of inner automorphisms of the natural pair

An involution intertwining conjugation by an involution r commutes with its
module action. Multiplying the two gives a centralizing involution, hence the
identity by the scalar commutant. Thus the intertwiner equals the action of r.
The endomorphism-ring calculation is kept abstract to avoid reducing the
concrete tensor action during elaboration.

Source: Aschbacher–Smith, quasithin manuscript, D.3.5, printed pp.195–196.
-/

@[expose] public noncomputable section
namespace Representation.AlternatingFiveMovedPair.Natural
open SL2FourNatural

private theorem inner_intertwiner_eq_of_centralizing_involution
    {K G U : Type*} [Field K] [Group G] [AddCommGroup U] [Module K U]
    (ρ : Representation K G U)
    (hc : ∀ D : Module.End K U, D * D = 1 →
      (∀ g v, D (ρ g v) = ρ g (D v)) → D = 1)
    (T : Module.End K U) (hT2 : T * T = 1) (r : G) (hr : r * r = 1)
    (hT : ∀ g v, T (ρ g v) = ρ (r * g * r⁻¹) (T v)) : T = ρ r := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_left hr
  have hTr : T * ρ r = ρ r * T := by
    apply LinearMap.ext
    intro v
    have h := hT r v
    rw [hr, one_mul, hri] at h
    exact h
  let D := ρ r * T
  have hD2 : D * D = 1 := by
    calc
      D * D = ρ r * (T * ρ r) * T := by simp only [D, mul_assoc]
      _ = ρ r * (ρ r * T) * T := by rw [hTr]
      _ = (ρ r * ρ r) * (T * T) := by simp only [mul_assoc]
      _ = 1 := by rw [← map_mul, hr, map_one, hT2, one_mul]
  have hDcomm : ∀ g v, D (ρ g v) = ρ g (D v) := by
    intro g v
    change ρ r (T (ρ g v)) = ρ g (ρ r (T v))
    have hgr : r * (r * g * r⁻¹) = g * r := by
      rw [← mul_assoc, ← mul_assoc, hr, one_mul, hri]
    rw [hT, ← Module.End.mul_apply, ← map_mul, hgr, map_mul, Module.End.mul_apply]
  have hD := hc D hD2 hDcomm
  calc
    T = (ρ r * ρ r) * T := by rw [← map_mul, hr, map_one, one_mul]
    _ = ρ r * D := by simp only [D, mul_assoc]
    _ = ρ r := by rw [hD, mul_one]

theorem inner_involution_intertwiner_eq_action (T : Module.End (ZMod 2) Space)
    (hT2 : T * T = 1) (r : SL × SL) (hr : r * r = 1)
    (hT : ∀ g v, T (action g v) = action (r * g * r⁻¹) (T v)) : T = action r :=
  inner_intertwiner_eq_of_centralizing_involution action
    centralizing_involution_eq_one T hT2 r hr hT

end Representation.AlternatingFiveMovedPair.Natural
