module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.Contracts
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.SymplecticNormalForm
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.SymplecticProducts

/-!
# Conjugate products of intrinsic binary symplectic type-a₂ involutions

Definition E.2.6 characterizes type a₂ by displacement rank two and the
identity `B(x, v x) = 0` for every vector. The intrinsic normal-form theorem
constructs its two isotropic coordinates. An isometric group action transports
these coordinates through the literal right conjugate `h⁻¹ * v * h`.
The product calculation then gives order at most four in the original faithful
group, with no assumed product bound or involution-class table.

This is the general symplectic input to cases (4)–(7) in the proof of 6.2.19.
The symmetric model applications are assembled in `Symmetric.Source`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definition E.2.6, printed p.218 (PDF p.229), and the proof of 6.2.19,
printed p.691 (PDF p.708).
-/

namespace Representation.RankTwo.Symmetric

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Isometric conjugation transports the isotropic-pair coordinates. -/
public theorem HasA2NormalForm.conjugate
    (B : LinearMap.BilinForm (ZMod 2) V) (ρ : Representation (ZMod 2) G V)
    (hpres : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    {v : G} (hv : HasA2NormalForm B (ρ v)) (h : G) :
    HasA2NormalForm B (ρ (h⁻¹ * v * h)) := by
  obtain ⟨a, b, hab, hv⟩ := hv
  refine ⟨ρ h⁻¹ a, ρ h⁻¹ b, (hpres h⁻¹ a b).trans hab, ?_⟩
  intro x
  have hcancel (y : V) : ρ h⁻¹ (ρ h y) = y := by
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  have hpair (y : V) : B (ρ h x) y = B x (ρ h⁻¹ y) := by
    simpa only [hcancel] using (hpres h⁻¹ (ρ h x) y).symm
  calc
    ρ (h⁻¹ * v * h) x = ρ h⁻¹ (ρ v (ρ h x)) := by
      simp only [map_mul, Module.End.mul_apply]
    _ = x + B x (ρ h⁻¹ a) • ρ h⁻¹ b + B x (ρ h⁻¹ b) • ρ h⁻¹ a := by
      rw [hv, map_add, map_add, map_smul, map_smul, hcancel, hpair, hpair]

/-- The source type-a₂ hypotheses imply the conjugate-product order bound. -/
public theorem smallConjugateProducts_of_type_a2 [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (ρ : Representation (ZMod 2) G V)
    (hAlt : B.IsAlt) (hND : B.Nondegenerate) (hρ : Function.Injective ρ)
    (hpres : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (v : G) (hv2 : v ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (movedSpace ρ v) = 2)
    (hType : ∀ x, B x (ρ v x) = 0) : SmallConjugateProducts v := by
  have hnormal := hasA2NormalForm_of_representation B ρ v hAlt hND
    (by simpa only [pow_two] using hv2) hpres hr hType
  intro h
  exact orderOf_mul_le_four_of_normal_forms B hAlt ρ hρ hnormal
    (hnormal.conjugate B ρ hpres h)

end Representation.RankTwo.Symmetric
