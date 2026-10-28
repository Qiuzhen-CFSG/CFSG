module
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Bounds
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Amplified natural displacement under arbitrary involutory automorphisms

Every automorphism of SL₂ over a finite binary field is inner times a field
automorphism. The existing amplified natural bounds therefore apply to every
nonidentity involutory automorphism, including arbitrary mixing of the natural
summands. Centerlessness supplies an involutory inner lift in the inner case.
At field order four the bound is two binary dimensions per natural copy.

This is the natural-module input to the separated-support multiplicity step
of Aschbacher–Smith D.3.9 and D.3.21, pp.199–201 and 204–207.
-/

public noncomputable section
namespace Representation.AlternatingFive.AmplifiedNatural
open BinaryOffender.NaturalTensor
variable (F : Type*) [Field F] [Algebra (ZMod 2) F] [CharP F 2] [Finite F]
variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Arbitrary automorphism intertwiners satisfy the same amplified bound. -/
theorem automorphism_involution_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (e : V ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ g v, e (ρ g v) = naturalSumAction F ι g (e v))
    (T : Module.End (ZMod 2) V) (hTi : Function.Injective T)
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F))
    (ha2 : a * a = 1) (ha : a ≠ 1)
    (hT : ∀ g v, T (ρ g v) = ρ (a g) (T v)) :
    Fintype.card ι * n ≤ operatorFixedCodim T := by
  classical
  obtain ⟨r, σ, hσ⟩ := Theory.PSL2.sl2_semilinear_coverage a
  by_cases hs : σ = 1
  · have hinner : a = MulAut.conj r := by
      rw [hσ, hs]
      change MulAut.conj r * 1 = MulAut.conj r
      exact mul_one _
    have hr2 : r * r = 1 := by
      apply Theory.GroupTheory.conj_injective_of_center_eq_bot
        (Theory.PSL2.sl2_center_eq_bot F)
      rw [map_mul, ← hinner, ha2, map_one]
    have hr : r ≠ 1 := by
      intro hr
      exact ha (by rw [hinner, hr, map_one])
    apply natural_sum_inner_bound F hF ρ e he T hTi r hr2 hr
    intro g v
    simpa only [hinner, MulAut.conj_apply] using hT g v
  · have hs' : ∃ x, σ.toRingHom x ≠ x := by
      by_contra hn
      push Not at hn
      apply hs
      apply RingEquiv.ext
      exact hn
    apply natural_sum_field_bound F hF ρ e he T r σ.toRingHom hs'
    intro g v
    have hg : a g = r * Matrix.SpecialLinearGroup.map σ.toRingHom g * r⁻¹ := by
      rw [hσ]
      rfl
    simpa only [hg] using hT g v

end Representation.AlternatingFive.AmplifiedNatural
