module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortQuotient
public import GorensteinWalter.SL2ProjectiveCover

/-!
# A perfect actor on the unitary orthogonal quotient

The fixed-field SL₂ embeds in the actual residual short-root centralizer.
For q ≥ 4 it is perfect. After killing the entire short-root line, its
image is transitive on the nonzero vectors of the orthogonal module.
The assertion retains the specified homomorphism and long-root marker,
so it applies to the ambient line-normalizer quotient in F.4.42.

Source: Aschbacher–Smith F.4.42, printed p.295 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Matrix Subgroup
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourShortRoot
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- The conjugators for the quotient orbit lie in a single actual perfect
subgroup, rather than merely in the prime-to-two residual. -/
theorem orthogonal_image_perfect_orbit
    (hK : 3 < Nat.card (FixedBy.subfield F σ))
    {H : Type*} [Group H] (f : shortCentralizer F σ hσ →* H)
    (hU : (shortLine F σ hσ).subgroupOf (shortCentralizer F σ hσ) ≤ f.ker) :
    ∃ P : Subgroup H, Group.IsPerfect P ∧ P ≤ f.range ∧
      ∀ v ∈ ((orthogonalRadical F σ hσ).subgroupOf
        (shortCentralizer F σ hσ)).map f, v ≠ 1 →
        ∃ a ∈ P, a * f (longMark F σ hσ) * a⁻¹ = v := by
  let k := f.comp (fixedLeviHom F σ hσ)
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three _ hK
  refine ⟨k.range, Group.IsPerfect.range k, ?_, ?_⟩
  · rintro _ ⟨a,rfl⟩
    exact ⟨fixedLeviHom F σ hσ a,rfl⟩
  · intro v hv hv1
    obtain ⟨A,he⟩ := orthogonal_image_fusion F σ hσ f hU hv hv1
    obtain ⟨B,hB⟩ := A.property
    have heq : fixedLeviHom F σ hσ B = fixedLevi F σ hσ A := by
      apply Subtype.ext
      change UnitaryFourPlaneRadical.levi F σ hσ
        (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype B) =
        UnitaryFourPlaneRadical.levi F σ hσ A.val
      rw [hB]
    exact ⟨f (fixedLevi F σ hσ A),⟨B,congrArg f heq⟩,he⟩

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
