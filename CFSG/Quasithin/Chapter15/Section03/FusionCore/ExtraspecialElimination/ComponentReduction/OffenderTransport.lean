module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import Theory.Representation.BinaryOffender.Stability

/-!
# Conjugating the selected quadratic best offender

The transition from (h) to (i) replaces `V_γ` by `V_α = V_γ^h`, for `h ∈ H`.
The star images are conjugate in the literal quotient `H/O₂(H)`. The
representation operator at `h` preserves quadratic action and offender
weights, so the new subgroup remains a quadratic best offender on `U_H/Z`.

This is transport of the independently proved geometric conclusion (h),
not an assertion that arbitrary subgroups are offenders.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1143.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- Star images commute with conjugation by elements of the local overgroup. -/
theorem starImage_map_conj (H A : Subgroup G) (hAH : A ≤ H) (h : H) :
    starImage H (A.map (MulAut.conj (h : G)).toMonoidHom) =
      (starImage H A).map (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h)).toMonoidHom := by
  let q := QuotientGroup.mk' (pCore 2 H)
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, he⟩ := ha
    refine ⟨q ⟨b, hAH hb⟩, ⟨⟨b, hAH hb⟩, hb, rfl⟩, ?_⟩
    have he' : h * (⟨b, hAH hb⟩ : H) * h⁻¹ = a := Subtype.ext he
    change q h * q ⟨b, hAH hb⟩ * (q h)⁻¹ = q a
    simpa only [map_mul, map_inv] using congrArg q he'
  · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨h * a * h⁻¹, ⟨a, ha, rfl⟩, ?_⟩
    change q (h * a * h⁻¹) = q h * q a * (q h)⁻¹
    simp only [map_mul, map_inv]

private theorem quadratic_map_conj {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (A : Subgroup G) (g : G)
    (hA : IsQuadratic ρ A) : IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  have hinv (x : W) : ρ g⁻¹ (ρ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  have hginv (x : W) : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) =
    ρ (g * b * g⁻¹) v - v
  simp only [map_mul, Module.End.mul_apply, map_sub, hinv]
  have he := congrArg (fun w => ρ g w) (hA a ha b hb (ρ g⁻¹ v))
  simpa only [map_sub, hginv] using he

/-- The selected conjugate `V_α = V_γ^h` is a quadratic best offender on
the same specified section action. In particular all subgroup weight
comparisons, not only the ordinary offending inequality, are transported. -/
theorem quadratic_bestOffender_conjugate
    (H U Z A : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z) (hAH : A ≤ H) (h : H)
    (hbest : IsBestOffender action.representation (starImage H A))
    (hquad : IsQuadratic action.representation (starImage H A)) :
    IsBestOffender action.representation
      (starImage H (A.map (MulAut.conj (h : G)).toMonoidHom)) ∧
    IsQuadratic action.representation
      (starImage H (A.map (MulAut.conj (h : G)).toMonoidHom)) := by
  rw [starImage_map_conj H A hAH h]
  exact ⟨hbest.map_conj action.representation _,
    quadratic_map_conj action.representation _ _ hquad⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
