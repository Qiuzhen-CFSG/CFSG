module
public import Theory.SpecificGroups.SL2.SylowTorusAutomorphisms

/-!
# A field action for a Sylow and Cartan factor exchanger

Compose a factor exchanger with the literal swap and apply the two-factor
Sylow-Cartan automorphism theorem. Preservation of the full inverse
diagonal then identifies its two field automorphisms. Consequently it acts
on that diagonal by a single field automorphism followed by inversion.
No involution hypothesis on the exchanger is needed.

The original tensor-Cartan consumer in Chapter 10 supplies all three
preservation properties on its literal quotient action.
Source: Aschbacher--Smith 9.2.7, pp.731--732, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
open BenderSuzuki.ZD.Linear
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "diag" => fun z : Fˣ => diag2 (z:F) (Units.ne_zero z)

/-- Exchanging the two factors while preserving the inverse diagonal forces
the same field automorphism on both Cartan coordinates. -/
theorem pair_sylow_torus_exchanger_field (hF : 2 < Nat.card F)
    (e : MulAut (SL(2,F) × SL(2,F))) (a : MulAut SL(2,F))
    (ha : ∀ x, e (x,1) = (1,a x))
    (hU : ((upperUnipotent F).prod (upperUnipotent F)).map e.toMonoidHom =
      (upperUnipotent F).prod (upperUnipotent F))
    (hD : ∀ z : Fˣ × Fˣ, ∃ w : Fˣ × Fˣ,
      e (diag z.1,diag z.2) = (diag w.1,diag w.2))
    (hB : ∀ z : Fˣ, ∃ w : Fˣ,
      e (diag z,diag z⁻¹) = (diag w,diag w⁻¹)) :
    ∃ σ : F ≃+* F, ∀ z : Fˣ × Fˣ,
      e (diag z.1,diag z.2) =
        (diag (Units.map σ.toMonoidHom z.2),diag (Units.map σ.toMonoidHom z.1)) := by
  let s : MulAut (SL(2,F) × SL(2,F)) := MulEquiv.prodComm
  let e' := e.trans s
  have ha' (x : SL(2,F)) : e' (x,1) = (a x,1) := by
    change s (e (x,1)) = _
    rw [ha]
    rfl
  have hU' : ((upperUnipotent F).prod (upperUnipotent F)).map e'.toMonoidHom =
      (upperUnipotent F).prod (upperUnipotent F) := by
    change ((upperUnipotent F).prod (upperUnipotent F)).map (s.toMonoidHom.comp e.toMonoidHom) = _
    rw [←Subgroup.map_map,hU]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy.2,hy.1⟩
    · intro hx
      exact ⟨(x.2,x.1),⟨hx.2,hx.1⟩,rfl⟩
  have hD' (z : Fˣ × Fˣ) : ∃ w : Fˣ × Fˣ,
      e' (diag z.1,diag z.2) = (diag w.1,diag w.2) := by
    obtain ⟨w,hw⟩ := hD z
    exact ⟨(w.2,w.1),congrArg s hw⟩
  obtain ⟨d,σ,τ,he⟩ := pair_sylow_torus_preserving_semilinear hF e' a ha' hU' hD'
  have hdiag (z : Fˣ × Fˣ) : e' (diag z.1,diag z.2) =
      (diag (Units.map σ.toMonoidHom z.1),diag (Units.map τ.toMonoidHom z.2)) := by
    rw [he]
    exact Prod.ext (diagonal_field_apply_diagonal d.1 z.1 σ)
      (diagonal_field_apply_diagonal d.2 z.2 τ)
  have hστ : σ = τ := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · let z := Units.mk0 x hx
      obtain ⟨w,hw⟩ := hB z
      have hh := (hdiag (z,z⁻¹)).symm.trans (congrArg s hw)
      have h1 : Units.map σ.toMonoidHom z = w⁻¹ := by
        apply Units.ext
        simpa [diag2_coe',s] using
          congrArg (fun p : SL(2,F) × SL(2,F) => p.1.val 0 0) hh
      have h2 : Units.map τ.toMonoidHom z⁻¹ = w := by
        apply Units.ext
        simpa [diag2_coe',s] using
          congrArg (fun p : SL(2,F) × SL(2,F) => p.2.val 0 0) hh
      have hh' : Units.map σ.toMonoidHom z = Units.map τ.toMonoidHom z := by
        rw [h1,←h2,←map_inv,inv_inv]
      exact congrArg Units.val hh'
  refine ⟨σ,fun z => ?_⟩
  have hh := congrArg s (hdiag z)
  change s (s (e (diag z.1,diag z.2))) = _ at hh
  change e (diag z.1,diag z.2) =
    (diag (Units.map τ.toMonoidHom z.2),diag (Units.map σ.toMonoidHom z.1)) at hh
  rw [←hστ] at hh
  exact hh
end Matrix.SpecialLinearGroup
