module
public import Theory.Representation.SL3.BinaryDefiningFactors
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.RestrictedSeparation
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.FinCases

/-!
# Characters of the concrete binary SL₃ factors

The natural character is the embedded matrix trace. In characteristic two,
`trace(id) = 3 = 1`, so endomorphisms split explicitly as the scalar identity
line plus the trace-zero kernel. The splitting intertwines conjugation with
the trivial action and the actual adjoint action. Taking traces and using the
character formula for `linHom` gives the adjoint character `1 + X * Y`, where
`X` and `Y` are the natural and inverse-natural traces.

Source: the direct-sum description in GLS III, 2.8.10(c). No irreducibility,
finite-field, or classification theorem is used.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped MatrixGroups
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity.CharacterSeparation
variable {F K : Type*} [Field F] [Field K]

/-- The character of the actual natural action through a coefficient embedding. -/
lemma natural_character_trace (ι : F →+* K) (g : SL(3,F)) :
    (natural ι).character g = ι (Matrix.trace g.val) := by
  change LinearMap.trace K (Fin 3 → K) (Matrix.toLin' (g.val.map ι)) = _
  rw [Matrix.trace_toLin'_eq]
  simp [Matrix.trace, map_sum]

variable [CharP K 2]
private lemma three_eq_one : (3 : K) = 1 := by
  have h := CharTwo.add_self_eq_zero (1 : K)
  linear_combination h

private def traceSplit : (K × AdjointSpace K) ≃ₗ[K] Module.End K (Fin 3 → K) where
  toFun x := x.1 • LinearMap.id + x.2.val
  invFun f := (LinearMap.trace K _ f, ⟨f - LinearMap.trace K _ f • LinearMap.id, by
    simp [three_eq_one]⟩)
  left_inv x := by
    apply Prod.ext
    · simp [three_eq_one, show LinearMap.trace K _ x.2.val = 0 from x.2.property]
    · apply Subtype.ext
      simp [three_eq_one, show LinearMap.trace K _ x.2.val = 0 from x.2.property]
  right_inv f := by dsimp; abel
  map_add' x y := by
    dsimp
    rw [add_smul]
    abel
  map_smul' c x := by
    dsimp
    rw [smul_add, smul_smul]

private def adjointAction (ι : F →+* K) (g : SL(3,F)) : Module.End K (AdjointSpace K) :=
  (traceZero ι).toRepresentation g

private lemma traceSplit_conj (ι : F →+* K) (g : SL(3,F)) :
    (traceSplit (K := K)).symm.conj (((natural ι).linHom (natural ι)) g) =
      LinearMap.prodMap LinearMap.id (adjointAction ι g) := by
  apply LinearMap.ext
  intro x
  apply (traceSplit (K := K)).injective
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply]
  change natural ι g ∘ₗ (x.1 • LinearMap.id + x.2.val) ∘ₗ natural ι g⁻¹ =
    x.1 • LinearMap.id + natural ι g ∘ₗ x.2.val ∘ₗ natural ι g⁻¹
  have h : natural ι g ∘ₗ natural ι g⁻¹ = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl
  simp [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul,
    LinearMap.smul_comp, h]

/-- The character of the actual trace-zero adjoint action in characteristic two. -/
lemma adjoint_character (ι : F →+* K) (g : SL(3,F)) :
    (factorRep ι .adjoint).character g =
      1 + ι (Matrix.trace g.val) * ι (Matrix.trace g⁻¹.val) := by
  have h : ((natural ι).linHom (natural ι)).character g =
      1 + (factorRep ι .adjoint).character g := by
    change LinearMap.trace K (Module.End K (Fin 3 → K))
      (((natural ι).linHom (natural ι)) g) =
        1 + LinearMap.trace K (AdjointSpace K) (adjointAction ι g)
    have he := LinearMap.trace_conj'
      (M := Module.End K (Fin 3 → K)) (N := K × AdjointSpace K)
      (((natural ι).linHom (natural ι)) g) (traceSplit (K := K)).symm
    rw [traceSplit_conj] at he
    let : Module.Free K (AdjointSpace K) := Module.Free.of_divisionRing K (AdjointSpace K)
    have hp := LinearMap.trace_prodMap' (R := K) (M := K) (N := AdjointSpace K)
      LinearMap.id (adjointAction ι g)
    rw [hp] at he
    rw [← he]
    simp
  rw [Representation.char_linHom, natural_character_trace, natural_character_trace] at h
  have hh := congrArg (fun x : K => 1 + x) h
  simpa only [← add_assoc, CharTwo.add_self_eq_zero, zero_add, mul_comm] using hh.symm

end Representation.SL3.BinaryDefiningFactors.TensorSimplicity.CharacterSeparation
