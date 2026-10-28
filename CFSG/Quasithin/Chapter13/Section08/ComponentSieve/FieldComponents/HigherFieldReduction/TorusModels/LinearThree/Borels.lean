module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree.Defs

/-!
# Intrinsic SL₃ and PSL₃ Borels in the higher-field argument

For either actual carrier over a field of order 2ⁿ, n>1, the two-residual
of the normalizer of a specified Sylow two-subgroup equals that normalizer.
Its two-core is precisely the specified Sylow. The imported matrix
calculations construct the quotient equivalences with two unit parameters,
retaining the cubic scalar quotient for PSL₃.

The arbitrary-actor centralizer and the degree-six outer commutator bound
remain separate obligations; these Borel calculations do not assert them.
The source assembly must also retain C_T(K) when lifting out of Aut(K).
Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
open Matrix.PSL3.CartanActions.BorelQuotient

/-- The full normalizer of a Sylow p-subgroup has that Sylow as its p-core,
here specialized to two and embedded back in the original carrier. -/
private theorem normalizer_twoCore {D : Type*} [Group D] (S : Sylow 2 D) :
    (normalizer (S : Set D)).pCoreIn 2 = S :=
  S.is_maximal' (isPGroup_pCoreIn 2 _)
    (le_pCoreIn_of_normalizes S.isPGroup' (S : Subgroup D).le_normalizer le_rfl)

private theorem field_card_gt_two {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) : 2 < Nat.card F := by
  rw [hF]
  have h : (2 : ℕ) ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The source two-residual is the whole intrinsic SL₃ Borel. -/
theorem special_residual_eq {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 SL(3,F)) :
    intrinsicResidual S = normalizer (S : Set SL(3,F)) := by
  rw [intrinsicResidual, borelResidual, residualIn,
    sylowSLNormalizer_twoResidual F (by omega) hF (field_card_gt_two hF hn) S,
    ← MonoidHom.range_eq_map, range_subtype]

/-- The source two-residual is the whole intrinsic PSL₃ Borel. -/
theorem projective_residual_eq {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 PSL(3,F)) :
    intrinsicResidual S = normalizer (S : Set PSL(3,F)) := by
  rw [intrinsicResidual, borelResidual, residualIn,
    sylowNormalizer_twoResidual F (by omega) hF (field_card_gt_two hF hn) S,
    ← MonoidHom.range_eq_map, range_subtype]

/-- O₂(B) and O₂(B₀) coincide with the specified Sylow in SL₃. -/
theorem special_residual_twoCore {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 SL(3,F)) :
    (intrinsicResidual S).pCoreIn 2 = S := by
  rw [special_residual_eq hF hn S, normalizer_twoCore]

/-- O₂(B) and O₂(B₀) coincide with the specified Sylow in PSL₃. -/
theorem projective_residual_twoCore {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 PSL(3,F)) :
    (intrinsicResidual S).pCoreIn 2 = S := by
  rw [projective_residual_eq hF hn S, normalizer_twoCore]

private theorem inner_core_fixes {D : Type*} [Group D] (B : Subgroup D)
    {s : D} (hs : s ∈ B.pCoreIn 2) : FixesResidualTorus B (MulAut.conj s) := by
  intro x hx
  have hxb : x ∈ B := (sup_le (map_subtype_le _) (pCoreIn_le 2 B)) hx
  obtain ⟨u,hu,rfl⟩ := hs
  let b : B := ⟨x,hxb⟩
  refine ⟨u*b*u⁻¹*b⁻¹, ?_, rfl⟩
  have hc := (inferInstance : (pCore 2 B).Normal).conj_mem u⁻¹
    ((pCore 2 B).inv_mem hu) b
  change u*b*u⁻¹*b⁻¹ ∈ pCore 2 B
  simpa only [mul_assoc] using (pCore 2 B).mul_mem hu hc

/-- Every inner Sylow actor fixes the source residual torus in SL₃. -/
theorem special_inner_fixes {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 SL(3,F))
    {α : MulAut SL(3,F)} (hα : α ∈ innerSylow S) :
    FixesResidualTorus (intrinsicResidual S) α := by
  obtain ⟨s,hs,rfl⟩ := hα
  apply inner_core_fixes
  rwa [special_residual_twoCore hF hn S]

/-- Every inner Sylow actor fixes the source residual torus in PSL₃. -/
theorem projective_inner_fixes {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 PSL(3,F))
    {α : MulAut PSL(3,F)} (hα : α ∈ innerSylow S) :
    FixesResidualTorus (intrinsicResidual S) α := by
  obtain ⟨s,hs,rfl⟩ := hα
  apply inner_core_fixes
  rwa [projective_residual_twoCore hF hn S]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
