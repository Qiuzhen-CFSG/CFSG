module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Assembly
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# The unchanged residual in the contrary replacement

In the reduction of 15.4.20, replace the placed overgroup H by KU, where
K is the normal closure of the original X in H. The embedding reduction
identifies K with the embedded prime-to-three residual of H. Idempotence
and monotonicity of this residual identify the residual of KU with the
same K. Applying the source normal-closure theorem to the replacement
then identifies its normal closure with K as well. Relative normality
gives the literal set product KU.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed pp.1163–1164.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary

universe u
variable {G : Type u} [Group G] [Finite G]

private theorem embedded_residual_eq_of_intermediate
    (p : ℕ) [Fact p.Prime] {H K D : Subgroup G}
    (hK : K = (primeToResidual p H).map H.subtype)
    (hKD : K ≤ D) (hDH : D ≤ H) :
    K = (primeToResidual p D).map D.subtype := by
  have hid : (primeToResidual p K).map K.subtype = K := by
    rw [hK, ← map_embedded_primeToResidual_of_hom p (primeToResidual p H) H.subtype,
      embedded_primeToResidual_eq_of_normal p (primeToResidual p H) le_rfl]
  apply le_antisymm
  · calc
      K = (primeToResidual p K).map K.subtype := hid.symm
      _ ≤ (primeToResidual p D).map D.subtype := embedded_primeToResidual_mono p hKD
  · exact (embedded_primeToResidual_mono p hDH).trans_eq hK.symm

open EmbeddingReduction Chapter1

variable {κ : GroupClass.{u}}
variable {d : Source.Geometry G} {i j : Bool} {H U : Subgroup G}

/-- The replaced placed configuration has the very same normal closure and
prime-to-three residual, and its join is the actual product of K with U. -/
theorem replacement_identifications_of_placed (hG : IsSimpleQTKE κ G)
    (embedding : LocalEmbeddingTheorem κ) (orbits : ComponentOrbitTheorem κ)
    (residual : TwoOrbitResidualTheorem κ)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX)
    (hD : PlacedX d i j (normalClosureIn d.wholeX H ⊔ U) U) :
    let K := normalClosureIn d.wholeX H
    let D := K ⊔ U
    K = normalClosureIn d.wholeX D ∧
      K = (primeToResidual 3 D).map D.subtype ∧
      (K : Set G) * (U : Set G) = (D : Set G) := by
  have hK := (h.normalClosure_branches hG embedding orbits residual P).1
  have hUH : U ≤ H := h.sylow_image ▸ map_subtype_le (h.sylow : Subgroup H)
  have hDH : normalClosureIn d.wholeX H ⊔ U ≤ H :=
    sup_le (normalClosureIn_le_overgroup _ _) hUH
  have hres := embedded_residual_eq_of_intermediate 3 hK le_sup_left hDH
  refine ⟨hres.trans (hD.normalClosure_branches hG embedding orbits residual P).1.symm,
    hres, ?_⟩
  exact (coe_mul_of_right_le_normalizer_left _ _
    (hUH.trans ((normal_subgroupOf_iff_le_normalizer
      (normalClosureIn_le_overgroup d.wholeX H)).mp
        (normalClosureIn_normal d.wholeX H)))).symm

/-- Source application: the residual replacement itself supplies the new
placed configuration, with no additional assumption on that replacement. -/
theorem replacement_identifications (hG : IsSimpleQTKE κ G)
    (embedding : LocalEmbeddingTheorem κ) (orbits : ComponentOrbitTheorem κ)
    (residual : TwoOrbitResidualTheorem κ)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX) :
    let K := normalClosureIn d.wholeX H
    let D := K ⊔ U
    K = normalClosureIn d.wholeX D ∧
      K = (primeToResidual 3 D).map D.subtype ∧
      (K : Set G) * (U : Set G) = (D : Set G) := by
  have hK := (h.normalClosure_branches hG embedding orbits residual P).1
  have hrepl := h.residual_replacement
  dsimp only at hrepl
  rw [← hK] at hrepl
  obtain ⟨hD, hU, _, hcore⟩ := hrepl
  obtain ⟨placed⟩ := h.replacement_configuration hD hU hcore
  exact replacement_identifications_of_placed hG embedding orbits residual h P placed

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary
