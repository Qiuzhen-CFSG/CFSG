module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree.Fixers
public import Theory.GroupAction.ModelConjugation

/-!
# Lifting the intrinsic linear-three fixer calculation to ambient actors

Identify K with the actual SL₃ or PSL₃ carrier, and let the two-group T
normalize K and stabilize the specified Sylow S in that model. Assume the
embedded S lies in T. Conjugation then has an image containing Inn(S),
so the intrinsic fixer theorem applies to that image. Its full preimage
is the embedded S joined with C_T(K), by the image-preimage identity.
The kernel is computed from actual conjugation, with only relative normality.

This does not identify a star-image component with its source lift, nor
discard the centralizer when lifting out of Aut(K).
Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).
-/

public section

open Subgroup Theory.GroupAction.ModelConjugation
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree

private theorem inner_le_conjugation_range {G D : Type*} [Group G] [Group D]
    (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G)) (e : K ≃* D)
    (S : Sylow 2 D) (hST : (S : Subgroup D).map (K.subtype.comp e.symm.toMonoidHom) ≤ T) :
    innerSylow S ≤ (action T K hTK e).range := by
  rw [innerSylow, ← inner_image T K hTK e S hST]
  rintro α ⟨t,_,rfl⟩
  exact ⟨t,rfl⟩

private theorem conjugation_fixer_preimage {G D : Type*} [Group G] [Group D]
    (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G)) (e : K ≃* D)
    (S : Sylow 2 D) (hST : (S : Subgroup D).map (K.subtype.comp e.symm.toMonoidHom) ≤ T)
    (hfix : ∀ α ∈ (action T K hTK e).range,
      FixesResidualTorus (intrinsicResidual S) α ↔ α ∈ innerSylow S)
    (t : T) : FixesResidualTorus (intrinsicResidual S) (action T K hTK e t) ↔
      (t : G) ∈ (S : Subgroup D).map (K.subtype.comp e.symm.toMonoidHom) ⊔
        (T ⊓ centralizer (K : Set G)) := by
  let U := (S : Subgroup D).map (K.subtype.comp e.symm.toMonoidHom)
  let ρ := action T K hTK e
  have hP : (U.subgroupOf T).map ρ = innerSylow S := inner_image T K hTK e S hST
  rw [hfix _ ⟨t,rfl⟩, ← hP]
  change t ∈ ((U.subgroupOf T).map ρ).comap ρ ↔ _
  rw [comap_map_eq]
  have hm : (U.subgroupOf T ⊔ ρ.ker).map T.subtype =
      U ⊔ (T ⊓ centralizer (K : Set G)) := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hST, action_ker_map]
  rw [← hm]
  exact (mem_map_iff_mem T.subtype_injective).symm

variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]

/-- The ambient SL₃ fixer formula retains the entire kernel C_T(K). -/
theorem special_conjugation_fixes_iff {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (hcover : standard F = ⊤) (T K : Subgroup G) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (e : K ≃* SL(3,F)) (S : Sylow 2 SL(3,F))
    (hstable : StabilizesSylow (action T K hTK e).range S)
    (hST : (S : Subgroup SL(3,F)).map (K.subtype.comp e.symm.toMonoidHom) ≤ T)
    (t : T) : FixesResidualTorus (intrinsicResidual S) (action T K hTK e t) ↔
      (t : G) ∈ (S : Subgroup SL(3,F)).map (K.subtype.comp e.symm.toMonoidHom) ⊔
        (T ⊓ centralizer (K : Set G)) := by
  apply conjugation_fixer_preimage T K hTK e S hST _ t
  intro α hα
  exact special_fixesResidualTorus_iff hF hn hn2 hn6 hcover S _
    (hT.of_surjective (action T K hTK e).rangeRestrict
      (action T K hTK e).rangeRestrict_surjective)
    hstable (inner_le_conjugation_range T K hTK e S hST) hα

/-- The ambient PSL₃ formula uses the actual model equivalence and the same kernel. -/
theorem projective_conjugation_fixes_iff {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (hcover : standard F = ⊤) (T K : Subgroup G) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (e : K ≃* PSL(3,F)) (S : Sylow 2 PSL(3,F))
    (hstable : StabilizesSylow (action T K hTK e).range S)
    (hST : (S : Subgroup PSL(3,F)).map (K.subtype.comp e.symm.toMonoidHom) ≤ T)
    (t : T) : FixesResidualTorus (intrinsicResidual S) (action T K hTK e t) ↔
      (t : G) ∈ (S : Subgroup PSL(3,F)).map (K.subtype.comp e.symm.toMonoidHom) ⊔
        (T ⊓ centralizer (K : Set G)) := by
  apply conjugation_fixer_preimage T K hTK e S hST _ t
  intro α hα
  exact projective_fixesResidualTorus_iff hF hn hn2 hn6 hcover S _
    (hT.of_surjective (action T K hTK e).rangeRestrict
      (action T K hTK e).rangeRestrict_surjective)
    hstable (inner_le_conjugation_range T K hTK e S hST) hα

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
