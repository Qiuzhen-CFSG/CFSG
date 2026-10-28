module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RadicalImages
public import Theory.SpecificGroups.HigherLinear.RadicalParabolics
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# The actual type-A normalizer flag in C.2.7

Use the component isomorphism supplied by the type-A classification row.
The original R*∩K* is radical by the preceding source transport, so its
normalizer is the full stabilizer of a genuine nonempty proper partial flag.
No flag or normalizer placement is an input. The trivial intersection and
promotion from this normalizer to M_K* remain separate source steps.

Source: Aschbacher (1981), Lemma 8.2(7); Aschbacher–Smith C.2.7, pp.146–147.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem star_linear_normalizer_flag
    (h : Input κ H R M K) [(K.subgroupOf H).Normal]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (e : starImage K R K ≃* SL(n,F))
    (hne : (starImage K R R).subgroupOf (starImage K R K) ≠ ⊥) :
    ∃ (k : ℕ) (W : Fin k → Submodule F (Fin n → F)),
      0 < k ∧ k < n ∧ StrictMono W ∧
      (∀ i, W i ≠ ⊥ ∧ W i ≠ ⊤) ∧
      (normalizer ((starImage K R R).subgroupOf (starImage K R K) :
        Set (starImage K R K))).map e.toMonoidHom =
        ⨅ i, Matrix.HigherLinear.parabolicSL (W i) := by
  have hr := (star_intersection_radical_of_normal_input h hne).map_equiv e
  obtain ⟨k,W,hk,hnk,hm,hp,he⟩ :=
    Matrix.HigherLinear.radical_normalizer_eq_partialFlag hn _ hr
  refine ⟨k,W,hk,hnk,hm,hp,?_⟩
  rwa [map_equiv_normalizer_eq]

end CFSG.Quasithin.ChapterC.C27Source
