module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.Endpoints

/-!
# The original triangle setup and the nonzero-core branch

Select K₀ with the existing canonical other-residual theorem. Its original
Cartan action, full Sylow intersections and characteristic-two endpoints are
proved in the imported setup modules. If the original completion has nonzero
two-core, that embedded core is an actual common normal Q in T. Apply the
existing common-normal theorem to construct the literal I = K₀ ∨ L₂.

The zero-core branch remains explicit. In particular these theorems do not
claim the marked DGS chief-section contradiction or source 11.1.2 in full.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.762--763.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The nonzero-core branch supplies Q and applies the existing literal
third-vertex construction. The zero-core contradiction is still outstanding. -/
theorem triangle_join_component_of_nonzero_completion_core
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hcore : pCore 2 (completion T X K₀ (f.Li 1)) ≠ ⊥) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
      K₀ ≤ normalizer (Q : Set G) ∧ f.Li 1 ≤ normalizer (Q : Set G) ∧
      Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
      (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
      (solvableResidual ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
        ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 ∧
      (pResidual 2 ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
        ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 := by
  obtain ⟨Q,hQ,hQT,hTQ,hKQ,hLQ⟩ := common_normal_of_completion_core_ne_bot c hX hTK₀
    (f.sylow_normalizes_Li 1) hcore
  exact ⟨Q,hQ,hQT,hTQ,hKQ,hLQ,
    triangle_join_component_of_common_normal_projective D S f hu hm₁ hm₂ hfour hfix hX
      hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove hQ hQT hTQ hKQ hLQ⟩

/-- Select the canonical original K₀ and discharge the full nonzero-core
branch. In the remaining branch both the full completion and the literal
F.1.1-generated group have zero core; the marked DGS contradiction remains. -/
theorem first_triangle_original_core_alternative
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G)) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ < K ∧ K₀ ≠ f.Li 0 ∧
      (∀ J : Subgroup G, J ∈ Chapter1.L G T → J ≤ K → J ≠ K → J ≠ f.Li 0 → J = K₀) ∧
      (T : Subgroup G) ≤ normalizer (K₀ : Set G) ∧ K₀ ∈ Chapter1.He G ∧
      f.Li 0 ⊔ K₀ = K ∧ ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4 ∧
      X ≤ normalizer (K₀ : Set G) ∧
      (∀ i, ∃ P : Sylow 2 (locals K₀ (f.Li 1) i),
        (P : Subgroup (locals K₀ (f.Li 1) i)).map (locals K₀ (f.Li 1) i).subtype =
          commonTwo T X ⊓ locals K₀ (f.Li 1) i) ∧
      (∀ i, generalizedFitting (endpoint T X (locals K₀ (f.Li 1) i)) =
        pCore 2 (endpoint T X (locals K₀ (f.Li 1) i))) ∧
      ((pCore 2 (completion T X K₀ (f.Li 1)) = ⊥ ∧
          pCore 2 (ChapterF.Source.generated (locals K₀ (f.Li 1)) (commonTwo T X)) = ⊥) ∨
        ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ (T : Subgroup G) ∧
          (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
          K₀ ≤ normalizer (Q : Set G) ∧ f.Li 1 ≤ normalizer (Q : Set G) ∧
          Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
          (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
          (solvableResidual ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
            ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 ∧
          (pResidual 2 ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
            ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1) := by
  obtain ⟨K₀,h₀,h₀K,hneK,hneL,hunique,hTK₀,hHe,hgen,hm₀⟩ :=
    first_triangle_other_residual D S f hm₁ hK hLK hk
  have hlt : K₀ < K := lt_of_le_of_ne h₀K hneK
  refine ⟨K₀,h₀,hlt,hneL,hunique,hTK₀,hHe,hgen,hm₀,
    cartan_normalizes_other_residual D S f hu hm₁ hX hK hLK h₀ hlt hk,
    original_pair_sylow D S f hu hm₁ hX hK hLK h₀K hTK₀ hk,
    original_endpoints_characteristic_two D S f hu hX hK h₀K hTK₀,?_⟩
  by_cases hz : pCore 2 (completion T X K₀ (f.Li 1)) = ⊥
  · exact Or.inl ⟨hz,
      generated_core_eq_bot_of_completion_core D S f hu hm₁ hX hK hLK h₀ hlt hk hz⟩
  · exact Or.inr (triangle_join_component_of_nonzero_completion_core D S f hu hm₁ hm₂
      hfour hfix hX hK hLK h₀ hlt hTK₀ hk hp hcard hmove hz)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
