module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.CoreAction

/-!
# The common normal subgroup in the original field-four triangle

The full marked reduced DGS catalogue is the only new earlier-source input.
Its original field-four comparison contradicts the chief-section bound on
the actual containing component's core. Consequently the original completion
has nonzero two-core. Its embedded core is the required subgroup Q of T,
normalized by T, the same canonical K₀, and the original L₂.

The final theorem applies the existing common-normal component theorem to
this Q and constructs the literal I = K₀ ∨ L₂ with both residual identities.
The original point and cubic-action premises of that component consumer are
retained; no marking, splitting, chief-profile or zero-core callback is added.

Source: Aschbacher--Smith 11.1.2, printed pp.762--763. The original K-core
chief-section proof replacing the printed G₂ long-root comparison is in
CoreAction. The independent DGS source input remains with its source owner;
this does not claim the unconditional entirety of 11.1.2.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Exclude zero core for the original completion and the same selected K₀.
The source DGS theorem is used only after genuine F.1.1 has been proved. -/
theorem original_completion_core_ne_bot_of_reduced_catalogue
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hm₀ : ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hdgs : HypothesisF11 ![K₀,f.Li 1] (commonTwo T X) →
      Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
        K₀ (f.Li 1) (commonTwo T X)) :
    pCore 2 (completion T X K₀ (f.Li 1)) ≠ ⊥ := by
  intro hz
  have hh := (original_hypothesis D S f hu hm₁ hm₂ hfour hX hK hLK
    hK₀ hK₀K hTK₀ hm₀ hk hp hz).1
  have he : locals K₀ (f.Li 1) = ![K₀,f.Li 1] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at hh
  obtain ⟨_,F,_,_,_,hF,b,⟨e⟩⟩ := original_zeroCore_remainder D S f hu hm₁ hm₂
    hfour hX hK hLK hK₀ hK₀K hTK₀ hm₀ hk hp hz (hdgs hh)
  exact no_original_g2_comparison D S f hu hm₁ hX hK hLK hk F hF b e

/-- Construct Q for the canonical original K₀, without any chief-action or
nonzero-core premise and without the extra cubic data needed for the join. -/
theorem first_triangle_common_normal_of_reduced_catalogue
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hdgs : ∀ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T → K₀ < K →
      HypothesisF11 ![K₀,f.Li 1] (commonTwo T X) →
      Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
        K₀ (f.Li 1) (commonTwo T X)) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ < K ∧ K₀ ≠ f.Li 0 ∧
      (∀ J : Subgroup G, J ∈ Chapter1.L G T → J ≤ K → J ≠ K → J ≠ f.Li 0 → J = K₀) ∧
      (T : Subgroup G) ≤ normalizer (K₀ : Set G) ∧ K₀ ∈ Chapter1.He G ∧
      f.Li 0 ⊔ K₀ = K ∧ ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4 ∧
      ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ (T : Subgroup G) ∧
        (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
        K₀ ≤ normalizer (Q : Set G) ∧ f.Li 1 ≤ normalizer (Q : Set G) := by
  obtain ⟨K₀,h₀,h₀K,hneK,hneL,hunique,hTK₀,hHe,hgen,hm₀⟩ :=
    first_triangle_other_residual D S f hm₁ hK hLK hk
  have hlt : K₀ < K := lt_of_le_of_ne h₀K hneK
  have hz := original_completion_core_ne_bot_of_reduced_catalogue D S f hu hm₁ hm₂
    hfour hX hK hLK h₀ hlt hTK₀ hm₀ hk hp (hdgs K₀ h₀ hlt)
  exact ⟨K₀,h₀,hlt,hneL,hunique,hTK₀,hHe,hgen,hm₀,
    common_normal_of_completion_core_ne_bot c hX hTK₀ (f.sylow_normalizes_Li 1) hz⟩

/-- Apply the original component consumer to the constructed common Q.
All five common-normal premises are discharged for the same canonical K₀,
and the third vertex is literally K₀ ∨ L₂. -/
theorem first_triangle_join_component_of_reduced_catalogue
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
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hdgs : ∀ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T → K₀ < K →
      HypothesisF11 ![K₀,f.Li 1] (commonTwo T X) →
      Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives
        K₀ (f.Li 1) (commonTwo T X)) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ < K ∧ K₀ ≠ f.Li 0 ∧
      (∀ J : Subgroup G, J ∈ Chapter1.L G T → J ≤ K → J ≠ K → J ≠ f.Li 0 → J = K₀) ∧
      (T : Subgroup G) ≤ normalizer (K₀ : Set G) ∧ K₀ ∈ Chapter1.He G ∧
      f.Li 0 ⊔ K₀ = K ∧ ClassicalGroup.IsPSL (K₀ ⧸ pCore 2 K₀) 2 4 ∧
      ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ (T : Subgroup G) ∧
          (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
          K₀ ≤ normalizer (Q : Set G) ∧ f.Li 1 ≤ normalizer (Q : Set G) ∧
          Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
          (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
          (solvableResidual ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
            ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 ∧
          (pResidual 2 ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
            ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 := by
  obtain ⟨K₀,h₀,hlt,hne,hu₀,hT,hHe,hgen,hm₀,Q,hQ,hQT,hTQ,hKQ,hLQ⟩ :=
    first_triangle_common_normal_of_reduced_catalogue D S f hu hm₁ hm₂ hfour hX hK hLK hk hp hdgs
  exact ⟨K₀,h₀,hlt,hne,hu₀,hT,hHe,hgen,hm₀,Q,hQ,hQT,hTQ,hKQ,hLQ,
    triangle_join_component_of_common_normal_projective D S f hu hm₁ hm₂ hfour hfix hX
      hK hLK h₀ hlt hT hk hp hcard hmove hQ hQT hTQ hKQ hLQ⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
