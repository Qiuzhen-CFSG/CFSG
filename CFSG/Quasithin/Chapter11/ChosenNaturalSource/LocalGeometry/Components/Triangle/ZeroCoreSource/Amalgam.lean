module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.Hypothesis
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.G2Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearCartanPlacement

/-!
# The canonical original triangle and its faithful zero-core branch

The original Cartan splits over the actual two residuals in each of the
SL₃, Sp₄ and G₂ natural models. This discharges the intermediate splitting
premise in the F.1.1 construction. Select K₀ with the existing canonical
other-residual theorem, preserving its uniqueness and the original quotient
markings. When O₂(H) is trivial, the literal pair ![K₀,L₂] satisfies genuine
F.1.1; its full Borel is S₀X and its actual parabolics form a faithful triple
in H. These are the original inputs for the independent broad reduced DGS
alternatives, with no independent replacement of the overlap or completion.

The nonzero-core branch constructs the actual common normal Q and applies
the existing I = K₀ ∨ L₂ component/residual consumer. The faithful branch is
still present: the marked original-to-reduced chief-section comparison must
exclude it before this becomes the common-normal conclusion of 11.1.2.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.762--763; F.1.1 and F.1.9, printed pp.259--262.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
open ChapterF.Source

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The original Cartan splits over the two original residuals in all three models. -/
theorem original_cartan_split {X : Subgroup G} (hX : IsCartan T L X) :
    (X ⊓ f.Li 0) ⊔ (X ⊓ f.Li 1) = X ∧ Disjoint (X ⊓ f.Li 0) (X ⊓ f.Li 1) := by
  cases c with
  | sl3 m => exact linear_cartan_split D S m hX f
  | sp4 m => exact sp4_cartan_split D S m f hX
  | g2 m => exact G2Cartan.cartan_split S m hX f

/-- The original zero-core configuration satisfies genuine F.1.1, without
a cross-Borel, Cartan-splitting or characteristic-two premise. -/
theorem original_hypothesis (hu : f.IsInnerUnique)
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
    (hz : pCore 2 (completion T X K₀ (f.Li 1)) = ⊥) :
    HypothesisF11 (locals K₀ (f.Li 1)) (commonTwo T X) ∧
      commonBorel (locals K₀ (f.Li 1)) (commonTwo T X) = overlap T X ∧
      (∀ i, parabolic (locals K₀ (f.Li 1)) (commonTwo T X) i =
        endpoint T X (locals K₀ (f.Li 1) i)) ∧
      generated (locals K₀ (f.Li 1)) (commonTwo T X) = completion T X K₀ (f.Li 1) :=
  original_hypothesis_of_cartan_split D S f hu hm₁ hm₂ hfour hX hK hLK hK₀ hK₀K
    hTK₀ hm₀ hk hp (original_cartan_split D S f hX) hz

omit [Finite G] in
private theorem locals_eq_pair (K₀ L₂ : Subgroup G) : locals K₀ L₂ = ![K₀,L₂] := by
  funext i
  fin_cases i <;> rfl

/-- Select the same canonical K₀. The zero-core branch is now an actual
faithful full source pair, literally matching the broad reduced-DGS input;
the nonzero-core branch constructs Q and applies the literal join consumer.
Excluding the faithful branch by the marked chief sections remains necessary. -/
theorem first_triangle_faithful_or_common_normal
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
      ((pCore 2 (completion T X K₀ (f.Li 1)) = ⊥ ∧
          HypothesisF11 ![K₀,f.Li 1] (commonTwo T X) ∧
          commonBorel ![K₀,f.Li 1] (commonTwo T X) = overlap T X ∧
          (∀ i, parabolic ![K₀,f.Li 1] (commonTwo T X) i =
            endpoint T X (![K₀,f.Li 1] i)) ∧
          generated ![K₀,f.Li 1] (commonTwo T X) = completion T X K₀ (f.Li 1) ∧
          LocallyRankOneTriple
            (fun i => (endpoint T X (![K₀,f.Li 1] i)).subgroupOf (completion T X K₀ (f.Li 1)))
            ((overlap T X).subgroupOf (completion T X K₀ (f.Li 1)))) ∨
        ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ (T : Subgroup G) ∧
          (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
          K₀ ≤ normalizer (Q : Set G) ∧ f.Li 1 ≤ normalizer (Q : Set G) ∧
          Source.NormalComponentIn ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) (K₀ ⊔ f.Li 1) ∧
          (K₀ ⊔ f.Li 1) ∈ Chapter1.L G T ∧ (K₀ ⊔ f.Li 1) ∈ Chapter1.He G ∧
          (solvableResidual ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
            ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1 ∧
          (pResidual 2 ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G) : Subgroup G)).map
            ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).subtype = K₀ ⊔ f.Li 1) := by
  obtain ⟨K₀,h₀,hlt,hne,hu₀,hT,hHe,hgen,hm₀,_hX,_hSyl,_hCT,hcases⟩ :=
    first_triangle_original_core_alternative D S f hu hm₁ hm₂ hfour hfix hX hK hLK hk hp hcard hmove
  refine ⟨K₀,h₀,hlt,hne,hu₀,hT,hHe,hgen,hm₀,?_⟩
  rcases hcases with ⟨hz,_⟩ | hQ
  · obtain ⟨h,hb,hp',hg⟩ := original_hypothesis D S f hu hm₁ hm₂ hfour hX hK hLK
      h₀ hlt hT hm₀ hk hp hz
    have ht := original_faithful_triple h hb hp' hg
    rw [locals_eq_pair] at h hb hp' hg ht
    exact Or.inl ⟨hz,h,hb,hp',hg,ht⟩
  · exact Or.inr hQ

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
