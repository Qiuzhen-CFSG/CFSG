module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.Borels
public import CFSG.Quasithin.ChapterF.Section01.SourceFaithfulTriple

/-!
# Genuine F.1.1 and the original faithful triangle

The original Borel factorizations identify B₁B₂S₀ with S₀X, hence identify
the F.1.1 parabolics with the literal K₀S₀X and L₂S₀X. The previously
proved Sylow, normalization, core and characteristic-two results discharge
all six F.1.1 clauses. The source faithful-triple theorem then applies in
the actual completion, preserving its full odd Borel.

Cartan splitting is an explicit intermediate input here, discharged for
all three natural models in the Amalgam consumer. The zero-core hypothesis
is the remaining contradiction branch, not a claimed exclusion of it.
Source: Aschbacher--Smith 11.1.2, printed p.762; F.1.1 and F.1.9,
printed pp.259--262, combined manuscript, 1 March 2004.
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

omit [Finite G] in
private theorem commonBorel_eq_overlap {K₀ L₂ X : Subgroup G}
    (hb : ∀ i, borel (locals K₀ L₂ i) (commonTwo T X) =
      (commonTwo T X ⊓ locals K₀ L₂ i) ⊔ (X ⊓ locals K₀ L₂ i))
    (hx : (X ⊓ K₀) ⊔ (X ⊓ L₂) = X) :
    commonBorel (locals K₀ L₂) (commonTwo T X) = overlap T X := by
  have hi (i : Fin 2) : borel (locals K₀ L₂ i) (commonTwo T X) ≤ overlap T X := by
    rw [hb i]
    exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  apply le_antisymm (sup_le (sup_le (hi 0) (hi 1)) le_sup_left)
  refine sup_le le_sup_right ?_
  apply hx.ge.trans
  apply sup_le
  · exact (show X ⊓ K₀ ≤ borel (locals K₀ L₂ 0) (commonTwo T X) by
      rw [hb 0]; exact le_sup_right).trans (le_sup_left.trans le_sup_left)
  · exact (show X ⊓ L₂ ≤ borel (locals K₀ L₂ 1) (commonTwo T X) by
      rw [hb 1]; exact le_sup_right).trans (le_sup_right.trans le_sup_left)

/-- All six genuine F.1.1 clauses, with the original overlap and parabolics.
The Amalgam consumer discharges the split premise for all three source models. -/
theorem original_hypothesis_of_cartan_split (hu : f.IsInnerUnique)
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
    (hsplit : (X ⊓ f.Li 0) ⊔ (X ⊓ f.Li 1) = X ∧
      Disjoint (X ⊓ f.Li 0) (X ⊓ f.Li 1))
    (hz : pCore 2 (completion T X K₀ (f.Li 1)) = ⊥) :
    HypothesisF11 (locals K₀ (f.Li 1)) (commonTwo T X) ∧
      commonBorel (locals K₀ (f.Li 1)) (commonTwo T X) = overlap T X ∧
      (∀ i, parabolic (locals K₀ (f.Li 1)) (commonTwo T X) i =
        endpoint T X (locals K₀ (f.Li 1) i)) ∧
      generated (locals K₀ (f.Li 1)) (commonTwo T X) = completion T X K₀ (f.Li 1) := by
  have hb := original_borels_of_cartan_split D S f hu hm₁ hm₂ hfour hX hK hLK
    hK₀ hK₀K hTK₀ hm₀ hk hp hsplit
  obtain ⟨_,h₁,h₀⟩ := first_triangle_cartan_intersections D S f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hx : (X ⊓ K₀) ⊔ (X ⊓ f.Li 1) = X := by rw [←h₀,h₁]; exact hsplit.1
  have hcb := commonBorel_eq_overlap hb hx
  have hep (i : Fin 2) : parabolic (locals K₀ (f.Li 1)) (commonTwo T X) i =
      endpoint T X (locals K₀ (f.Li 1) i) := by
    rw [parabolic_eq_sup_commonBorel,hcb]
    rfl
  have hgen : generated (locals K₀ (f.Li 1)) (commonTwo T X) =
      completion T X K₀ (f.Li 1) := by
    rw [←parabolics_generate,hep 0,hep 1]
    rfl
  have hn (i : Fin 2) : overlap T X ≤ normalizer (locals K₀ (f.Li 1) i : Set G) := by
    apply sup_le
    · apply (commonTwo_le_sylow X).trans
      fin_cases i
      · exact hTK₀
      · exact f.sylow_normalizes_Li 1
    · fin_cases i
      · exact cartan_normalizes_other_residual D S f hu hm₁ hX hK hLK hK₀ hK₀K hk
      · exact cartan_normalizes_flag_residual D S f hu hX 1
  refine ⟨?_,hcb,hep,hgen⟩
  refine ⟨inferInstance,isPGroup_pCoreIn 2 _,fun i => le_sup_left.trans (hn i),
    original_pair_sylow D S f hu hm₁ hX hK hLK hK₀K.le hTK₀ hk,?_,?_,hgen ▸ hz,?_⟩
  · intro i
    apply IsRankOneModel.linear 2 (by decide)
    fin_cases i
    · exact hm₀
    · simpa [locals,hfour] using hm₂
  · intro i
    apply le_trans ?_ (hn i)
    rw [hb (other i)]
    exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  · intro i
    rw [hep i]
    exact original_endpoints_characteristic_two D S f hu hX hK hK₀K.le hTK₀ i

omit [Finite G] in
/-- Faithfulness concerns the full original Borel in the actual completion. -/
theorem original_faithful_triple {K₀ L₂ X : Subgroup G}
    (h : HypothesisF11 (locals K₀ L₂) (commonTwo T X))
    (hb : commonBorel (locals K₀ L₂) (commonTwo T X) = overlap T X)
    (hp : ∀ i, parabolic (locals K₀ L₂) (commonTwo T X) i =
      endpoint T X (locals K₀ L₂ i))
    (hg : generated (locals K₀ L₂) (commonTwo T X) = completion T X K₀ L₂) :
    LocallyRankOneTriple
      (fun i => (endpoint T X (locals K₀ L₂ i)).subgroupOf (completion T X K₀ L₂))
      ((overlap T X).subgroupOf (completion T X K₀ L₂)) := by
  rw [←hg]
  simpa only [hp,hb] using h.generatedLocallyRankOneTriple

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
