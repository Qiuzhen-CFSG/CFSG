module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Paired
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.KnownSimple
/-!
# The original E.6.27 consumer with one numerical source branch

The small minimal parabolics are contained by the proved SQTK E.6.26.
Every large model has a reflected Cartan alternative except the actual
exchanged odd-prime PSL2 family. Its genuine degree-one E-generation
implication suffices for the original centralizer bound. This earlier
branch is retained explicitly while its source owner completes it;
there is no E.6.26 or 4.4.13 callback.
Source: Aschbacher–Smith E.6.27, printed p.257.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
open ChapterB ParabolicCartan ParabolicCartan.MarkedModels
universe u
variable {G : Type u} [Group G] [Finite G]
theorem centralizer_le_of_paired_odd_generation
    (hpaired : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK KnownSimple.IsKnownSimple H → ∀ (T : Sylow 2 H)
      (hP : IsMinimalParabolicOver T ⊤), ¬Group.IsSolvable H →
      ∀ K : Subgroup H, K.IsCComponent → K ⊔ (T : Subgroup H) = ⊤ → ¬K.Normal →
      ∀ p : ℕ, p.Prime → Odd p → 7 ≤ p →
        ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax T hP) K) 2 p →
        IsEGenerated 1 H)
    {T : Sylow 2 G} {M V U : Subgroup G}
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hU : U ≠ ⊥) (hUV : U ≤ V)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (j : ℕ∞) < globalR V)
    (hn : nPrime (inducedAutomizer V (M ⊓ centralizer (U : Set G))) ≤ j)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤ M ⊓ centralizer (V : Set G))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ M ⊓ centralizer (V : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ M) :
    centralizer (U : Set G) ≤ M := by
  obtain ⟨R,hN,hsmall⟩ := SylowThompson.exists_preparation_knownSimple h hU hUV hj1 hj hJ
  apply centralizer_le_of_parabolic_upper_bounds h hU hUV j hn hodd R hN hsmall
  intro S hS P hP hbig hescape
  rcases Inverted.source_residual_alternative_or_paired_odd h hU hUV hj1 hj hJ
    R S hS P hP hbig hescape with ho|ha
  · obtain ⟨K,hK,_,hgen,hnorm,p,hp,hop,h7,hm⟩ := ho
    have hs : ¬Group.IsSolvable P := by
      intro hs
      let := hs
      exact (Nat.not_le_of_gt (lt_of_le_of_lt hj1 hbig)) generationParameter_le_one_of_solvable
    have hgp := hpaired P (residual_sqtk h hU hUV P) (parabolicSylow S P hP)
      (minimalParabolic_subtype (residualSylow S) P hP) hs K hK hgen hnorm p hp hop h7 hm
    exact ((Nat.not_le_of_gt (lt_of_le_of_lt hj1 hbig))
      (generationParameter_le (by decide) hgp)).elim
  · obtain ⟨f,_,hb,ha⟩ := ha
    exact ⟨f,hb,ha⟩
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
