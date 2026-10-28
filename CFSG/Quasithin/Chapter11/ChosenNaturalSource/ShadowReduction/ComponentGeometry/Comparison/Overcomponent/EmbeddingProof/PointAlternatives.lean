module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.SporadicPoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.OddTernaryComparison
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.PrimeExtensions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.AlternatingSeven

/-!
# Nonquasisimple point quotients in the complete containing catalogue

On the original chosen flag, strict containment first forces the original
field to have four elements. We then exhaust every containing row from
11.1.1: the alternating and rank-one exclusions, the complete signed
ternary comparison, the sporadic order and rank arguments, and the
quasisimplicity of the maximal containing quotient remove all but the
literal elementary-plane-by-SL₂(5) pair and the J₄ row.

This is a derived reduction of the full catalogue, including the central
covers and odd extensions. The J₄ row, quasisimple point comparisons and
final component equality remain with qt-d-1222-shadow-component-comparison.
The earlier source hypotheses retain their discharge by
qt-d-1222-shadow-components.
Source: Aschbacher--Smith 11.4.2, printed p.776, using A.3.6 and A.3.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The complete containing catalogue for a nonquasisimple point quotient
leaves the literal quintic elementary-by-SL₂ proper pair or the original
J₄ row. Every other source row is excluded, including both odd extensions,
all covering rows and both signed ternary branches. -/
theorem ofFlag_nonquasisimple_proper_pair_or_jankoFour
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧
      ((HasExtension ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
          (ElementaryModel 5 2) (fun Q _ => IsSL Q 2 5) ∧
        (ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 5 ∨ IsSL (J ⧸ pCore 2 J) 3 5) ∧
        ProperEmbedding (ofFlag S f X z H).Kz J) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) := by
  obtain ⟨hd,hrows⟩ := ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ.1 hlt
  refine ⟨hd,?_⟩
  have hrank := ofFlag_rankOne_exclusions S f X z H h hne hlinear h1132 e hJ.1 hlt
  let := ofFlag_proper_overcomponent_quasisimple S f X z H h hne hlinear h1132 e hcent hJ hlt
  cases hrows with
  | alternating hm =>
    exact (ofFlag_not_alternating_seven_overcomponent S f X z H h hne
      hlinear h1132 e hJ.1 hlt (.inl hm)).elim
  | alternatingCover hm =>
    exact (ofFlag_not_alternating_seven_overcomponent S f X z H h hne
      hlinear h1132 e hJ.1 hlt (.inr hm)).elim
  | primeLinear p hp hm =>
    have ho : Odd p := hp.1.odd_of_ne_two (by have := hp.2.1; omega)
    exact ((hrank.2.2 p hp.1 ho).1 hm).elim
  | linearTwentyFive hm => exact ((hrank.2.2 5 (by decide) (by decide)).2 hm).elim
  | three u hm =>
    obtain ⟨_,hu,hsmall,hpair⟩ := ofFlag_properEmbedding_of_odd_ternary S f X z H h hne
      hlinear h1132 e hcent hJ hlt (by decide : Nat.Prime 5) (by decide : Odd 5) u hm
    subst u
    exact .inl ⟨hsmall,hm,hpair⟩
  | m22 hm => exact (hn (point_quasisimple_in_small_sporadic h hJ.1 hlt (.inr (.inr (.inl hm))))).elim
  | m22Cover hm => exact (hn (point_quasisimple_in_small_sporadic h hJ.1 hlt (.inr (.inr (.inr (.inl hm)))))).elim
  | m23 hm => exact (hn (point_quasisimple_in_small_sporadic h hJ.1 hlt (.inr (.inr (.inr (.inr hm)))))).elim
  | j1 hm => exact (hn (point_quasisimple_in_small_sporadic h hJ.1 hlt (.inl hm))).elim
  | j2 hm => exact (hn (point_quasisimple_in_small_sporadic h hJ.1 hlt (.inr (.inl hm)))).elim
  | j4 hm => exact .inr hm
  | hs hm => exact (hn (point_quasisimple_in_higmanSims_or_rudvalis h hJ.1 hlt (.inl hm))).elim
  | ru hm => exact (hn (point_quasisimple_in_higmanSims_or_rudvalis h hJ.1 hlt (.inr hm))).elim
  | nilpotentExtension hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension
      (pCore_quotient_pCore_eq_bot 2) _ (by decide : Odd 5) hm).elim
  | elementaryExtension p hp hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension
      (pCore_quotient_pCore_eq_bot 2) _
      (hp.1.odd_of_ne_two (by have := hp.2.1; omega)) hm).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
