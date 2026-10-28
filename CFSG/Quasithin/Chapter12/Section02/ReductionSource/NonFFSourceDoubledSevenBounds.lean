module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenMixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenGeneration
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenMixedGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledAssembly


/-!
# The improved A₇ bounds with original odd-normalizer control

The original local centralizer image is either controlled by the already
proved odd-image or two-group arguments, or contains an involution and a
cubic. The full-pair geometry excludes the last possibility below corank
six. Taking the literal minimum gives r ≥ 6 on the original source orbit.
Together with its full automizer rank three and the earlier w ≤ 2 theorem,
this constructs DoubledSevenBounds and applies its contradiction to the
same chosen module.

All representation, centralizer-image and numerical premises have been
discharged. The original 4.4.3 odd-normalizer control remains explicit in
these theorems and is still required for the unconditional A₇ source row.
No individual plane-fixer equality or generic E.6.3 callback is used.
Source: Aschbacher--Smith 7.3.4, 7.4.1 and 7.5.5, pp.699--701;
E.6.11 and E.6.27, pp.249,257; original 4.4.3, p.619.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
open Representation.AlternatingSevenConjugatePair.Model
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
/-- The corrected full-pair geometry closes the mixed centralizer branch
on the original orbit, retaining only original odd-normalizer control. -/
theorem sourceOrbit_seven_small_centralizer_of_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ normalizer (L : Set G))
    {U : Subgroup G} (hUW : U ≤ D.sourceOrbit) (hc : subgroupCorank D.sourceOrbit U < 6) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  by_contra he
  obtain ⟨t,s,ht,hs,ht2,hs3⟩ := D.sourceOrbit_seven_small_escape_mixed
    h hd σ hσ hmodel hodd hUW hc he
  obtain ⟨_,_,_,P,E,_,_⟩ := D.sourceOrbit_seven_H8_pair h hd σ hσ hmodel
  let I := inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ centralizer (U : Set G))
  have h6 := doubledSeven_mixed_fixedCodim P (I.map E.groupEquiv.toMonoidHom)
    (E.groupEquiv t) (E.groupEquiv s) (mem_map_of_mem _ ht) (mem_map_of_mem _ hs)
    ((orderOf_injective E.groupEquiv.toMonoidHom E.groupEquiv.injective t).trans ht2)
    ((orderOf_injective E.groupEquiv.toMonoidHom E.groupEquiv.injective s).trans hs3)
  have heq := fixedCodim_map_equivariant (automizerRepresentation D.sourceOrbit) P.representation
    E.groupEquiv.toMonoidHom E.linearEquiv E.intertwines I
  have hU : U ≠ ⊥ := by
    intro hb
    rw [hb,Section06.corank_bot,D.sourceOrbit_seven_dimension h hd σ hmodel] at hc
    omega
  have hbound : fixedCodim (automizerRepresentation D.sourceOrbit) I ≤
      subgroupCorank D.sourceOrbit U := by
    rw [fixedCodim_inducedAutomizer D.sourceOrbit _
      ((D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).localCentralizer_le_normalizer hU hUW)]
    exact Section06.subgroupCorank_antitone (le_inf hUW (le_centralizer_iff.mpr inf_le_right))
  omega

/-- The improved source bound r ≥ 6, with the genuine odd-normalizer
premise still explicit and every centralizer-image branch discharged. -/
theorem sourceOrbit_seven_six_le_globalR_of_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ normalizer (L : Set G))
    : 6 ≤ globalR D.sourceOrbit := by
  unfold globalR
  refine le_iInf fun U => le_iInf fun hU => ?_
  have hb : 6 ≤ subgroupCorank D.sourceOrbit U := by
    by_contra hn
    apply hU.2
    rw [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
    exact D.sourceOrbit_seven_small_centralizer_of_odd_control h hd σ hσ hmodel hodd hU.1
      (by omega)
  exact_mod_cast hb

/-- All three numerical obligations on the original chosen orbit, conditional
only on source 4.4.3's odd-normalizer control. -/
theorem sourceOrbit_seven_bounds_of_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    DoubledSevenBounds D.sourceOrbit T := by
  exact ⟨(D.sourceOrbit_seven_automizer_rank_eq h hd σ hσ hmodel).le,
    D.sourceOrbit_seven_globalW_le_two_of_odd_control h hd hmany σ hσ hmodel hodd,
    D.sourceOrbit_seven_six_le_globalR_of_odd_control h hd σ hσ hmodel hodd⟩

/-- The literal chosen-module application of the improved A₇ bounds.
The outstanding original odd-normalizer theorem must discharge `hodd`
before this conditional implication completes the source exclusion. -/
theorem sourceOrbit_seven_false_of_odd_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) : False :=
  DoubledSevenBounds.false D.sourceOrbit T
    (D.sourceOrbit_seven_bounds_of_odd_control h hd σ hσ hmodel hodd hmany)
    D.sourceOrbit_weakClosure_setup (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
