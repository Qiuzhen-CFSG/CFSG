module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.Automizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneOddCodimension

/-!
# The odd-element alternative in the original M22 escaping-space argument

Both original simple M22 markings have odd-prime displacement at least six
on the full automizer. Thus an actual local centralizer fixing a subspace of
rank greater than four has no nontrivial odd Cartan witness. This discharges
the odd-element alternative of 8.1.2; the near-offender alternative and the
distinguished-vector containment still require their own arguments.

Source: Aschbacher--Smith Table7.2.1, H.15.7 and 8.1.2, printed
pp.698,402,713, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

private theorem marked_odd_bound
    {H W U : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H W)
    (τ : Representation (ZMod 2) MathieuCode.m22PairStabilizer U)
    (a : H →* MathieuCode.m22PairStabilizer) (ha : Function.Injective a)
    (E : W ≃ₗ[ZMod 2] U) (hE : ∀ b v, E (ρ b v) = τ (a b) (E v))
    (hτ : ∀ B : Subgroup MathieuCode.m22PairStabilizer, ∀ p : ℕ,
      p.Prime → Odd p → Nat.card B = p → 6 ≤ fixedCodim τ B)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (b : H) (hb : orderOf b = p) :
    6 ≤ fixedCodim ρ (zpowers b) := by
  rw [fixedCodim_map_equivariant ρ τ a E hE]
  apply hτ _ p hp ho
  rw [card_map_of_injective ha,Nat.card_zpowers,hb]

/-- The native six-dimensional odd displacement holds on the full original
automizer in either simple M22 row. -/
theorem sourceOrbit_m22_odd_fixedCodim_ge_six
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (b : Automizer D.sourceOrbit) (hb : orderOf b = p) :
    6 ≤ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers b) := by
  rcases D.sourceOrbit_m22_simple_marking_of_many h hmany hV hq hnon with hc | hc
  · obtain ⟨d⟩ := hc
    obtain ⟨a,ha,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
    exact marked_odd_bound _ _ a ha _ hE
      (fun B _ hp ho hc => m22Outer_code_fixedCodim_ge_six B hp ho hc) p hp ho b hb
  · obtain ⟨d⟩ := hc
    obtain ⟨a,ha,hE,_⟩ := D.sourceOrbit_m22_cocode_full_automizer h.toHypothesis1221 d
    exact marked_odd_bound _ _ a ha _ hE
      (fun B _ hp ho hc => m22Outer_cocode_fixedCodim_ge_six B hp ho hc) p hp ho b hb

/-- At a subspace of rank at least five, the original local centralizer
already satisfies the odd-Cartan premise of E.6.27. -/
theorem sourceOrbit_m22_large_local_nPrime_le_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit) (hr : 4 < rank U) :
    ChapterE.Section06.FixedPointBounds.nPrime
      (inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ centralizer (U : Set G))) ≤ 1 := by
  have h61 := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV
  apply induced_nPrime_le_one_of_odd_fixedCodim D.sourceOrbit _ U
    (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right (b := 6) (c := 1)
  · intro p hp ho b hb
    simpa only [one_mul] using D.sourceOrbit_m22_odd_fixedCodim_ge_six h hmany hV hq hnon p hp ho b hb
  · have hd : rank D.sourceOrbit = 10 := by
      have he : Module.finrank (ZMod 2) D.orbitSpace = 10 := by
        rcases D.sourceOrbit_m22_simple_marking_of_many h hmany hV hq hnon with hc | hc
        · exact (Classical.choice hc).degree
        · exact (Classical.choice hc).degree
      exact (Chapter7.log_card_eq_finrank D.sourceOrbit).trans
        (D.sourceOrbitCoordinates.finrank_eq.symm.trans he)
    have hadd := offender_corank_add (B := (⊥ : Subgroup G)) bot_le hUW
    have he : rank D.sourceOrbit = subgroupCorank D.sourceOrbit U + rank U := by
      simpa only [subgroupCorank,relIndex_bot_left,rank] using hadd
    omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
