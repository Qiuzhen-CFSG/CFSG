module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeOffender
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuFiveBounds
public import CFSG.Quasithin.Chapter8.Section02.Offenders.FixedPoints

/-!
# The fixed subgroup of the original M24 code offender

The source weak-closure bound makes the actor nontrivial. Together with the
exact centralizer kernel and corank one, non-FF forces the fixed subgroup
to be the intersection of the two original conjugates. Hence the original
selected pair centralizes it. Its rank and the full actor rank add to ten.
This proves the fixed-subgroup equality in 8.2.5 before the remaining
rank saturation and model identification; neither is assumed here.
Source: Aschbacher--Smith 8.2.2--5, printed pp.714--717.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original M24 code pair centralizes its fixed subgroup. The full
offender image has rank between four and six, and the fixed subgroup has
complementary rank adding to ten. No action-kernel or fixed-space premise
is added to the original inputs. -/
theorem sourceOrbit_m24_code_fixed_pair_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let B := inducedAutomizer D.sourceOrbit A
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      globalW D.sourceOrbit (T : Subgroup G) = 1 ∧
      IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧
      I ≤ centralizer (U : Set G) ∧
      4 ≤ rank B ∧ rank B ≤ 6 ∧
      subgroupCorank D.sourceOrbit U = 1 + rank B ∧
      rank U + rank B = 10 := by
  obtain ⟨I,i,S,s,hw,hOff,hA,hAT,hker,hc⟩ :=
    D.sourceOrbit_m24_code_offender_pair_of_many h hmany hV hq hnon a E hE hH
  have hFF := D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon
  have hr := D.sourceOrbit_largeMathieu_globalR_ge_five h hmany hV (.inr hq) hnon
  have hi := (lemma_E_3_28 D.sourceOrbit_weakClosure_setup (Or.inr hFF) hOff).2.1.1
  rw [hw] at hi
  have hfour : 4 ≤ rank (inducedAutomizer D.sourceOrbit
      (offenderNormalizer D.sourceOrbit i.val⁻¹)) := by
    have hl : (5 : ℕ) ≤ 1 + rank (inducedAutomizer D.sourceOrbit
        (offenderNormalizer D.sourceOrbit i.val⁻¹)) := by
      exact_mod_cast hr.trans hi
    omega
  have hsix := (offender_automizer_rank_le D.sourceOrbit i.val⁻¹).trans
    ((_root_.primeRank_le_of_injective 2 a.toMonoidHom a.injective).trans m24_twoRank_le_six)
  have hcor : subgroupCorank (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
      (offenderNormalizer D.sourceOrbit i.val⁻¹) = 1 := by
    exact_mod_cast hOff.2.symm.trans hw
  have hf := fixed_eq_intersection_of_nonFF D.sourceOrbit i.val⁻¹ hFF
    (by omega) hker hcor
  have hcentral := generated_pair_centralizes_fixed D.sourceOrbit i.val⁻¹ hf
  rw [s.generate] at hcentral
  have hz := intersection_corank D.sourceOrbit i.val⁻¹ hker
  rw [← hf,hcor] at hz
  have hv : rank D.sourceOrbit = 11 :=
    (Chapter7.log_card_eq_finrank D.sourceOrbit).trans (E.finrank_eq.trans finrank_code)
  have hsum := offender_corank_add (W := D.sourceOrbit)
    (A := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G))
    (B := ⊥) bot_le inf_le_left
  have hsum' : rank D.sourceOrbit =
      subgroupCorank D.sourceOrbit
        (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) +
      rank (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hsum
  refine ⟨I,i,S,s,hw,hOff,hf,hf.trans hker.symm,hcentral,hfour,hsix,hz,?_⟩
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
