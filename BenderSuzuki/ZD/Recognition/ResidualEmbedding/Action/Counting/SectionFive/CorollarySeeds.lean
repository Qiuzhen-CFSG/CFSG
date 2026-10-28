module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.Seeds
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Elementary
public import BenderSuzuki.SE.Theorem2

/-!
# Corollary 5.7 before the action theorem

Failure of double transitivity gives a pair-stabilizer Sylow with at least
three fixed points by Bender's criterion. Its distinguished swapping
involution supplies the required global prime share. Extend to a maximal
candidate, and apply Proposition 5.2 to make it fix its distinguished
involution's point. One conjugation then sends the involution to the specified
base involution and the subgroup into the base stabilizer, preserving the
prime, inverted cardinality and fixed-set cardinality.

This proves the first assertion of Corollary 5.7 independently of Theorem 2.
It does not combine that assertion with the corollary's separate pair-Sylow
witness. Source: GLS, Volume 4, Chapter 2, Corollary 5.7, printed p.41.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Corollary 5.7's first seed, with its prescribed prime and base involution,
follows directly from Proposition 5.2 and the permutation criterion. -/
public theorem actionSaturationSeeds_of_maximalFixes
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    (hf : ActionPrimeShareMaximalFixes Z M) : ActionSaturationSeeds Z M := by
  classical
  intro z hzZ hzM p hp hpodd hnot
  have hbad : ¬ ∀ (beta gamma : G ⧸ M), beta ≠ gamma → ∀ Q : Subgroup G,
      theorem4bIsSylowSubgroupOf p Q
        (MulAction.stabilizer G beta ⊓ MulAction.stabilizer G gamma) →
      Nat.card (theorem4bFixedPoints M Q) = 2 := by
    intro hh
    exact hnot (chapter1_bender_criterion (conjugateCosetSpace_isPretransitive M)
      hp hpodd (fun {beta gamma} hne Q hQ => hh beta gamma hne Q hQ))
  push Not at hbad
  obtain ⟨beta, gamma, hne, Q, hQsyl, hQc⟩ := hbad
  have hQp : IsPGroup p Q := by
    obtain ⟨S, rfl⟩ := hQsyl
    exact S.isPGroup'.map _
  have hQD : Q ≤ MulAction.stabilizer G beta ⊓ MulAction.stabilizer G gamma := by
    obtain ⟨S, rfl⟩ := hQsyl
    simpa using Subgroup.map_le_range
      (MulAction.stabilizer G beta ⊓ MulAction.stabilizer G gamma).subtype
      (S : Subgroup (MulAction.stabilizer G beta ⊓ MulAction.stabilizer G gamma : Subgroup G))
  have hbeta : beta ∈ fixedPointsOfSubgroup G (G ⧸ M) Q := fun x hx =>
    MulAction.mem_stabilizer_iff.mp (hQD hx).1
  have hgamma : gamma ∈ fixedPointsOfSubgroup G (G ⧸ M) Q := fun x hx =>
    MulAction.mem_stabilizer_iff.mp (hQD hx).2
  have hntr : Nontrivial (theorem4bFixedPoints M Q) :=
    ⟨⟨⟨beta, hbeta⟩, ⟨gamma, hgamma⟩, fun he => hne (congrArg Subtype.val he)⟩⟩
  have hthree : 3 ≤ Nat.card (theorem4bFixedPoints M Q) := by
    have := Finite.one_lt_card_iff_nontrivial.mpr hntr
    omega
  obtain ⟨s, hsZ, hsN, hsMove⟩ := sectionFive_distinguished_sylow_swap h h3 hp hpodd hne hQsyl
  have hInv : theorem4bInvertedCard s Q = theorem4bPrimeShare M z p :=
    (h3.swapping_bound z hzZ hzM s hsZ beta (by simpa [hsMove] using hne.symm)
      p hp hpodd Q hQp (by simpa [hsMove] using hQD) hsN).2
        (by simpa [hsMove] using hQsyl)
  have hgood : actionPrimeShareCandidate Z M z p Q := ⟨hQp, hthree, s, hsZ, hsN, hInv⟩
  obtain ⟨R, _, hRmax⟩ := Finite.exists_le_maximal hgood
  obtain ⟨s, hsZ, hsN, hsInv⟩ := hRmax.1.2.2
  obtain ⟨g, hg⟩ := isConj_iff.mp (productDisconnected_isConj h s hsZ z hzZ)
  let base : G ⧸ M := QuotientGroup.mk 1
  let alpha : G ⧸ M := g⁻¹ • base
  have hzbase : z • base = base := by
    apply MulAction.mem_stabilizer_iff.mp
    simpa only [base, baseCoset_stabilizer] using hzM
  have hsalpha : s • alpha = alpha := by
    apply MulAction.injective g
    calc
      g • (s • alpha) = (g * s * g⁻¹) • base := by simp [alpha, mul_smul]
      _ = base := by rw [hg, hzbase]
      _ = g • alpha := by simp [alpha]
  have hRalpha := hf z hzZ hzM p hp hpodd R hRmax s hsZ hsN alpha hsalpha
  let P := R.conjBy g
  have hPM : P ≤ M := by
    rintro x ⟨y, hy, rfl⟩
    change g * y * g⁻¹ ∈ M
    have hyfix := MulAction.mem_stabilizer_iff.mp (hRalpha hy)
    have hfix : (g * y * g⁻¹) • base = base := by
      simpa only [alpha, mul_smul, smul_inv_smul] using
        congrArg (fun b : G ⧸ M => g • b) hyfix
    simpa only [base, baseCoset_stabilizer] using MulAction.mem_stabilizer_iff.mpr hfix
  have hzN : z ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_map (H := R) (MulAut.conj g).toMonoidHom ⟨s, hsN, hg⟩
  have hPthree : 3 ≤ Nat.card (theorem4bFixedPoints M P) := by
    rw [show P = R.conjBy g from rfl, sectionFive_fixedPoints_card_conj]
    exact hRmax.1.2.1
  refine ⟨P, hRmax.1.1.map (MulAut.conj g).toMonoidHom, hPM, hzN, hPthree, ?_⟩
  have hinv := theorem4bInvertedCard_conjBy s g⁻¹ R
  have he : rightConjugateElem s g⁻¹ = z := by simpa [rightConjugateElem] using hg
  simpa only [he, inv_inv, P] using hinv.trans hsInv

end BenderSuzuki.ZD
