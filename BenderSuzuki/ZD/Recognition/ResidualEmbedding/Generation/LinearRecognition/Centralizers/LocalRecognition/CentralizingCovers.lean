module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.CentralizingCovers.Recognition
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.CentralizingCovers.Embeddings

/-!
# The remaining central-cover input to GLS Lemma 12.3

The local quotient is recognized at the same exponent as the distinguished
subgroup `A`, and the covering group is perfect with odd center. PSL₂ and
Suzuki quotients lift by the checked odd-central-cover theorem. The unitary
quotient requires the separate source theorem recognizing a perfect odd
central extension as PSU₃ or SU₃. The same-parameter embedding exclusions
then give exactly the centralizing-extension alternative of Lemma 12.3.

The theorem below retains that unitary-cover theorem as an explicit input;
it does not assert that Lemma 12.3 has been completed. Its existing producer
is `ModelGeometry/UnitaryCovers.lean`, whose unconditional assembly awaits
PSU₃ universality. The source statement belongs to this module once that
input is discharged.

Source: GLS4, Chapter 2, Lemma 12.3; Chapter 4, Lemmas 2.8(a) and 3.9(a).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup _root_.BenderSuzuki.MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The complete Lemma 12.3 argument conditional only on the independent
PSU₃ odd-central-cover theorem (GLS4, Chapter 4, Lemma 2.8(a)). Every local
recognition, common-parameter and embedding premise is discharged here. -/
public theorem proper_residualGenerated_centralizing_extension_of_unitary_covers
    (hunitary : ∀ (F : Type u) [Group F] [Finite F] (n : ℕ), 2 ≤ n →
      ∀ (E : Type) [Field E] [Finite E] (J : HermitianForm 3 E),
        J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] →
        Nat.card E = (2 ^ n) ^ 2 →
        Nat.card {x : E // J.conj x = x} = 2 ^ n →
        commutator F = ⊤ → Odd (Nat.card (center F)) →
        Nonempty ((F ⧸ center F) ≃* ProjectiveSpecialUnitaryMatrixGroup J) →
        Nonempty (F ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
          Nonempty (F ≃* J.specialSubgroup))
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    ∀ v ∈ centralizer (residualGenerated M z t : Set G), v ≠ 1 →
      centralizerClosure Z v = residualGenerated M z t ∨
        ∃ n : ℕ, 2 ≤ n ∧ Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n ∧
          Nonempty (residualGenerated M z t ≃* PSL2BinaryMatrixGroup n) ∧
          residualGenerated M z t < centralizerClosure Z v ∧
          IsUnitaryCentralizerCoverAt n (centralizerClosure Z v) := by
  intro v hvL hv
  obtain ⟨n, hn, hmodels, hAL, hDN, hlocal, hcore, hnormal, hA, hcard, hrest⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  let F := centralizerClosure Z v
  obtain ⟨hcenter, hperfect, hquot⟩ := proper_centralizing_quotient_atExponent
    h r ha hz hzM ht htM hL heven hvL hv hn hcard
  have hres : twoPrimeResidual F = ⊤ := by
    apply top_unique
    rw [← centralizerClosure_involutionCore_eq_top h.disconnected v,
      involutionCore_eq_closure, closure_le]
    intro x hx
    exact isPGroup_le_twoPrimeResidual (isPGroup_two_zpowers_of_isInvolution hx) (mem_zpowers x)
  have hFmodels : (Nonempty (F ≃* PSL2BinaryMatrixGroup n) ∨
      ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧ Nonempty (F ≃* SuzukiMatrixGroup m)) ∨
      IsUnitaryCentralizerCoverAt n F := by
    cases hquot with
    | isPSL2 he =>
      have hlift := lemma114_model_psl_or_suzuki_of_model hn (Or.inl he) hres hcenter
      rcases hlift with he | ⟨m, hm, he⟩
      · exact Or.inl (Or.inl he)
      · exact Or.inl (Or.inr ⟨m, by omega, hm, he⟩)
    | isSuzuki he =>
      have hlift := lemma114_model_psl_or_suzuki_of_model hn (Or.inr he) hres hcenter
      rcases hlift with he | ⟨m, hm, he⟩
      · exact Or.inl (Or.inl he)
      · exact Or.inl (Or.inr ⟨m, by omega, hm, he⟩)
    | isPSU3 he =>
      obtain ⟨E, hfield, hfinite, J, hJ, hc, hfixed, ⟨e⟩⟩ := he
      let : Field E := hfield
      let : Finite E := hfinite
      have hcOdd : Odd (Nat.card (center F)) := by
        rw [← hcenter]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      let ecenter : (F ⧸ center F) ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
        (QuotientGroup.quotientMulEquivOfEq hcenter).symm.trans e
      exact Or.inr ⟨E, hfield, hfinite, J, hJ, hc, hfixed,
        hunitary F n hn E J hJ hc hfixed hperfect hcOdd ⟨ecenter⟩⟩
  have hLF := residualGenerated_le_centralizerClosure_of_centralizes h.disconnected hz ht hvL
  rcases CentralizingCovers.eq_or_unitary_of_models hLF hmodels hFmodels with he | ⟨he, hlt, hU⟩
  · exact Or.inl he
  · exact Or.inr ⟨n, hn, hcard, he, hlt, hU⟩

end BenderSuzuki.ZD
