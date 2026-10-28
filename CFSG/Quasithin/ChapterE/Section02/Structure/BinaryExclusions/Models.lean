module
public import CFSG.Quasithin.ChapterE.Section02.Structure.BinaryExclusions.Exceptional
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.BinaryLinear.Ambient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.G2
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.Algebra.CharP.CharAndCard
/-!
# The characteristic-two higher-rank sieve in E.2.2

For the original normal subgroup K and Sylow T with H = KT, minimal
parabolicity excludes binary PSL4 and PSL5, G2 (including its actual binary
derived subgroup), triality, Ree and Tits. Applying this to the literal
Theorem C rank-two list retains exactly PSL3, PSp4, and the binary PSp4
commutator, preserving the original field parameter and equivalences.

Source: Aschbacher–Smith E.2.2, printed p.216. This supplies the excluded
characteristic-two normal-component cases; the rank-one and surviving
rank-two Borel/diagram conclusions are separate source obligations.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.BinaryExclusions
variable {H : Type*} [Group H] [Finite H]

/-- The field-independent binary linear model is excluded on the actual K. -/
theorem not_linear_binary
    (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {n : ℕ} (hn : n = 4 ∨ n = 5) : ¬ ClassicalGroup.IsPSL K n 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let _ := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hnpos : 0 < n := by rcases hn with rfl | rfl <;> decide
  exact ChapterB.not_minimalParabolic_of_binary_linear_supplement T K hn
    ((e.trans (Atlas.fieldEquivPSL n f.symm)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL hnpos)) hgen hP

/-- Every binary field parameter in the full G2 model has the same obstruction. -/
theorem not_g2_binary
    (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (f : ℕ) :
    ¬ ClassificationModels.IsG2At K (2^f) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact ChapterB.not_minimalParabolic_of_normal_g2 T K hgen e hP

/-- The actual binary triality model is excluded, including exponent one. -/
theorem not_triality_binary
    (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (f : ℕ) (hf : 1 ≤ f) :
    ¬ Triality.Standard.IsTrialityGroupAt (2^f) K := by
  intro hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff K f hf).mp hm
  exact not_minimalParabolic_of_triality T K hgen _ rfl e hP

/-- The complete Theorem C rank-two dispatcher on the original normal component. -/
theorem rank_two_survivors
    (T : Sylow 2 H) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) {f : ℕ}
    (hm : ChapterA.Section02.IsTheoremCRankTwoModel K f) :
    (1 ≤ f ∧ ClassicalGroup.IsPSL K 3 (2^f)) ∨
    (2 ≤ f ∧ ClassicalGroup.IsPSp K 2 (2^f)) ∨
    (f = 1 ∧ Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) := by
  cases hm with
  | linear hf e => exact Or.inl ⟨hf,e⟩
  | symplectic hf e => exact Or.inr (Or.inl ⟨hf,e⟩)
  | g2 _ e => exact (not_g2_binary T K hgen hP f e).elim
  | triality hf e => exact (not_triality_binary T K hgen hP f hf e).elim
  | ree_f4 m hm _ e =>
    obtain ⟨e⟩ := e
    exact (not_minimalParabolic_of_ree T K hgen m hm e hP).elim
  | symplectic_derived hf e => exact Or.inr (Or.inr ⟨hf,e⟩)
  | g2_derived _ e =>
    obtain ⟨e⟩ := e
    exact (ChapterB.not_minimalParabolic_of_normal_binary_g2_derived T K hgen e hP).elim
  | tits _ e =>
    obtain ⟨e⟩ := e
    exact (not_minimalParabolic_of_tits T K hgen e hP).elim
end CFSG.Quasithin.ChapterE.BinaryExclusions
