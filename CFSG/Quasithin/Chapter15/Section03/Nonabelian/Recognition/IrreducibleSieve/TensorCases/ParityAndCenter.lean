module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.TensorKernel
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# The odd tensor and the SL₃ half-field tensor exclusions

The corrected case (14) has odd degree even when its component group is
proper in the full actor. In case (17), comparison with the source degree
forces the half-field exponent to be two. The tensor then has trivial
central kernel, so the component is SL₃(16), whose center has order three.
This contradicts the centerlessness of a nonsolvable minimal normal subgroup.

The field and kernel lemmas below also construct the precise model interface
from a faithful scalar-extension comparison. In particular its kernel clauses
are consequences of the actual tensor action, not an assumed exclusion.

Source: Aschbacher--Smith, G.9.3(14),(17), printed p.354, and 15.3.58,
printed p.1149.
-/

public section

open Representation Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases

open CFSG.Quasithin.ChapterG.Section09
open DefiningCharacteristic.LinearThreeRecognition

/-- The named half-field has the required order. -/
theorem tensorHalfField_card (n : ℕ) (hn : 0 < n) :
    Nat.card (TensorHalfField n) = 2 ^ n := by
  let : NeZero n := ⟨hn.ne'⟩
  exact Representation.OrthogonalFourMinus.FiniteModel.card_fixedField n

/-- The specified field automorphism is involutory at every positive exponent. -/
theorem tensorConjugation_involutive (n : ℕ) (hn : 0 < n) :
    Function.Involutive (tensorConjugation n) := by
  let : NeZero n := ⟨hn.ne'⟩
  exact Representation.OrthogonalFourMinus.FiniteModel.conjugation_involutive n

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {K : Subgroup H}

/-- The SL₂ coordinates in case (16) induce the actual projective group
identification through the canonical central quotient. -/
theorem TripleCase.component_psl {m : ℕ} (ht : TripleCase ρ K m) :
    Nonempty (K ≃* PSL(2, GaloisField 2 3)) := by
  obtain ⟨e, _⟩ := ht
  exact ⟨e.trans (Theory.PSL2.sl2QuotientEquiv _)⟩

/-- A faithful descended tensor determines precisely the kernel used in the
model alternative. This supplies the interface from the raw scalar-extension
conclusion without assuming either kernel calculation. -/
theorem halfFieldTensor_of_extension {n : ℕ} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 2)
    (hf : Function.Injective (ρ.comp K.subtype))
    (π : SL(3, TensorField n) →* K) (hπ : Function.Surjective π)
    (hc : π.ker ≤ center SL(3, TensorField n))
    (scalar : Module (TensorHalfField n) W) :
    letI := scalar
    letI : Algebra (ZMod 2) (TensorHalfField n) := ZMod.algebra (TensorHalfField n) 2
    letI : Module (ZMod 2) (TensorHalfField n) := Algebra.toModule
    ∀ τ : Representation (TensorHalfField n) K W,
      restrictScalars (k := ZMod 2) τ = ρ.comp K.subtype →
      Nonempty ((extendScalars (TensorField n) (τ.comp π)).Equiv
        (twistedTensor (TensorField n) (tensorConjugation n))) →
      HalfFieldTensor ρ K n := by
  let := scalar
  let : Algebra (ZMod 2) (TensorHalfField n) := ZMod.algebra (TensorHalfField n) 2
  let : Module (ZMod 2) (TensorHalfField n) := Algebra.toModule
  intro τ hτ he
  have hfaith : Function.Injective τ := by
    intro a b hab
    apply hf
    rw [← hτ]
    ext w
    exact congrArg (fun f : Module.End (TensorHalfField n) W => f w) hab
  have hk := twisted_cover_recognition π hπ hc τ hfaith hn₁ hn₂
    (tensorConjugation n) (fun a => iterateFrobeniusEquiv_def _ _ _ a) (Or.inl he)
  refine ⟨π, hπ, ?_, scalar, τ, hτ, he⟩
  rcases hk with ⟨hn, hk, _⟩ | ⟨hn, hk, _⟩
  · exact Or.inl ⟨hn, hk⟩
  · exact Or.inr ⟨hn, hk⟩

/-- The covering maps in the model yield the actual source groups. -/
theorem HalfFieldTensor.group_models {n : ℕ} (ht : HalfFieldTensor ρ K n) :
    (n = 1 ∧ Nonempty (K ≃* PSL(3, TensorField n))) ∨
      (n = 2 ∧ Nonempty (K ≃* SL(3, TensorField n))) := by
  obtain ⟨π, hπ, hk, _⟩ := ht
  rcases hk with ⟨hn, hk⟩ | ⟨hn, hk⟩
  · exact Or.inl ⟨hn, ⟨(QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk)⟩⟩
  · exact Or.inr ⟨hn, ⟨(MulEquiv.ofBijective π ⟨π.ker_eq_bot_iff.mp hk, hπ⟩).symm⟩⟩

variable [Finite H] [FiniteDimensional (ZMod 2) W]
  {X : Subgroup H} {T : Sylow 2 H} {v : H} {s : ℕ}

/-- The nine-dimensional component tensor is excluded without identifying the
full actor with the product. -/
theorem not_productCase (h : SourceData ρ X T v s) : ¬ ProductCase ρ K (s + 1) := by
  rintro ⟨he, _, _⟩
  exact h.not_odd_component_model K TwoComponents.threeTensor
    (by rw [TwoComponents.threeTensor_degree]; decide) he

/-- The source degree and rank force the larger of the two half-fields. -/
theorem twistedThree_parameters (h : SourceData ρ X T v s) {n : ℕ}
    (hd : Module.finrank (ZMod 2) W = 9 * n) (hm : s + 1 = 4 * n) :
    n = 2 ∧ s = 7 := by
  have := h.dimension
  omega

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
/-- The actual SL₃(16) model cannot be a nonsolvable minimal normal subgroup. -/
theorem not_specialLinear_sixteen (hK : ComponentData ρ K)
    (e : K ≃* SL(3, TensorField 2)) : False := by
  have hc := Nat.card_congr (centerCongr e).toEquiv
  rw [hK.center_eq_bot, card_bot] at hc
  have hz : center SL(3, TensorField 2) = ⊥ := card_eq_one.mp hc.symm
  have hm := (Matrix.SL3.center_eq_bot_iff_card_mod_three (TensorField 2)).mp hz
  apply hm
  change Nat.card (GaloisField 2 4) % 3 = 1
  rw [GaloisField.card 2 4 (by decide)]
  decide

/-- Case (17) is impossible by degree arithmetic and its true central kernel.
No involution-placement or model-exclusion premise is used. -/
theorem not_twistedThreeCase (h : SourceData ρ X T v s) (hK : ComponentData ρ K) :
    ¬ TwistedThreeCase ρ K (s + 1) := by
  rintro ⟨n, _, _, ht, hd, hm⟩
  obtain ⟨rfl, _⟩ := twistedThree_parameters h hd hm
  rcases ht.group_models with ⟨hn, _⟩ | ⟨_, ⟨e⟩⟩
  · omega
  · exact not_specialLinear_sixteen hK e

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases
