module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveQuarticData
public import Stellmacher.Recognition.LyonsU3Four.SylowQuarticCharacters
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveQuarticExtension
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveOddElements
public import Theory.Character.LinearTwist

/-!
# The fifteen genuine quartic characters of the local group

Each of the three central kernels gives five linear twists of its normalized
extension. Restriction to the Sylow subgroup distinguishes the central index;
values on the complement distinguish the five twists. Scalar twisting keeps
these characters representation-backed and irreducible.

The Lemma 4 identity follows from the central scalar formula and Fourier
inversion on the complement, including the identity odd-order element.
The construction lemmas first take explicit Sylow and extension witnesses.
The final theorems discharge both existence premises using the separate Sylow
character and rational-extension constructions, and supply the fifteen rows
from the given order-fifteen automorphism alone.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (α : FiveComplement →* MulAut S)

omit [Finite G] in
/-- Every element of the chosen complement has odd order. -/
theorem localFive_inr_odd (a : FiveComplement) :
    Odd (orderOf (SemidirectProduct.inr a : LocalFiveGroup S α)) := by
  rw [orderOf_injective _ SemidirectProduct.inr_injective]
  have hd : orderOf a ∣ 5 := by
    simpa [FiveComplement, Nat.card_eq_fintype_card] using orderOf_dvd_natCard a
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with he | he <;> rw [he] <;> decide

/-- The sum of the four other linear characters, including at the identity. -/
theorem fiveLinear_sum_erase (χ : FiveLinearIndex) (a : FiveComplement) :
    ∑ ψ ∈ (Finset.univ.erase χ), ψ a = if a = 1 then 4 else -χ a := by
  have he := Finset.sum_erase_add (Finset.univ : Finset FiveLinearIndex)
    (fun ψ => ψ a) (Finset.mem_univ χ)
  rw [AbelianLinearCharacters.sum_apply] at he
  by_cases ha : a = 1
  · subst a
    simp only [map_one] at he
    norm_num [FiveComplement, Nat.card_eq_fintype_card] at he ⊢
    linear_combination he
  · simp only [ha, if_false] at he ⊢
    exact eq_neg_of_add_eq_zero_left he

/-- The pointwise twist of a normalized extension by an inflated linear row. -/
def localFiveQuarticTwist (φ : ConjClassFunction (LocalFiveGroup S α))
    (χ : FiveLinearIndex) : ConjClassFunction (LocalFiveGroup S α) :=
  localFiveLinear S α χ * φ

omit [Finite G] in
@[simp] theorem localFiveQuarticTwist_apply (φ : ConjClassFunction (LocalFiveGroup S α))
    (χ : FiveLinearIndex) (x : LocalFiveGroup S α) :
    localFiveQuarticTwist S α φ χ (ConjClasses.mk x) = χ x.right * φ (ConjClasses.mk x) := rfl

/-- Each twist is afforded by an irreducible complex representation. -/
theorem localFiveQuarticTwist_irreducible (φ : ConjClassFunction (LocalFiveGroup S α))
    (hφ : IsIrreducibleConjCharacter φ) (χ : FiveLinearIndex) :
    IsIrreducibleConjCharacter (localFiveQuarticTwist S α φ χ) := by
  change IsIrreducibleConjCharacter ((localFiveLinearHom S α χ).characterClass * φ)
  exact hφ.linearTwist (localFiveLinearHom S α χ)

variable {S α}
/-- The specified Sylow character has degree four. -/
theorem IsSylowQuarticCharacter.degree {z : QuarticCentralIndex S}
    {θ : ConjClassFunction S} (hθ : IsSylowQuarticCharacter S z θ) :
    θ (ConjClasses.mk 1) = 4 := by simp [hθ.value]

/-- Extension preserves degree four. -/
theorem IsLocalFiveQuarticExtension.degree {z : QuarticCentralIndex S}
    {θ : ConjClassFunction S} {φ : ConjClassFunction (LocalFiveGroup S α)}
    (hφ : IsLocalFiveQuarticExtension S α z θ φ) (hθ : IsSylowQuarticCharacter S z θ) :
    φ (ConjClasses.mk 1) = 4 := by
  simpa using (hφ.restriction 1).trans hθ.degree

/-- Twisting by an inflated linear character preserves the Sylow restriction. -/
theorem localFiveQuarticTwist_restriction {z : QuarticCentralIndex S}
    {θ : ConjClassFunction S} {φ : ConjClassFunction (LocalFiveGroup S α)}
    (hφ : IsLocalFiveQuarticExtension S α z θ φ) (χ : FiveLinearIndex) (s : S) :
    localFiveQuarticTwist S α φ χ (ConjClasses.mk (SemidirectProduct.inl s)) =
      θ (ConjClasses.mk s) := by
  simp [localFiveQuarticTwist_apply, hφ.restriction]

/-- All five twists have degree four. -/
theorem localFiveQuarticTwist_degree {z : QuarticCentralIndex S}
    {θ : ConjClassFunction S} {φ : ConjClassFunction (LocalFiveGroup S α)}
    (hφ : IsLocalFiveQuarticExtension S α z θ φ) (hθ : IsSylowQuarticCharacter S z θ)
    (χ : FiveLinearIndex) :
    localFiveQuarticTwist S α φ χ (ConjClasses.mk 1) = 4 := by
  simpa using (localFiveQuarticTwist_restriction hφ χ 1).trans hθ.degree

/-- The signed four-character sum in Lyons Lemma 4. -/
theorem localFiveQuarticTwist_lemma_four {z : QuarticCentralIndex S}
    {θ : ConjClassFunction S} {φ : ConjClassFunction (LocalFiveGroup S α)}
    (hφ : IsLocalFiveQuarticExtension S α z θ φ) (hθ : IsSylowQuarticCharacter S z θ)
    (χ : FiveLinearIndex) (w : QuarticCentralIndex S) (u : LocalFiveGroup S α)
    (hu : Odd (orderOf u)) :
    localFiveQuarticTwist S α φ χ
      (ConjClasses.mk (SemidirectProduct.inl w.1.1 * u)) =
      quarticCentralSign z w * ∑ ψ ∈ Finset.univ.erase χ, ψ u.right := by
  rw [localFiveQuarticTwist_apply, hφ.central_mul, fiveLinear_sum_erase]
  simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
  by_cases he : u = 1
  · subst u
    simp [hφ.degree hθ]
  · have hr := mt (localFive_odd_right_eq_one_iff S α u hu).mp he
    rw [if_neg hr, hφ.odd_value u hu he]
    ring

variable (S α)
/-- The central kernel and linear twist jointly determine the row. -/
theorem localFiveQuarticTwist_joint_injective
    (θ : QuarticCentralIndex S → ConjClassFunction S)
    (φ : QuarticCentralIndex S → ConjClassFunction (LocalFiveGroup S α))
    (hθ : ∀ z, IsSylowQuarticCharacter S z (θ z))
    (hφ : ∀ z, IsLocalFiveQuarticExtension S α z (θ z) (φ z)) :
    Function.Injective (fun p : QuarticCentralIndex S × FiveLinearIndex =>
      localFiveQuarticTwist S α (φ p.1) p.2) := by
  rintro ⟨z, χ⟩ ⟨w, ψ⟩ he
  change localFiveQuarticTwist S α (φ z) χ = localFiveQuarticTwist S α (φ w) ψ at he
  have hzw : z = w := by
    by_contra hn
    have hv := congrFun he (ConjClasses.mk (SemidirectProduct.inl z.1.1))
    rw [localFiveQuarticTwist_restriction (hφ z),
      localFiveQuarticTwist_restriction (hφ w), (hθ z).value, (hθ w).value] at hv
    have hz1 : z.1.1 ≠ (1 : S) := fun hh => z.2 (Subtype.ext hh)
    have hzw' : z.1.1 ≠ w.1.1 := fun hh => hn (Subtype.ext (Subtype.ext hh))
    norm_num [hz1, hzw', z.1.2] at hv
  subst w
  congr 1
  apply MonoidHom.ext
  intro a
  by_cases ha : a = 1
  · simp [ha]
  · have hn : (SemidirectProduct.inr a : LocalFiveGroup S α) ≠ 1 := by
      intro hh
      exact ha (congrArg SemidirectProduct.right hh)
    have hv := congrFun he (ConjClasses.mk (SemidirectProduct.inr a))
    simp only [localFiveQuarticTwist_apply, SemidirectProduct.right_inr,
      (hφ z).odd_value _ (localFive_inr_odd S α a) hn] at hv
    simpa using hv

/-- There are three central indices and five twists for each. -/
theorem quarticRowIndex_card (h : SylowStructure S) :
    Nat.card (QuarticCentralIndex S × FiveLinearIndex) = 15 := by
  rw [Nat.card_prod, quarticCentralIndex_card S h, fiveLinearIndex_card]

/-- Reindexing the three-by-five construction supplies fifteen distinct rows. -/
theorem exists_fifteen_quartic_characters_of_extensions (h : SylowStructure S)
    (θ : QuarticCentralIndex S → ConjClassFunction S)
    (φ : QuarticCentralIndex S → ConjClassFunction (LocalFiveGroup S α))
    (hθ : ∀ z, IsSylowQuarticCharacter S z (θ z))
    (hφ : ∀ z, IsLocalFiveQuarticExtension S α z (θ z) (φ z)) :
    ∃ η : Fin 15 → ConjClassFunction (LocalFiveGroup S α),
      (∀ i, IsIrreducibleConjCharacter (η i)) ∧ Function.Injective η ∧
      (∀ i, η i (ConjClasses.mk 1) = 4) := by
  let e : QuarticCentralIndex S × FiveLinearIndex ≃ Fin 15 := by
    simpa only [quarticRowIndex_card S h] using
      Finite.equivFin (QuarticCentralIndex S × FiveLinearIndex)
  refine ⟨fun i => localFiveQuarticTwist S α (φ (e.symm i).1) (e.symm i).2,
    fun i => localFiveQuarticTwist_irreducible S α _ (hφ _).irreducible _,
    (localFiveQuarticTwist_joint_injective S α θ φ hθ hφ).comp e.symm.injective, ?_⟩
  intro i
  exact localFiveQuarticTwist_degree (hφ _) (hθ _) _

variable (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
include h β hβ hα

/-- Construct the three Sylow quartic characters and their normalized rational
extensions simultaneously from the supplied automorphism. Each Sylow character
has the complete central value table and an actual degree-four realization with
kernel `zpowers z`, by `IsSylowQuarticCharacter.exists_representation`. -/
theorem exists_localFiveQuarticExtensions :
    ∃ (θ : QuarticCentralIndex S → ConjClassFunction S)
      (φ : QuarticCentralIndex S → ConjClassFunction (LocalFiveGroup S α)),
      (∀ z, IsSylowQuarticCharacter S z (θ z)) ∧
      (∀ z, IsLocalFiveQuarticExtension S α z (θ z) (φ z)) := by
  choose θ hθ using exists_sylowQuarticCharacter S h β hβ
  choose φ hφ using fun z => (hθ z).exists_extension h β hβ α hα
  exact ⟨θ, φ, hθ, hφ⟩

/-- The supplied local group has fifteen distinct genuine irreducible
degree-four characters, without any character-existence assumptions. -/
theorem exists_fifteen_quartic_characters :
    ∃ η : Fin 15 → ConjClassFunction (LocalFiveGroup S α),
      (∀ i, IsIrreducibleConjCharacter (η i)) ∧ Function.Injective η ∧
      (∀ i, η i (ConjClasses.mk 1) = 4) := by
  obtain ⟨θ, φ, hθ, hφ⟩ := exists_localFiveQuarticExtensions S α h β hβ hα
  exact exists_fifteen_quartic_characters_of_extensions S α h θ φ hθ hφ

/-- The three-by-five quartic rows with their full Sylow restriction and Lyons
Lemma 4 identity. The signed sum omits precisely the twisting character, giving
the positive and negative permutations of `(0,1,1,1,1)`. -/
theorem exists_localFiveQuartic_rows :
    ∃ η : QuarticCentralIndex S × FiveLinearIndex →
        ConjClassFunction (LocalFiveGroup S α),
      (∀ p, IsIrreducibleConjCharacter (η p)) ∧ Function.Injective η ∧
      (∀ p, η p (ConjClasses.mk 1) = 4) ∧
      (∀ (z : QuarticCentralIndex S) (χ : FiveLinearIndex) (s : S),
        η (z, χ) (ConjClasses.mk (SemidirectProduct.inl s)) =
          if s = 1 ∨ s = z.1.1 then 4 else if s ∈ Subgroup.center S then -4 else 0) ∧
      (∀ (z w : QuarticCentralIndex S) (χ : FiveLinearIndex)
        (u : LocalFiveGroup S α), Odd (orderOf u) →
        η (z, χ) (ConjClasses.mk (SemidirectProduct.inl w.1.1 * u)) =
          quarticCentralSign z w * ∑ ψ ∈ Finset.univ.erase χ, ψ u.right) := by
  obtain ⟨θ, φ, hθ, hφ⟩ := exists_localFiveQuarticExtensions S α h β hβ hα
  refine ⟨fun p => localFiveQuarticTwist S α (φ p.1) p.2,
    fun p => localFiveQuarticTwist_irreducible S α _ (hφ _).irreducible _,
    localFiveQuarticTwist_joint_injective S α θ φ hθ hφ,
    fun p => localFiveQuarticTwist_degree (hφ _) (hθ _) _, ?_, ?_⟩
  · intro z χ s
    exact (localFiveQuarticTwist_restriction (hφ z) χ s).trans ((hθ z).value s)
  · intro z w χ u hu
    exact localFiveQuarticTwist_lemma_four (hφ z) (hθ z) χ w u hu

end
end Stellmacher.Recognition.LyonsU3Four
