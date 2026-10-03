module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveQuarticCharacters
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveQuinticCharacters
public import Theory.Character.DegreeCompleteness

/-!
# A complete ordinary character table for the Lyons local group

The order-320 semidirect product has five linear, fifteen quartic and three
quintic irreducible characters. The constructions retain the three rational
quartic extensions and the three inducing linear characters. Distinct degrees
separate the families, and the sum `5 + 15 * 16 + 3 * 25 = 320` proves
completeness. The same chosen rows satisfy the Sylow restriction formulas and
the signed cyclic section identities used in Lyons' Lemma 4.

This module concerns ordinary characters. Principal-block membership and
genuine modular realizations are separate transfer obligations.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 2,
p. 373, and Lemma 4, p. 381.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (α : FiveComplement →* MulAut S)

/-- The three families, retaining their central and linear indices. -/
abbrev LocalFiveRowIndex :=
  FiveLinearIndex ⊕ ((QuarticCentralIndex S × FiveLinearIndex) ⊕ Fin 3)

/-- Assemble the supplied extensions and inducing characters into ordinary rows. -/
def localFiveRow (φ : QuarticCentralIndex S → ConjClassFunction (LocalFiveGroup S α))
    (ψ : Fin 3 → S →* ℂ) : LocalFiveRowIndex S → ConjClassFunction (LocalFiveGroup S α) :=
  Sum.elim (localFiveLinear S α)
    (Sum.elim (fun p => localFiveQuarticTwist S α (φ p.1) p.2)
      (fun i => localFiveQuintic S α (ψ i)))

/-- The degrees of the five, fifteen and three rows respectively. -/
def localFiveRowDegree : LocalFiveRowIndex S → ℕ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 4) (fun _ => 5))

/-- There are twenty-three row indices. -/
theorem localFiveRowIndex_card (h : SylowStructure S) :
    Nat.card (LocalFiveRowIndex S) = 23 := by
  change Nat.card (FiveLinearIndex ⊕ ((QuarticCentralIndex S × FiveLinearIndex) ⊕ Fin 3)) = _
  rw [Nat.card_sum, Nat.card_sum, quarticRowIndex_card S h, fiveLinearIndex_card]
  norm_num

variable {S α}
/-- The assembled rows have their indicated degrees. -/
theorem localFiveRow_degree
    {θ : QuarticCentralIndex S → ConjClassFunction S}
    {φ : QuarticCentralIndex S → ConjClassFunction (LocalFiveGroup S α)}
    (hθ : ∀ z, IsSylowQuarticCharacter S z (θ z))
    (hφ : ∀ z, IsLocalFiveQuarticExtension S α z (θ z) (φ z))
    (ψ : Fin 3 → S →* ℂ) (i : LocalFiveRowIndex S) :
    localFiveRow S α φ ψ i (ConjClasses.mk 1) = (localFiveRowDegree S i : ℂ) := by
  rcases i with χ | (⟨z, χ⟩ | i)
  · simp [localFiveRow, localFiveRowDegree]
  · exact localFiveQuarticTwist_degree (hφ z) (hθ z) χ
  · exact localFiveQuintic_degree S α (ψ i)

variable (S α)
/-- The constructed rows exhaust all genuine complex irreducible characters. -/
theorem localFiveRow_complete (h : SylowStructure S) (β : MulAut S)
    (hβ : orderOf β = 15) (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (θ : QuarticCentralIndex S → ConjClassFunction S)
    (φ : QuarticCentralIndex S → ConjClassFunction (LocalFiveGroup S α))
    (hθ : ∀ z, IsSylowQuarticCharacter S z (θ z))
    (hφ : ∀ z, IsLocalFiveQuarticExtension S α z (θ z) (φ z))
    (ψ : Fin 3 → S →* ℂ)
    (hψ : (∀ i, ψ i ≠ 1) ∧ Function.Injective (fun p : Fin 3 × FiveComplement =>
      (ψ p.1).comp (α p.2).toMonoidHom)) :
    IsCompleteIrreducibleCharacterFamily (localFiveRow S α φ ψ) := by
  apply completeIrreducibleFamily_of_sum_degree_normSq
  · rintro (χ | (⟨z, χ⟩ | i))
    · exact localFiveLinear_irreducible S α χ
    · exact localFiveQuarticTwist_irreducible S α _ (hφ z).irreducible χ
    · exact localFiveQuintic_irreducible S α h β hβ hα (ψ i) (hψ.1 i)
  · intro i j he
    have hd := congrFun he (ConjClasses.mk 1)
    rw [localFiveRow_degree hθ hφ, localFiveRow_degree hθ hφ] at hd
    rcases i with χ | (p | i) <;> rcases j with χ' | (p' | j)
    · exact congrArg Sum.inl (localFiveLinear_class_injective S α he)
    · norm_num [localFiveRowDegree] at hd
    · norm_num [localFiveRowDegree] at hd
    · norm_num [localFiveRowDegree] at hd
    · exact congrArg (Sum.inr ∘ Sum.inl)
        (localFiveQuarticTwist_joint_injective S α θ φ hθ hφ he)
    · norm_num [localFiveRowDegree] at hd
    · norm_num [localFiveRowDegree] at hd
    · norm_num [localFiveRowDegree] at hd
    · exact congrArg (Sum.inr ∘ Sum.inr)
        (localFiveQuintic_joint_injective S α h β hβ hα ψ hψ he)
  · simp only [localFiveRow_degree hθ hφ, Complex.normSq_natCast]
    simp only [localFiveRowDegree, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      fiveLinearIndex_card, quarticRowIndex_card S h, localFiveGroup_card S h α]
    norm_num

/-- A complete ordinary table together with the witnesses defining its rows. -/
structure LocalFiveCharacterTable where
  sylowQuartic : QuarticCentralIndex S → ConjClassFunction S
  quartic : QuarticCentralIndex S → ConjClassFunction (LocalFiveGroup S α)
  quinticSeed : Fin 3 → S →* ℂ
  sylow_spec : ∀ z, IsSylowQuarticCharacter S z (sylowQuartic z)
  extension_spec : ∀ z, IsLocalFiveQuarticExtension S α z (sylowQuartic z) (quartic z)
  seed_nontrivial : ∀ i, quinticSeed i ≠ 1
  seed_disjoint : Function.Injective (fun p : Fin 3 × FiveComplement =>
    (quinticSeed p.1).comp (α p.2).toMonoidHom)
  complete : IsCompleteIrreducibleCharacterFamily (localFiveRow S α quartic quinticSeed)

/-- Construct the complete table from the supplied order-fifteen automorphism. -/
theorem exists_localFiveCharacterTable (h : SylowStructure S) (β : MulAut S)
    (hβ : orderOf β = 15) (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ)) :
    Nonempty (LocalFiveCharacterTable S α) := by
  obtain ⟨θ, φ, hθ, hφ⟩ := exists_localFiveQuarticExtensions S α h β hβ hα
  obtain ⟨ψ, hnon, hinj, _⟩ := exists_three_linear_orbits S h β hβ α hα
  exact ⟨⟨θ, φ, ψ, hθ, hφ, hnon, hinj,
    localFiveRow_complete S α h β hβ hα θ φ hθ hφ ψ ⟨hnon, hinj⟩⟩⟩

namespace LocalFiveCharacterTable
variable {S α} (T : LocalFiveCharacterTable S α)

/-- The complete family indexed by its linear, quartic and quintic rows. -/
def row : LocalFiveRowIndex S → ConjClassFunction (LocalFiveGroup S α) :=
  localFiveRow S α T.quartic T.quinticSeed

theorem row_complete : IsCompleteIrreducibleCharacterFamily T.row := T.complete

theorem row_degree (i : LocalFiveRowIndex S) :
    T.row i (ConjClasses.mk 1) = (localFiveRowDegree S i : ℂ) :=
  localFiveRow_degree T.sylow_spec T.extension_spec T.quinticSeed i

theorem linear_value (χ : FiveLinearIndex) (x : LocalFiveGroup S α) :
    T.row (.inl χ) (ConjClasses.mk x) = χ x.right := rfl

theorem quartic_restriction (z : QuarticCentralIndex S) (χ : FiveLinearIndex) (s : S) :
    T.row (.inr (.inl (z, χ))) (ConjClasses.mk (SemidirectProduct.inl s)) =
      if s = 1 ∨ s = z.1.1 then 4 else if s ∈ Subgroup.center S then -4 else 0 :=
  (localFiveQuarticTwist_restriction (T.extension_spec z) χ s).trans ((T.sylow_spec z).value s)

theorem quintic_restriction (i : Fin 3) (s : S) :
    T.row (.inr (.inr i)) (ConjClasses.mk (SemidirectProduct.inl s)) =
      ∑ a : FiveComplement, T.quinticSeed i (α a s) :=
  localFiveQuintic_restriction S α (T.quinticSeed i) s

theorem quintic_vanishes_off_sylow (i : Fin 3) (x : LocalFiveGroup S α)
    (hx : x.right ≠ 1) : T.row (.inr (.inr i)) (ConjClasses.mk x) = 0 :=
  localFiveQuintic_vanishes_off_sylow S α (T.quinticSeed i) x hx

theorem quartic_odd_value (z : QuarticCentralIndex S) (χ : FiveLinearIndex)
    (u : LocalFiveGroup S α) (hu : Odd (orderOf u)) :
    T.row (.inr (.inl (z, χ))) (ConjClasses.mk u) =
      if u = 1 then 4 else -χ u.right := by
  change χ u.right * T.quartic z (ConjClasses.mk u) = _
  by_cases he : u = 1
  · subst u
    simp [(T.extension_spec z).degree (T.sylow_spec z)]
  · simp [he, (T.extension_spec z).odd_value u hu he]

theorem quintic_odd_value (i : Fin 3) (u : LocalFiveGroup S α)
    (hu : Odd (orderOf u)) :
    T.row (.inr (.inr i)) (ConjClasses.mk u) = if u = 1 then 5 else 0 :=
  localFiveQuintic_odd_value S α (T.quinticSeed i) u hu

/-- The five positive or negative permutations of `(0,1,1,1,1)`. -/
theorem quartic_section (z w : QuarticCentralIndex S) (χ : FiveLinearIndex)
    (u : LocalFiveGroup S α) (hu : Odd (orderOf u)) :
    T.row (.inr (.inl (z, χ)))
      (ConjClasses.mk (SemidirectProduct.inl w.1.1 * u)) =
      quarticCentralSign z w * ∑ ψ ∈ Finset.univ.erase χ, ψ u.right :=
  localFiveQuarticTwist_lemma_four (T.extension_spec z) (T.sylow_spec z) χ w u hu

/-- The quintic rows have section coefficients `(1,1,1,1,1)`. -/
theorem quintic_section (h : SylowStructure S) (i : Fin 3)
    (w : Subgroup.center S) (u : LocalFiveGroup S α) (hu : Odd (orderOf u)) :
    T.row (.inr (.inr i)) (ConjClasses.mk (SemidirectProduct.inl (w : S) * u)) =
      ∑ χ : FiveLinearIndex, χ u.right := by
  by_cases he : u = 1
  · subst u
    change localFiveQuintic S α (T.quinticSeed i)
      (ConjClasses.mk (SemidirectProduct.inl (w : S) * 1)) = ∑ χ : FiveLinearIndex, χ 1
    rw [mul_one, localFiveQuintic_central_value S α h]
    simp [← Nat.card_eq_fintype_card, fiveLinearIndex_card]
  · have hr := mt (localFive_odd_right_eq_one_iff S α u hu).mp he
    change localFiveQuintic S α (T.quinticSeed i)
      (ConjClasses.mk (SemidirectProduct.inl (w : S) * u)) = _
    rw [localFiveQuintic_apply]
    simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
    rw [if_neg hr, AbelianLinearCharacters.sum_apply, if_neg hr]

end LocalFiveCharacterTable
end
end Stellmacher.Recognition.LyonsU3Four
