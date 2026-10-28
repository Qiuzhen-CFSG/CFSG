module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveLinearCharacters
public import Theory.Character.CharacterKernel

/-!
# The quartic-character construction interfaces

The three nonidentity central elements index the degree-four Sylow characters.
Their central values distinguish their kernels. An extension is normalized to
be rational and to have value minus one on nonidentity odd-order elements;
its central multiplication formula records the corresponding scalar action.

These predicates specify the two construction steps in Lyons,
*A Characterization of the Group U₃(4)* (1972), pp. 373 and 381 (Lemma 4).
They assert no existence: construction modules must supply their witnesses.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
/-- The three possible kernels are indexed by nonidentity central elements. -/
abbrev QuarticCentralIndex {G : Type*} [Group G] (S : Sylow 2 G) :=
  {z : Subgroup.center S // z ≠ 1}
/-- The central scalar at a nonidentity central element. -/
def quarticCentralSign {G : Type*} [Group G] {S : Sylow 2 G}
    (z w : QuarticCentralIndex S) : ℂ := by
  classical
  exact if z = w then 1 else -1
@[simp] theorem quarticCentralSign_self {G : Type*} [Group G] {S : Sylow 2 G}
    (z : QuarticCentralIndex S) : quarticCentralSign z z = 1 := by
  simp [quarticCentralSign]
theorem quarticCentralIndex_card {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) : Nat.card (QuarticCentralIndex S) = 3 := by
  classical
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {z : Subgroup.center S // ¬ z = 1} = 3
  rw [Fintype.card_subtype_compl]
  simp [← Nat.card_eq_fintype_card, h.center_card]
/-- An actual irreducible Sylow character with the required complete value table. -/
structure IsSylowQuarticCharacter {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (z : QuarticCentralIndex S) (θ : ConjClassFunction S) : Prop where
  irreducible : IsIrreducibleConjCharacter θ
  value : ∀ s : S, θ (ConjClasses.mk s) =
    if s = 1 ∨ s = z.1.1 then 4 else if s ∈ Subgroup.center S then -4 else 0
/-- A normalized genuine extension, with its central scalar and odd-order values. -/
structure IsLocalFiveQuarticExtension {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (α : FiveComplement →* MulAut S) (z : QuarticCentralIndex S)
    (θ : ConjClassFunction S) (φ : ConjClassFunction (LocalFiveGroup S α)) : Prop where
  irreducible : IsIrreducibleConjCharacter φ
  restriction : ∀ s : S, φ (ConjClasses.mk (SemidirectProduct.inl s)) = θ (ConjClasses.mk s)
  rational : ∀ x, ∃ q : ℚ, φ (ConjClasses.mk x) = q
  odd_value : ∀ u, Odd (orderOf u) → u ≠ 1 → φ (ConjClasses.mk u) = -1
  central_mul : ∀ (w : QuarticCentralIndex S) x,
    φ (ConjClasses.mk (SemidirectProduct.inl w.1.1 * x)) =
      quarticCentralSign z w * φ (ConjClasses.mk x)

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}

/-- The value table determines an actual degree-four realization and its exact kernel. -/
theorem IsSylowQuarticCharacter.exists_representation (h : SylowStructure S)
    {z : QuarticCentralIndex S} {θ : ConjClassFunction S}
    (hθ : IsSylowQuarticCharacter S z θ) :
    ∃ ρ : Representation ℂ S (Fin 4 → ℂ), Representation.IsIrreducible ρ ∧
      θ = characterClassFunction ρ ∧ ρ.ker = Subgroup.zpowers z.1.1 := by
  classical
  obtain ⟨n, ρ, hr⟩ := hθ.irreducible.1
  have hi : Representation.IsIrreducible ρ :=
    (irreducible_iff_character_norm_one ρ).mpr (hr ▸ hθ.irreducible.2)
  have hn : n = 4 := by
    have hd := hθ.value 1
    rw [hr] at hd
    change ρ.character 1 = _ at hd
    simp only [Representation.char_one, Module.finrank_fin_fun] at hd
    exact_mod_cast (by simpa using hd : (n : ℂ) = 4)
  subst n
  refine ⟨ρ, hi, hr, ?_⟩
  have hz1 : z.1.1 ≠ (1 : S) := fun hh => z.2 (Subtype.ext hh)
  have hz2 : orderOf z.1.1 = 2 := by
    let := h.center_elementary
    exact orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian z.1.1 z.1.2) hz1
  ext s
  rw [ρ.mem_ker_iff_character_eq_degree]
  change characterClassFunction ρ (ConjClasses.mk s) =
    characterClassFunction ρ (ConjClasses.mk 1) ↔ _
  rw [← hr, hθ.value s, hθ.value 1]
  have hm : s ∈ Subgroup.zpowers z.1.1 ↔ s = 1 ∨ s = z.1.1 := by
    rw [mem_zpowers_iff_mem_range_orderOf, hz2]
    constructor
    · intro hs
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hs
      have hklt : k < 2 := Finset.mem_range.mp hk
      interval_cases k <;> simp
    · rintro (rfl | rfl)
      · exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
      · exact Finset.mem_image.mpr ⟨1, by simp, by simp⟩
  rw [hm]
  by_cases hs : s = 1 ∨ s = z.1.1
  · simp [hs]
  · by_cases hc : s ∈ Subgroup.center S <;> norm_num [hs, hc]

/-- The complete value table determines the Sylow character uniquely. -/
theorem IsSylowQuarticCharacter.unique {z : QuarticCentralIndex S}
    {θ ψ : ConjClassFunction S} (hθ : IsSylowQuarticCharacter S z θ)
    (hψ : IsSylowQuarticCharacter S z ψ) : θ = ψ := by
  ext c
  obtain ⟨s, rfl⟩ := ConjClasses.exists_rep c
  rw [hθ.value, hψ.value]

/-- The specified character vanishes off the center. -/
theorem IsSylowQuarticCharacter.vanishes {z : QuarticCentralIndex S}
    {θ : ConjClassFunction S} (hθ : IsSylowQuarticCharacter S z θ)
    {s : S} (hs : s ∉ Subgroup.center S) : θ (ConjClasses.mk s) = 0 := by
  have hs1 : s ≠ 1 := fun he => hs (he ▸ (Subgroup.center S).one_mem)
  have hsz : s ≠ z.1.1 := fun he => hs (he ▸ z.1.2)
  simp [hθ.value, hs1, hsz, hs]

/-- Every automorphism fixing the center pointwise fixes the quartic character. -/
theorem IsSylowQuarticCharacter.invariant_of_fixes_center {z : QuarticCentralIndex S}
    {θ : ConjClassFunction S} (hθ : IsSylowQuarticCharacter S z θ)
    (f : MulAut S) (hf : ∀ c : Subgroup.center S, f c = c) (s : S) :
    θ (ConjClasses.mk (f s)) = θ (ConjClasses.mk s) := by
  by_cases hs : s ∈ Subgroup.center S
  · rw [hf ⟨s, hs⟩]
  · have hfs : f s ∉ Subgroup.center S := by
      intro hc
      have he : f s = s := f.injective (hf ⟨f s, hc⟩)
      exact hs (he ▸ hc)
    rw [hθ.vanishes hs, hθ.vanishes hfs]

end
end Stellmacher.Recognition.LyonsU3Four
