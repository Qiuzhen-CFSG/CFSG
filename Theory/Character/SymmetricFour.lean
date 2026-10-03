module

public import Theory.Representation.SymmetricFour
public import Theory.Character.Orthogonality

/-!
# Completeness of the five constructed S₄ characters

The integer matrix representations give genuine characters. Their computed
norms are one, so they are irreducible. Their degrees and transposition values
distinguish them, and the five-class count proves completeness and identifies
them with any prescribed complete irreducible family.

Source: the ordinary S₄ character table, derived from the permutation modules;
see Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967), p. 71.
-/

public section

open scoped BigOperators
namespace SymmetricFourCharacters
open SymmetricFourClasses

/-- The conjugacy-class character afforded by each constructed representation. -/
noncomputable def character (i : Fin 5) : ConjClassFunction G := characterClassFunction (rep i)

theorem character_apply (i : Fin 5) (g : G) :
    character i (ConjClasses.mk g) = (table i (classIndex g) : ℂ) := rep_character i g

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem norm_check : ∀ i, ∑ g : G, table i (classIndex g) * table i (classIndex g) = 24 := by
  decide +kernel

/-- Each genuine character has norm one, hence is irreducible. -/
theorem character_irreducible (i : Fin 5) : IsIrreducibleConjCharacter (character i) := by
  refine ⟨⟨degree i, rep i, rfl⟩, ?_⟩
  have hs : (∑ g : G, (table i (classIndex g) : ℂ) * (table i (classIndex g) : ℂ)) = 24 := by
    exact_mod_cast norm_check i
  unfold classFunctionInner
  -- Compare the computational enumeration with the inner product’s finite instance.
  rw [Subsingleton.elim (Fintype.ofFinite G) (inferInstance : Fintype G)]
  simp only [character_apply, star_intCast]
  rw [hs]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial, G]

private theorem table_injective_check : ∀ i j, table i 0 = table j 0 → table i 1 = table j 1 → i = j := by
  decide +kernel

/-- Degrees and transposition values distinguish the five characters. -/
theorem character_injective : Function.Injective character := by
  intro i j h
  apply table_injective_check i j
  · have hv := congrFun h (ConjClasses.mk (1 : G))
    rw [character_apply, character_apply] at hv
    exact_mod_cast hv
  · have hv := congrFun h (ConjClasses.mk (Equiv.swap 0 1 : G))
    rw [character_apply, character_apply] at hv
    exact_mod_cast hv

private theorem completeFamily_card {I : Type*} [Fintype I]
    {χ : I → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ) :
    Fintype.card I = 5 := by
  classical
  obtain ⟨b, _⟩ := completeFamily_form_basis hχ
  rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card,
    ← Nat.card_eq_fintype_card, SymmetricFourClasses.card_conjClasses]

/-- Identify the five constructed characters with any prescribed complete family. -/
noncomputable def familyIndex {I : Type*} [Fintype I]
    {χ : I → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ) :
    Fin 5 ≃ I := by
  classical
  let f (i : Fin 5) : I := Classical.choose (hχ.2.1 (character i) (character_irreducible i))
  have hf (i) : χ (f i) = character i :=
    Classical.choose_spec (hχ.2.1 (character i) (character_irreducible i))
  refine Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨?_, ?_⟩)
  · intro i j hij
    apply character_injective
    rw [← hf i, ← hf j, hij]
  · rw [Fintype.card_fin, completeFamily_card hχ]

theorem familyIndex_apply {I : Type*} [Fintype I]
    {χ : I → ConjClassFunction G} (hχ : IsCompleteIrreducibleCharacterFamily χ) (i : Fin 5) :
    χ (familyIndex hχ i) = character i :=
  Classical.choose_spec (hχ.2.1 (character i) (character_irreducible i))

/-- The five explicitly afforded characters exhaust the ordinary irreducibles. -/
theorem character_complete : IsCompleteIrreducibleCharacterFamily character := by
  classical
  refine ⟨character_irreducible, ?_, character_injective⟩
  intro θ hθ
  obtain ⟨I, hI, χ, hχ, _⟩ := card_irreducible_characters_eq_card_conjClasses (G := G)
  let := hI
  obtain ⟨i, hi⟩ := hχ.2.1 θ hθ
  obtain ⟨j, rfl⟩ := (familyIndex hχ).surjective i
  exact ⟨j, (familyIndex_apply hχ j).symm.trans hi⟩

end SymmetricFourCharacters
