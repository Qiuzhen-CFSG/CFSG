module

public import Theory.SpecificGroups.ReeTwo.FirstParabolic
public import Theory.SpecificGroups.ReeTwo.FirstParabolicCharacterAction
public import Theory.SpecificGroups.SymmetricFourSylowFixedPoint

/-!
# Character selection for automorphisms of the first Ree two parabolic core

The specified Sylow action contains all inner automorphisms of the core
and fixes every binary character restricted from the Sylow model. Thus a
compatible two-group fixes both alternative characters.

A four-point action supplies a smaller certificate than a full automorphism
census: if the specified Sylow action induces a transposition and its two
fixed points represent the core and mixed characters, one of those
characters is fixed by the whole compatible action. The characteristic
binary quotient constructs this action in `FirstParabolicCharacterAction`;
the final theorem below discharges all its structural inputs.

Source: the first parabolic subgroup in van Beek, *Fusion Systems and Rank 2
Simple Groups of Lie Type* (2024), Proposition 3.1, p. 10. The reductions
below use only conjugation, Lagrange's theorem, and Sylow's theorem.
-/

namespace ReeTwo.SylowModel

/-- Inner automorphisms of the actual first parabolic core. -/
@[expose] public def firstParabolicInner : Subgroup (MulAut firstParabolicCore) :=
  (MulAut.conj : firstParabolicCore →* MulAut firstParabolicCore).range

public instance firstParabolicInner_normal : firstParabolicInner.Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ a
  refine ⟨a x, ?_⟩
  apply MulEquiv.ext
  intro y
  simp [MulAut.mul_apply, MulAut.conj_apply]

/-- Conjugation by the core is part of the specified Sylow action. -/
public theorem firstParabolicInner_le_range :
    firstParabolicInner ≤ firstParabolicAction.range := by
  rintro _ ⟨x, rfl⟩
  refine ⟨x.val, ?_⟩
  apply MulEquiv.ext
  intro y
  rfl

/-- The specified Sylow action fixes the restriction of any binary character. -/
public theorem firstParabolicAction_preserves_character
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (a : MulAut firstParabolicCore) (ha : a ∈ firstParabolicAction.range)
    (x : firstParabolicCore) : χ (a x : SylowModel) = χ x := by
  obtain ⟨s, rfl⟩ := ha
  simp [map_mul, map_inv]

/-- The prescribed Sylow-image condition includes the whole specified action. -/
public theorem firstParabolicAction_range_le
    {A : Subgroup (MulAut firstParabolicCore)}
    (hA : ∃ P : Sylow 2 A,
      (P : Subgroup A).map A.subtype = firstParabolicAction.range) :
    firstParabolicAction.range ≤ A := by
  obtain ⟨P, hP⟩ := hA
  rw [← hP]
  exact Subgroup.map_subtype_le (P : Subgroup A)

/-- A compatible two-group has no automorphisms beyond the specified action. -/
public theorem firstParabolicAction_eq_of_isPGroup
    (A : Subgroup (MulAut firstParabolicCore)) (hA : IsPGroup 2 A)
    (hSylow : ∃ P : Sylow 2 A,
      (P : Subgroup A).map A.subtype = firstParabolicAction.range) :
    A = firstParabolicAction.range := by
  obtain ⟨P, hP⟩ := hSylow
  have htop : (P : Subgroup A) = ⊤ :=
    (P.is_maximal' (hA.to_subgroup ⊤) le_top).symm
  simpa [htop, ← MonoidHom.range_eq_map] using hP

/-- Both alternative characters are fixed in the compatible two-group case. -/
public theorem firstParabolic_characters_of_isPGroup
    (A : Subgroup (MulAut firstParabolicCore)) (hA : IsPGroup 2 A)
    (hSylow : ∃ P : Sylow 2 A,
      (P : Subgroup A).map A.subtype = firstParabolicAction.range) :
    (∀ a ∈ A, ∀ x : firstParabolicCore,
      coreCharacter (a x : SylowModel) = coreCharacter x) ∧
    (∀ a ∈ A, ∀ x : firstParabolicCore,
      mixedCharacter (a x : SylowModel) = mixedCharacter x) := by
  rw [firstParabolicAction_eq_of_isPGroup A hA hSylow]
  exact ⟨firstParabolicAction_preserves_character coreCharacter,
    firstParabolicAction_preserves_character mixedCharacter⟩

/-- Reduce character selection to the actual action on four characters. The
construction and character interpretation of this action are explicit inputs. -/
public theorem firstParabolic_character_selection_of_four_point_action
    (ρ : MulAut firstParabolicCore →* Equiv.Perm (Fin 4))
    (hρ : firstParabolicAction.range.map ρ =
      Subgroup.zpowers (Equiv.swap (2 : Fin 4) 3))
    (hcore : ∀ a : MulAut firstParabolicCore, ρ a 0 = 0 →
      ∀ x : firstParabolicCore, coreCharacter (a x : SylowModel) = coreCharacter x)
    (hmixed : ∀ a : MulAut firstParabolicCore, ρ a 1 = 1 →
      ∀ x : firstParabolicCore, mixedCharacter (a x : SylowModel) = mixedCharacter x)
    (A : Subgroup (MulAut firstParabolicCore))
    (hSylow : ∃ P : Sylow 2 A,
      (P : Subgroup A).map A.subtype = firstParabolicAction.range) :
    (∀ a ∈ A, ∀ x : firstParabolicCore,
      coreCharacter (a x : SylowModel) = coreCharacter x) ∨
    (∀ a ∈ A, ∀ x : firstParabolicCore,
      mixedCharacter (a x : SylowModel) = mixedCharacter x) := by
  obtain ⟨P, hP⟩ := hSylow
  have hmap : (P : Subgroup A).map (ρ.comp A.subtype) =
      Subgroup.zpowers (Equiv.swap (2 : Fin 4) 3) := by
    rw [← Subgroup.map_map, hP, hρ]
  rcases SymmetricFour.hom_fixes_zero_or_one_of_sylow_swap (ρ.comp A.subtype) P hmap with
    h | h
  · exact Or.inl (fun a ha => hcore a (h ⟨a, ha⟩))
  · exact Or.inr (fun a ha => hmixed a (h ⟨a, ha⟩))

/-- Every automorphism subgroup with the prescribed Sylow two-image preserves
one of the two alternative characters of the first parabolic core. -/
public theorem firstParabolic_character_selection
    (A : Subgroup (MulAut firstParabolicCore))
    (hSylow : ∃ P : Sylow 2 A,
      (P : Subgroup A).map A.subtype = firstParabolicAction.range) :
    (∀ a ∈ A, ∀ x : firstParabolicCore,
      coreCharacter (a x : SylowModel) = coreCharacter x) ∨
    (∀ a ∈ A, ∀ x : firstParabolicCore,
      mixedCharacter (a x : SylowModel) = mixedCharacter x) :=
  firstParabolic_character_selection_of_four_point_action
    firstParabolicCharacterAction firstParabolicCharacterAction_range_map
    firstParabolicCharacterAction_core_fixed firstParabolicCharacterAction_mixed_fixed A hSylow

end ReeTwo.SylowModel
