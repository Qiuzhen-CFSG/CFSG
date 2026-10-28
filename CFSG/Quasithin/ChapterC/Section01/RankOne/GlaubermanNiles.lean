module

public import Theory.GroupTheory.PGroup.CharacteristicPairReduction

/-!
# The characteristic-pair reduction for Glauberman–Niles

Given the characteristic pair on B = Baum(S), C.1.19 prescribes
C₁(S) = Z(S) ∩ C₁(B) and C₂(S) = C₂(B). The second subgroup is kept
intrinsically in B, and is mapped explicitly whenever used in S or an
overgroup of B. This proves the structural and alternative-transfer parts
of that reduction. It does not assert the existence theorem C.1.18:
the universal pair on a Baumann-fixed group remains an upstream obligation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), C.1.18–C.1.20, pp.126–127. The source attributes
the existence theorem to Glauberman–Niles (1983) and Campbell (1979).
-/

public section

namespace CFSG.Quasithin.ChapterC

variable {S : Type*} [Group S]

/-- The structural part of a characteristic pair relative to B ≤ S.
The universal pushing-up alternatives are a separate assertion. -/
structure RankOneCharacteristicPair (B : Subgroup S) where
  first : Subgroup S
  second : Subgroup B
  first_characteristic : first.Characteristic
  second_characteristic : second.Characteristic
  first_ne_bot : first ≠ ⊥
  second_ne_bot : second ≠ ⊥
  first_le_omega : first ≤
    (omega₁ (Subgroup.center S) (p := 2)).map (Subgroup.center S).subtype
  first_le_base : first ≤ B

/-- Both members are characteristic in S; the second is also characteristic
in B by construction, as required by C.1.18. -/
theorem RankOneCharacteristicPair.second_image_characteristic
    {B : Subgroup S} [B.Characteristic] (C : RankOneCharacteristicPair B) :
    (C.second.map B.subtype).Characteristic := by
  let := C.second_characteristic
  infer_instance

/-- The intrinsic second member stays nontrivial in the ambient group. -/
theorem RankOneCharacteristicPair.second_image_ne_bot
    {B : Subgroup S} (C : RankOneCharacteristicPair B) :
    C.second.map B.subtype ≠ ⊥ := by
  intro h
  exact C.second_ne_bot ((C.second.map_eq_bot_iff_of_injective B.subtype_injective).mp h)

/-- C.1.19's construction from the two characteristic subgroups on B.
Its use with B = Baum(S) requires the upstream existence theorem on B. -/
@[expose] def glaubermanNiles_reducePair [Finite S] (hS : IsPGroup 2 S)
    (B : Subgroup S) [B.Characteristic]
    (D₁ D₂ : Subgroup B) [D₁.Characteristic] [D₂.Characteristic]
    (h₁ : D₁ ≠ ⊥) (h₂ : D₂ ≠ ⊥)
    (hω : D₁ ≤ (omega₁ (Subgroup.center B) (p := 2)).map (Subgroup.center B).subtype) :
    RankOneCharacteristicPair B := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hspec := Subgroup.centerRestriction_spec hS B D₁ h₁ hω
  exact ⟨Subgroup.centerRestriction B D₁, D₂, hspec.1, inferInstance,
    hspec.2.1, h₂, hspec.2.2, Subgroup.centerRestriction_le B D₁⟩

/-- The first identity prescribed in C.1.20, with the intrinsic image explicit. -/
theorem glaubermanNiles_reducePair_first [Finite S] (hS : IsPGroup 2 S)
    (B : Subgroup S) [B.Characteristic]
    (D₁ D₂ : Subgroup B) [D₁.Characteristic] [D₂.Characteristic]
    (h₁ : D₁ ≠ ⊥) (h₂ : D₂ ≠ ⊥)
    (hω : D₁ ≤ (omega₁ (Subgroup.center B) (p := 2)).map (Subgroup.center B).subtype) :
    (glaubermanNiles_reducePair hS B D₁ D₂ h₁ h₂ hω).first =
      Subgroup.center S ⊓ D₁.map B.subtype := rfl

/-- The second identity prescribed in C.1.20 is literal on intrinsic subgroups. -/
theorem glaubermanNiles_reducePair_second [Finite S] (hS : IsPGroup 2 S)
    (B : Subgroup S) [B.Characteristic]
    (D₁ D₂ : Subgroup B) [D₁.Characteristic] [D₂.Characteristic]
    (h₁ : D₁ ≠ ⊥) (h₂ : D₂ ≠ ⊥)
    (hω : D₁ ≤ (omega₁ (Subgroup.center B) (p := 2)).map (Subgroup.center B).subtype) :
    (glaubermanNiles_reducePair hS B D₁ D₂ h₁ h₂ hω).second = D₂ := rfl

/-- The structural clauses alone have witnesses exactly when B is nontrivial.
This does not supply the universal alternatives of the existence theorem. -/
theorem nonempty_rankOneCharacteristicPair_iff [Finite S] (hS : IsPGroup 2 S)
    (B : Subgroup S) [B.Characteristic] :
    Nonempty (RankOneCharacteristicPair B) ↔ B ≠ ⊥ := by
  constructor
  · rintro ⟨C⟩ hB
    exact C.first_ne_bot (bot_unique (hB ▸ C.first_le_base))
  · intro hB
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).mpr hB
    let D := (omega₁ (Subgroup.center B) (p := 2)).map (Subgroup.center B).subtype
    let : (omega₁ (Subgroup.center B) (p := 2)).Characteristic := omega₁_characteristic _
    let : D.Characteristic := inferInstance
    have hD : D ≠ ⊥ := Subgroup.omega_center_ne_bot (hS.to_subgroup B)
    exact ⟨glaubermanNiles_reducePair hS B D D hD hD le_rfl⟩

/-- Transfer all three alternatives under the C.1.19 construction.
The exceptional proposition will be the two block alternatives of C.1.18.
An embedding of B in H suffices: S need not be a subgroup of H. -/
theorem glaubermanNiles_reduction_alternatives
    (B : Subgroup S) (D₁ D₂ : Subgroup B)
    {H : Type*} [Group H] (e : B →* H) (exceptional : Prop)
    (h : D₁.map e ≤ Subgroup.center H ∨ (D₂.map e).Normal ∨ exceptional) :
    ((Subgroup.centerRestriction B D₁).subgroupOf B).map e ≤ Subgroup.center H ∨
      (((D₂.map B.subtype).subgroupOf B).map e).Normal ∨ exceptional := by
  rcases h with hcentral | hnormal | hexc
  · exact Or.inl ((Subgroup.map_mono
      (Subgroup.centerRestriction_subgroupOf_le B D₁)).trans hcentral)
  · exact Or.inr (Or.inl (by rwa [Subgroup.image_subgroupOf_subtype]))
  · exact Or.inr (Or.inr hexc)

end CFSG.Quasithin.ChapterC
