module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.WeightCone.Core
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Geometry

/-!
# Positive root characters are nonnegative simple-root products

Induction on the realized integral height decomposes each nonsimple positive
root into two positive roots. Character multiplication then puts it in the
simple-root monoid. Inverting characters gives the direct-conjugation version
while preserving the actual positive root groups.

Source: the positive-system and simple-root definitions of GLS3 §1.9.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.WeightCone
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}

/-- The positive-root cone follows from realized height and addition, without
an assumed root-coordinate comparison. -/
theorem positive_root_character_mem (D : RootGroupData K T) (hD : D.IsRealization)
    (f : TorusWeight T →* TorusWeight T) (M : Submonoid (TorusWeight T))
    (hsimple : ∀ a ∈ D.simple, f (D.rootWeight a) ∈ M)
    (a : D.Root) (ha : a ∈ D.positive) : f (D.rootWeight a) ∈ M := by
  obtain ⟨_, _, _, _, hadd, _, _, _, _, hheight, hpositive, hsimpleIff, _⟩ := hD
  have aux : ∀ n (a : D.Root), (D.height a).toNat = n → a ∈ D.positive →
      f (D.rootWeight a) ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a han ha
      by_cases hs : a ∈ D.simple
      · exact hsimple a hs
      have hsplit : ∃ b c, D.add b c = some a ∧ b ∈ D.positive ∧ c ∈ D.positive := by
        by_contra hn
        apply hs
        refine (hsimpleIff a).mpr ⟨ha, ?_⟩
        intro b c hbc hpos
        exact hn ⟨b, c, hbc, hpos⟩
      obtain ⟨b, c, hbc, hb, hc⟩ := hsplit
      have hbpos : 0 < D.height b := by simpa [hpositive] using hb
      have hcpos : 0 < D.height c := by simpa [hpositive] using hc
      have habc := hheight b c a hbc
      have hbM := ih (D.height b).toNat (by omega) b rfl hb
      have hcM := ih (D.height c).toNat (by omega) c rfl hc
      rw [hadd b c a hbc, map_mul]
      exact M.mul_mem hbM hcM
  exact aux _ a rfl ha

variable [CharP k 2]

/-- Direct simple-root eigencharacters, with the raw positive roots unchanged. -/
def simpleCharacter (S : Geometry K) (i : Fin 4) : TorusWeight S.torus :=
  (S.roots.rootWeight (S.simpleRoot i).val)⁻¹

/-- Raw negative-root characters belong to the direct positive simple cone. -/
theorem negative_root_mem_cone (S : Geometry K) (a : S.roots.Root)
    (ha : a ∈ S.roots.neg ⁻¹' S.roots.positive) :
    S.roots.rootWeight a ∈ characterCone (simpleCharacter S) := by
  have h := positive_root_character_mem S.roots S.realized (invMonoidHom : TorusWeight S.torus →* TorusWeight S.torus)
    (characterCone (simpleCharacter S)) (fun b hb => ?_) (S.roots.neg a) ha
  · simpa only [invMonoidHom_apply, S.realized.2.2.2.1, inv_inv] using h
  · obtain ⟨i, hi⟩ := S.simpleRoot.surjective ⟨b, hb⟩
    have hi' : (S.simpleRoot i).val = b := congrArg Subtype.val hi
    rw [← hi']
    exact characterCone_generator (simpleCharacter S) i

/-- Raw positive-root characters belong to the opposite simple cone. -/
theorem positive_root_mem_opposite_cone (S : Geometry K) (a : S.roots.Root)
    (ha : a ∈ S.roots.positive) :
    S.roots.rootWeight a ∈ characterCone (fun i => (simpleCharacter S i)⁻¹) := by
  apply positive_root_character_mem S.roots S.realized (MonoidHom.id _)
    (characterCone (fun i => (simpleCharacter S i)⁻¹)) _ a ha
  intro b hb
  obtain ⟨i, hi⟩ := S.simpleRoot.surjective ⟨b, hb⟩
  have hi' : (S.simpleRoot i).val = b := congrArg Subtype.val hi
  rw [← hi']
  simpa only [MonoidHom.id_apply, simpleCharacter, inv_inv] using
    characterCone_generator (fun i => (simpleCharacter S i)⁻¹) i

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.WeightCone
