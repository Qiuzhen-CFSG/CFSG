module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables

/-!
# Inverse certificates for the eight cached ambient actions

A left inverse identity on every ambient point suffices once the forward
function is interpreted as the genuine model permutation. The strict evaluator
forces the inner table lookup before the outer one. No permutation property of
an unverified table is assumed.
Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v, and the retained word DAG.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges.MapComparison

/-- The padding is reduced modulo the full degree, never a restriction orbit. -/
def inverseTest (i : Fin 8) (x : Nat) : Bool :=
  force (cachedMaps i true (x % 306936)) (cachedMaps i false) == x % 306936

/-- All eight left inverse identities on the original ambient set. -/
def InverseChecks : Prop :=
  ∀ (i : Fin 8) (x : Fin 306936), inverseTest i x.val = true

/-- Invert a genuine permutation using a checked numerical left inverse. -/
theorem backward_eq_of_forward_inverse
    (p : Ambient) (f g : Nat → Nat)
    (hf : ∀ x : Fin 306936, f x.val = (p x).val)
    (hg : ∀ x : Fin 306936, g (f x.val) = x.val)
    (x : Fin 306936) : g x.val = (p⁻¹ x).val := by
  have h := hg (p⁻¹ x)
  rw [hf] at h
  have he : p (p⁻¹ x) = x := p.apply_symm_apply x
  rwa [he] at h

/-- The signed comparison uses precisely the positive comparisons and inverse checks. -/
theorem mapsCorrect_of_forward_inverse
    (hf : ∀ (i : Fin 8) (x : Fin 306936),
      cachedMaps i true x.val = (literal i x).val)
    (hi : InverseChecks) : MapsCorrect cachedMaps := by
  rintro ⟨i, b⟩ x
  cases b
  · apply backward_eq_of_forward_inverse (literal i)
      (cachedMaps i true) (cachedMaps i false) (hf i) ?_ x
    intro y
    have h := hi i y
    simpa only [inverseTest, force_eq, Nat.mod_eq_of_lt y.isLt, beq_iff_eq] using h
  · exact hf i x

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges.MapComparison
