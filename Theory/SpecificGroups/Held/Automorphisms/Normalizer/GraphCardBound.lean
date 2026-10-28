module

public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound.Separation

/-!
# Cardinal bound for the full Held graph-preserving group

Fix the four vertices 0, 1, 2, 3 successively. Certified neighbor-sum
refinements bound the three subsequent orbit sizes by 425, 256, 36.
The pointwise four-point stabilizer is trivial, so orbit–stabilizer gives
2058 · 425 · 256 · 36 = 8060774400 for the full preserving group.

The relation is exactly the one published in `Normalizer/GraphData`, derived
from the ATLAS `HeG1-p2058B0` data; see `GraphCardBound/Source/README.md` for
the reproducible certificate. Orbital identification and normalizer containment
are separate results and are not hypotheses or conclusions of this bound.
-/

namespace Held.NormalizerGraph
open CardBound

private abbrev S0 := ↥preservingGroup
private abbrev S1 := ↥(MulAction.stabilizer S0 (0 : Fin 2058))
private abbrev S2 := ↥(MulAction.stabilizer S1 (1 : Fin 2058))
private abbrev S3 := ↥(MulAction.stabilizer S2 (2 : Fin 2058))
private abbrev S4 := ↥(MulAction.stabilizer S3 (3 : Fin 2058))

private theorem fix1 (g : S1) : Fixes 1 g.val.val := by
  intro x hx
  have he : x = 0 := Fin.ext (by omega)
  subst x
  exact g.property

private theorem fix2 (g : S2) : Fixes 2 g.val.val.val := by
  intro x hx
  by_cases h : x.val < 1
  · exact fix1 g.val x h
  · have he : x = 1 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix3 (g : S3) : Fixes 3 g.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 2
  · exact fix2 g.val x h
  · have he : x = 2 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix4 (g : S4) : Fixes 4 g.val.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 3
  · exact fix3 g.val x h
  · have he : x = 3 := Fin.ext (by omega)
    subst x
    exact g.property

/-- The full group of permutations preserving the specified Held relation has
at most twice the Held lower bound. All finite certificates are discharged. -/
public theorem card_preservingGroup_le :
    Nat.card preservingGroup ≤ 8060774400 := by
  have h4 : Nat.card S4 = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, fun g => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact four_fixed_eq_one _ g.val.val.val.val.property (fix4 g)
  have h3 : Nat.card S3 ≤ 36 * Nat.card S4 :=
    orbit_upper (3 : Fin 2058) (fun x => weight33 x.val)
      (fun g x => invariant33 _ g.val.val.val.property (fix3 g) x) cell3_card.le
  have h2 : Nat.card S2 ≤ 256 * Nat.card S3 :=
    orbit_upper (2 : Fin 2058) (fun x => weight22 x.val)
      (fun g x => invariant22 _ g.val.val.property (fix2 g) x) cell2_card.le
  have h1 : Nat.card S1 ≤ 425 * Nat.card S2 :=
    orbit_upper (1 : Fin 2058) (fun x => weight11 x.val)
      (fun g x => invariant11 _ g.val.property (fix1 g) x) cell1_card.le
  have h0 : Nat.card S0 ≤ 2058 * Nat.card S1 := by
    apply orbit_upper (0 : Fin 2058) (fun _ => 0) (fun _ _ => rfl)
    simpa only [Nat.card_fin] using
      Nat.card_le_card_of_injective
        (fun x : {x : Fin 2058 // (0 : ℕ) = 0} => x.val) Subtype.val_injective
  change Nat.card S0 ≤ 8060774400
  omega

end Held.NormalizerGraph
