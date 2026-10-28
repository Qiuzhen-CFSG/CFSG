module
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.FixedOrderBound.Support

/-!
# The four-point centralizer chain

Invariant cells at 0, 1, 2 and 3 bound the corresponding point orbits.
The established four-point base for the entire graph group terminates the
chain. Source: the ATLAS Held relation used for GLS3 Table 5.3p.
-/

namespace Held.OuterInvolution.FixedStructure.FixedOrderBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound

private abbrev S0 := ↥graphCentralizer
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

public theorem card_le_of_cells (w : Fin 4 → ℕ → ℕ) (c : Fin 4 → ℕ)
    (hw : ∀ n, Invariant n.val (w n))
    (hc : ∀ n, Nat.card {x : Fin 2058 // w n x.val = w n n.val} ≤ c n) :
    Nat.card graphCentralizer ≤ c 0 * (c 1 * (c 2 * c 3)) := by
  have h4 : Nat.card S4 = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, fun g => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact four_fixed_eq_one _ g.val.val.val.val.property.1 (fix4 g)
  have h3 : Nat.card S3 ≤ c 3 * Nat.card S4 :=
    orbit_upper (3 : Fin 2058) (fun x => w 3 x.val)
      (fun g x => hw 3 _ g.val.val.val.property (fix3 g) x) (hc 3)
  have h2 : Nat.card S2 ≤ c 2 * Nat.card S3 :=
    orbit_upper (2 : Fin 2058) (fun x => w 2 x.val)
      (fun g x => hw 2 _ g.val.val.property (fix2 g) x) (hc 2)
  have h1 : Nat.card S1 ≤ c 1 * Nat.card S2 :=
    orbit_upper (1 : Fin 2058) (fun x => w 1 x.val)
      (fun g x => hw 1 _ g.val.property (fix1 g) x) (hc 1)
  have h0 : Nat.card S0 ≤ c 0 * Nat.card S1 :=
    orbit_upper (0 : Fin 2058) (fun x => w 0 x.val)
      (fun g x => hw 0 _ g.property (by intro x hx; omega) x) (hc 0)
  rw [h4, mul_one] at h3
  exact h0.trans (Nat.mul_le_mul_left _
    (h1.trans (Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ h3)))))

end Held.OuterInvolution.FixedStructure.FixedOrderBound
