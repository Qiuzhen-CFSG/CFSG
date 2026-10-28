module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Fusion.Witnesses
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# Seven-coordinate fusion from generator certificates

The checked finite orbit table reduces all 342 nonidentity normal forms to
X, Y, XY and Z. Multiplicativity transports the three generator images of
each normalizing word to every coordinate. Three ambient fusion identities
and the Z-to-Y bridge then give representative indices 3 or 4, with power one.
The concrete matrix obligations are `Fusion.NormalizerIdentities` and
`Fusion.RootIdentities`; they remain explicit in this assembly theorem.

Witness provenance and the exact conjugation convention are documented in
`Seven/Fusion/Orbit.lean` and `Seven/Fusion/Witnesses.lean`.
-/

namespace ONan.Simplicity.Seven
namespace Fusion

private theorem evaluate_basis_zero : evaluate (basis 0) = generatorX := evaluate_x
private theorem evaluate_basis_one : evaluate (basis 1) = generatorY := evaluate_y
private theorem evaluate_basis_two : evaluate (basis 2) = generatorZ := by
  change generatorX ^ 0 * generatorY ^ 0 * generatorZ ^ 1 = generatorZ
  simp

private theorem coordinate_inner_images (j r : Fin 3) :
    (basis j)⁻¹ * basis r * basis j = generatorImage ⟨j.val, by omega⟩ r := by
  fin_cases j <;> fin_cases r <;> apply Coordinates.ext <;> decide +kernel

private theorem first_normalizer (j : Fin 3) :
    normalizer ⟨j.val, by omega⟩ = evaluate (basis j) := by
  fin_cases j
  · exact evaluate_basis_zero.symm
  · exact evaluate_basis_one.symm
  · exact evaluate_basis_two.symm

/-- Multiplicativity proves the nine inner-generator equations, leaving only
the six equations for the two additional normalizing words. -/
public theorem normalizer_identities_of_extra
    (hmul : ∀ s t, evaluate (s * t) = evaluate s * evaluate t)
    (hextra : ∀ (j : Fin 5) (r : Fin 3), 3 ≤ j.val →
      (normalizer j)⁻¹ * evaluate (basis r) * normalizer j =
        evaluate (generatorImage j r)) : NormalizerIdentities := by
  have hinner (j r : Fin 3) :
      (normalizer ⟨j.val, by omega⟩)⁻¹ * evaluate (basis r) *
          normalizer ⟨j.val, by omega⟩ = evaluate (generatorImage ⟨j.val, by omega⟩ r) := by
    rw [first_normalizer, ← coordinate_inner_images j r, hmul, hmul]
    rw [show evaluate ((basis j)⁻¹) = (evaluate (basis j))⁻¹ from
      (coordinateHom hmul).map_inv (basis j)]
  intro j r
  fin_cases j
  · exact hinner 0 r
  · exact hinner 1 r
  · exact hinner 2 r
  · exact hextra 3 r (by decide)
  · exact hextra 4 r (by decide)

/-- Three generator equations transport each substitution to every coordinate. -/
public theorem evaluate_step
    (hmul : ∀ s t, evaluate (s * t) = evaluate s * evaluate t)
    (hn : NormalizerIdentities) (j : Fin 5) (t : Coordinates) :
    evaluate (step j t) = (normalizer j)⁻¹ * evaluate t * normalizer j := by
  let f : Model →* Model := (MulAut.conj (normalizer j)⁻¹).toMonoidHom
  have hf (v : Model) : f v = (normalizer j)⁻¹ * v * normalizer j := by
    simp only [f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hx : evaluate (generatorImage j 0) = f generatorX := by
    rw [hf, ← evaluate_basis_zero]
    exact (hn j 0).symm
  have hy : evaluate (generatorImage j 1) = f generatorY := by
    rw [hf, ← evaluate_basis_one]
    exact (hn j 1).symm
  have hz : evaluate (generatorImage j 2) = f generatorZ := by
    rw [hf, ← evaluate_basis_two]
    exact (hn j 2).symm
  have hp (s : Coordinates) (n : ℕ) : evaluate (s ^ n) = evaluate s ^ n :=
    (coordinateHom hmul).map_pow s n
  calc
    evaluate (step j t) = (f generatorX) ^ t.a.val * (f generatorY) ^ t.b.val *
        (f generatorZ) ^ t.c.val := by
      rw [step, hmul, hmul, hp, hp, hp, hx, hy, hz]
    _ = f (evaluate t) := by simp only [evaluate, map_mul, map_pow]
    _ = _ := hf _

/-- Actual conjugating word attached to a finite coordinate path. -/
@[expose] public def pathWord (w : List (Fin 5)) : Model := (w.map normalizer).prod

/-- Successive coordinate substitutions are conjugation by the path product. -/
public theorem evaluate_walk
    (hmul : ∀ s t, evaluate (s * t) = evaluate s * evaluate t)
    (hn : NormalizerIdentities) (t : Coordinates) (w : List (Fin 5)) :
    evaluate (walk t w) = (pathWord w)⁻¹ * evaluate t * pathWord w := by
  induction w generalizing t with
  | nil => simp [walk, pathWord]
  | cons j js ih =>
    rw [walk, ih, evaluate_step hmul hn]
    simp only [pathWord, List.map_cons, List.prod_cons]
    group

/-- The four orbit origins are covered by the two specified representatives. -/
public theorem origin_coverage (hr : RootIdentities) (r : Fin 4) :
    ∃ (i : Fin 8) (g : Model), (i = 3 ∨ i = 4) ∧
      primeRepresentative i = g * evaluate (origin r) * g⁻¹ := by
  fin_cases r
  · exact ⟨3, rootConjugator 0, Or.inl rfl, hr.roots 0⟩
  · exact ⟨3, rootConjugator 1, Or.inl rfl, hr.roots 1⟩
  · exact ⟨4, rootConjugator 2, Or.inr rfl, hr.roots 2⟩
  · refine ⟨3, rootConjugator 1 * centralBridge⁻¹, Or.inl rfl, ?_⟩
    have h := hr.roots 1
    change primeRepresentative 3 = rootConjugator 1 * evaluate (basis 1) *
      (rootConjugator 1)⁻¹ at h
    rw [evaluate_basis_one, ← hr.central] at h
    change primeRepresentative 3 = _ * evaluate (basis 2) * _
    rw [evaluate_basis_two, h]
    group

end Fusion

/-- Assemble finite orbit coverage with the concrete generator and root identities.
The only power required by these certificates is one. -/
public theorem coordinate_coverage_of_fusion_certificates
    (hmul : ∀ s t, evaluate (s * t) = evaluate s * evaluate t)
    (hn : Fusion.NormalizerIdentities) (hr : Fusion.RootIdentities)
    (t : Coordinates) (ht : t ≠ 1) :
    ∃ (i : Fin 8) (k : ℕ) (g : Model), (i = 3 ∨ i = 4) ∧
      primeRepresentative i = g * evaluate t ^ k * g⁻¹ := by
  let r := (Fusion.pathTable (Fusion.index t)).1
  let w := (Fusion.pathTable (Fusion.index t)).2
  have hw : Fusion.walk (Fusion.origin r) w = t := Fusion.walk_pathTable t ht
  have he := Fusion.evaluate_walk hmul hn (Fusion.origin r) w
  rw [hw] at he
  obtain ⟨i, g, hi, hg⟩ := Fusion.origin_coverage hr r
  refine ⟨i, 1, g * Fusion.pathWord w, hi, ?_⟩
  rw [pow_one, hg, he]
  group

end ONan.Simplicity.Seven
