module

public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.LineGeometry
/-!
# Strict fixed-space bounds for the selected singular-line Sylow image

The selected line stabilizer is the Ω-part of a singular-point stabilizer,
with order four. A nonidentity element in it fixes four vectors; the whole
four-group fixes two. Hence every nontrivial subgroup has fixed-vector/order
product strictly less than sixteen. The two finite counts use the existing
bijection with the 72 actual quadratic isometries and are kernel checked.

This is the finite geometry needed for the maximum elementary family in
Aschbacher–Smith, 15.3.67, first paragraph of the proof, printed p.1153;
the selected Sylow intersection is 15.3.66, printed p.1152.
-/

@[expose] public section

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines
set_option synthInstance.maxSize 10000

/-- Vectors fixed by every member of an actual isometry subgroup. -/
abbrev FixedVectors (B : Subgroup Actor) :=
  {v : Space // ∀ g ∈ B, g.val v = v}

set_option maxRecDepth 10000 in
private theorem finite_involution_fixed : ∀ k : Code,
    (∃ v : Space, eval k v ≠ v) → k.1.2 = k.2.1.2 →
    (∀ v : Space, eval k (eval k v) = v) →
    Fintype.card {v : Space // eval k v = v} = 4 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem finite_point_omega_fixed : ∀ x : Space, x ≠ 0 → q x = 0 →
    Fintype.card {v : Space // ∀ k : Code,
      eval k x = x → k.1.2 = k.2.1.2 → eval k v = v} = 2 := by decide +kernel

private theorem involution_fixed_card (g : Actor) (hg : g ∈ omega)
    (hne : g ≠ 1) (h2 : g ^ 2 = 1) : Nat.card {v : Space // g.val v = v} = 4 := by
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
  change Nat.card {v : Space // candidate k v = v} = 4
  simp_rw [candidate_eval]
  rw [Nat.card_eq_fintype_card]
  refine finite_involution_fixed k ?_ ((codeMap_mem_omega k).mp hg) ?_
  · by_contra! h
    apply hne
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact (candidate_eval k v).trans (h v)
  · intro v
    have hh := congrArg (fun a : Actor => a.val v) h2
    change candidate k (candidate k v) = v at hh
    simpa only [candidate_eval] using hh

private theorem point_omega_fixed_card (x : Space) (hx : x ≠ 0) (hqx : form x = 0) :
    Nat.card (FixedVectors (MulAction.stabilizer Actor x ⊓ omega)) = 2 := by
  let e : FixedVectors (MulAction.stabilizer Actor x ⊓ omega) ≃
      {v : Space // ∀ k : Code,
        eval k x = x → k.1.2 = k.2.1.2 → eval k v = v} :=
    (Equiv.refl Space).subtypeEquiv (fun v => by
      constructor
      · intro h k hk hp
        rw [← candidate_eval]
        exact h (codeMap k) ⟨(candidate_eval k x).trans hk,
          (codeMap_mem_omega k).mpr hp⟩
      · intro h g hg
        obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
        change candidate k v = v
        rw [candidate_eval]
        exact h k ((candidate_eval k x).symm.trans hg.1)
          ((codeMap_mem_omega k).mp hg.2))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact finite_point_omega_fixed x hx hqx

/-- Every nontrivial subgroup of the selected singular-line Sylow image has
strictly smaller fixed-space/order product than the order of the natural module. -/
theorem line_sylow_strict_fixed_bound (P : Sylow 2 Actor)
    (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0)
    (Q : Sylow 2 (lineStabilizer E))
    (hQ : (Q : Subgroup (lineStabilizer E)).map (lineStabilizer E).subtype =
      (P : Subgroup Actor) ⊓ lineStabilizer E)
    (B : Subgroup Actor) (hB : B ≤ (P : Subgroup Actor) ⊓ lineStabilizer E)
    (hne : B ≠ ⊥) : Nat.card (FixedVectors B) * Nat.card B < 16 := by
  let H : Subgroup Actor := (P : Subgroup Actor) ⊓ lineStabilizer E
  have hc : Nat.card H = 4 := line_sylow_intersection_card P E hcard hs Q hQ
  have he : H = (P : Subgroup Actor) ⊓ omega :=
    line_sylow_intersection_eq_omega P E hcard hs Q hQ
  obtain ⟨x,hx,hqx,hP⟩ := sylow_eq_point_stabilizer P
  have hf : Nat.card (FixedVectors H) = 2 := by
    rw [he,hP]
    exact point_omega_fixed_card x hx hqx
  by_cases hBH : B = H
  · rw [hBH,hf,hc]
    decide
  · have hlt : Nat.card B < 4 := by
      rw [← hc]
      exact lt_of_le_of_ne (Subgroup.card_le_of_le hB)
        (fun h => hBH (Subgroup.eq_of_le_of_card_ge hB h.ge))
    obtain ⟨g,hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hgH : (g : Actor) ∈ MulAction.stabilizer Actor x ⊓ omega := by
      rw [← hP, ← he]
      exact hB g.property
    have hcg : Nat.card {v : Space // (g : Actor).val v = v} = 4 :=
      involution_fixed_card g hgH.2 (fun h => hg (Subtype.ext h))
        (point_omega_square x hx hqx g hgH)
    have hcf : Nat.card (FixedVectors B) ≤ 4 := by
      rw [← hcg]
      exact Nat.card_le_card_of_injective
        (fun v : FixedVectors B => (⟨v.val,v.property g g.property⟩ :
          {v : Space // (g : Actor).val v = v}))
        (fun a b h => Subtype.ext (congrArg
          (fun v : {v : Space // (g : Actor).val v = v} => v.val) h))
    calc
      Nat.card (FixedVectors B) * Nat.card B ≤ 4 * 3 :=
        Nat.mul_le_mul hcf (by omega)
      _ < 16 := by decide
end OrthogonalFourBinary.SylowGeometry
