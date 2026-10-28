module

public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.LineGeometry

/-!
# Fixed vectors and displacement for a selected singular line

The Sylow intersection hypothesis makes the singular point fixed by the
Sylow group incident with the selected line. The fixed vectors are zero and
that point. An isometry fixing the line pointwise has all its displacement
in the line, and one such isometry in the Sylow group has displacement equal
to the whole line. The finite certificates use the existing 72 isometry
coordinates and are checked by the kernel.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.66(4)
and the orthogonal-space calculation used after 15.3.67, printed pp.1152--1153.
-/

@[expose] public section

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines
set_option synthInstance.maxSize 10000

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_fixed : ∀ x : Space, x ≠ 0 → q x = 0 → ∀ y : Space,
    (∀ k : Code, eval k x = x → eval k y = y) → y = 0 ∨ y = x := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_incidence : ∀ x : Space, x ≠ 0 → q x = 0 → ∀ i : LineCode,
    4 ≤ Fintype.card {k : Code // eval k x = x ∧ preservesGraph k i} →
      x.2 = planeEval i x.1 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_displacement : ∀ i : LineCode, ∀ k : Code,
    (∀ x : Space, x.2 = planeEval i x.1 → eval k x = x) →
    ∀ v : Space, (eval k v - v).2 = planeEval i (eval k v - v).1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_moves : ∀ i : LineCode, ∃ k : Code,
    (∀ x : Space, x.2 = planeEval i x.1 → eval k x = x) ∧
    ∀ w : Space, w.2 = planeEval i w.1 → ∃ v : Space, eval k v - v = w := by
  decide +kernel

private theorem point_line_incident (x : Space) (hx : x ≠ 0) (hqx : form x = 0)
    (i : LineCode)
    (hc : Nat.card (MulAction.stabilizer Actor x ⊓ lineStabilizer (graphLine i) :
      Subgroup Actor) = 4) : Multiplicative.ofAdd x ∈ graphLine i := by
  let e : {k : Code // eval k x = x ∧ preservesGraph k i} ≃
      (MulAction.stabilizer Actor x ⊓ lineStabilizer (graphLine i) : Subgroup Actor) :=
    codeEquiv.subtypeEquiv (fun k => by
      change (eval k x = x ∧ preservesGraph k i) ↔
        (candidate k x = x ∧ codeMap k ∈ lineStabilizer (graphLine i))
      rw [candidate_eval, codeMap_mem_line])
  have hcount : Fintype.card {k : Code // eval k x = x ∧ preservesGraph k i} = 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e, hc]
  change x.2 = planePermutation i x.1
  rw [planePermutation_eval]
  exact finite_incidence x hx hqx i (by omega)

/-- Every vector fixed by the Sylow group belongs to the selected singular line. -/
theorem line_sylow_fixed_mem (P : Sylow 2 Actor)
    (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0)
    (Q : Sylow 2 (lineStabilizer E))
    (hQ : (Q : Subgroup (lineStabilizer E)).map (lineStabilizer E).subtype =
      (P : Subgroup Actor) ⊓ lineStabilizer E)
    (w : Multiplicative Space) (hw : ∀ g ∈ (P : Subgroup Actor), vectorAction g w = w) :
    w ∈ E := by
  have hc := line_sylow_intersection_card P E hcard hs Q hQ
  obtain ⟨i,rfl⟩ := singular_four_eq_graph E hcard hs
  obtain ⟨x,hx,hqx,hP⟩ := sylow_eq_point_stabilizer P
  rw [hP] at hc hw
  have hy : w.toAdd = 0 ∨ w.toAdd = x := finite_fixed x hx hqx w.toAdd (by
    intro k hk
    rw [← candidate_eval]
    apply hw (codeMap k)
    change candidate k x = x
    rw [candidate_eval, hk])
  rcases hy with hy | hy
  · have he : w = 1 := hy
    exact he ▸ (graphLine i).one_mem
  · have he : w = Multiplicative.ofAdd x := hy
    exact he ▸ point_line_incident x hx hqx i hc

/-- Fixing a singular line pointwise puts every displacement in that line. -/
theorem line_pointwise_displacement_mem (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0)
    (g : Actor) (hg : ∀ w ∈ E, vectorAction g w = w)
    (v : Multiplicative Space) : vectorAction g v * v⁻¹ ∈ E := by
  obtain ⟨i,rfl⟩ := singular_four_eq_graph E hcard hs
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
  have hfix : ∀ x : Space, x.2 = planeEval i x.1 → eval k x = x := by
    intro x hx
    have h := hg (Multiplicative.ofAdd x) (by
      change x.2 = planePermutation i x.1
      rwa [planePermutation_eval])
    change candidate k x = x at h
    rwa [candidate_eval] at h
  change (candidate k v.toAdd + -v.toAdd).2 =
    planePermutation i (candidate k v.toAdd + -v.toAdd).1
  rw [candidate_eval, planePermutation_eval]
  simpa only [sub_eq_add_neg] using finite_displacement i k hfix v.toAdd

/-- A pointwise line fixer in the selected Sylow group moves onto the whole line. -/
theorem line_sylow_displacement_surjective (P : Sylow 2 Actor)
    (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ v ∈ E, form v.toAdd = 0)
    (Q : Sylow 2 (lineStabilizer E))
    (hQ : (Q : Subgroup (lineStabilizer E)).map (lineStabilizer E).subtype =
      (P : Subgroup Actor) ⊓ lineStabilizer E) :
    ∃ g ∈ (P : Subgroup Actor), (∀ w ∈ E, vectorAction g w = w) ∧
      ∀ w ∈ E, ∃ v : Multiplicative Space, vectorAction g v * v⁻¹ = w := by
  have hc := line_sylow_intersection_card P E hcard hs Q hQ
  obtain ⟨i,rfl⟩ := singular_four_eq_graph E hcard hs
  obtain ⟨x,hx,hqx,hP⟩ := sylow_eq_point_stabilizer P
  rw [hP] at hc ⊢
  have hxi := point_line_incident x hx hqx i hc
  change x.2 = planePermutation i x.1 at hxi
  rw [planePermutation_eval] at hxi
  obtain ⟨k,hfix,hmove⟩ := finite_moves i
  refine ⟨codeMap k, ?_, ?_, ?_⟩
  · change candidate k x = x
    rw [candidate_eval]
    exact hfix x hxi
  · intro w hw
    change w.toAdd.2 = planePermutation i w.toAdd.1 at hw
    rw [planePermutation_eval] at hw
    change candidate k w.toAdd = w.toAdd
    rw [candidate_eval]
    exact hfix w.toAdd hw
  · intro w hw
    change w.toAdd.2 = planePermutation i w.toAdd.1 at hw
    rw [planePermutation_eval] at hw
    obtain ⟨v,hv⟩ := hmove w.toAdd hw
    refine ⟨Multiplicative.ofAdd v, ?_⟩
    change candidate k v + -v = w.toAdd
    rw [candidate_eval]
    simpa only [sub_eq_add_neg] using hv

end OrthogonalFourBinary.SylowGeometry
