module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
The displayed point coordinates are adapted from ATLAS, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, through
Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.Geometry.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.BinaryMaps
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The unique invariant quadratic form of the binary A₈ module

The 28 nonsingular vectors are the duads. The alternating group is transitive
on them: a permutation taking one duad to another can have its parity corrected
by swapping the two source letters. Every nonzero singular vector is a sum of
three distinct duads through one point. The quadratic identity on those three
vectors shows that an invariant quadratic form vanishes there. Consequently
all invariant quadratic forms are scalar multiples of the split form, and an
invertible map normalizing the alternating action preserves that form.

The point coordinates and their deleted-module interpretation use the ATLAS
port cited above. Only certificates on the 64 vectors are checked finitely.
Source application: Aschbacher–Smith, K.3.2.2, printed p.455/PDF p.466,
and B.4.2(10), printed p.86/PDF p.97.
-/

noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.OrthogonalSix.Normalizer
open Atlas.Order20160A8 ClassicalOrthogonal
open DeletedEight
private abbrev D := VectorD 3 (ZMod 2)
private abbrev Q := formD 3 (ZMod 2)
private def point : Fin 8 → D := ![
  Sum.elim ![0,0,0] ![0,0,0],
  Sum.elim ![0,1,0] ![0,1,0],
  Sum.elim ![0,0,1] ![0,1,1],
  Sum.elim ![1,1,1] ![0,0,1],
  Sum.elim ![0,1,1] ![1,0,1],
  Sum.elim ![1,1,0] ![1,0,0],
  Sum.elim ![1,0,0] ![1,1,1],
  Sum.elim ![1,0,1] ![1,1,0]]
private def edge (i j : Fin 8) : D := point i + point j
private theorem edge_value : ∀ i j : Fin 8, Q (edge i j) = if i = j then 0 else 1 := by
  decide +kernel
-- These witnesses only describe the 64 vectors; no linear group is enumerated.
-- The two specifications below are checked by the kernel.
private def vectorIndex (x : D) : Fin 64 :=
  Fin.ofNat 64 ((x (.inl 0)).val + 2 * (x (.inl 1)).val + 4 * (x (.inl 2)).val +
    8 * (x (.inr 0)).val + 16 * (x (.inr 1)).val + 32 * (x (.inr 2)).val)
private def pairWitness : Fin 64 → Fin 8 × Fin 8 := ![
  (0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),
  (0,0),(3,4),(0,0),(0,5),(0,0),(2,6),(0,0),(1,7),
  (0,0),(0,0),(0,1),(2,3),(0,0),(0,0),(5,7),(4,6),
  (0,0),(1,5),(2,4),(0,0),(0,0),(0,7),(3,6),(0,0),
  (0,0),(0,0),(0,0),(0,0),(6,7),(4,5),(1,2),(0,3),
  (0,0),(2,7),(0,0),(1,6),(3,5),(0,0),(0,4),(0,0),
  (0,0),(0,0),(5,6),(4,7),(0,2),(1,3),(0,0),(0,0),
  (0,0),(0,6),(3,7),(0,0),(1,4),(0,0),(0,0),(2,5)]
private def tripleWitness : Fin 64 → Fin 8 × Fin 8 × Fin 8 := ![
  (0,0,0),(1,2,3),(3,4,5),(3,6,7),(1,5,7),(1,4,6),(2,5,6),(2,4,7),
  (1,2,4),(0,0,0),(4,6,7),(0,0,0),(1,3,6),(0,0,0),(2,3,7),(0,0,0),
  (2,6,7),(2,4,5),(0,0,0),(0,0,0),(3,4,7),(3,5,6),(0,0,0),(0,0,0),
  (2,3,5),(0,0,0),(0,0,0),(1,3,4),(4,5,6),(0,0,0),(0,0,0),(1,2,6),
  (1,5,6),(1,4,7),(2,5,7),(2,4,6),(0,0,0),(0,0,0),(0,0,0),(0,0,0),
  (1,3,7),(0,0,0),(2,3,6),(0,0,0),(0,0,0),(1,2,5),(0,0,0),(5,6,7),
  (3,4,6),(3,5,7),(0,0,0),(0,0,0),(0,0,0),(0,0,0),(1,6,7),(1,4,5),
  (4,5,7),(0,0,0),(0,0,0),(1,2,7),(0,0,0),(2,3,4),(1,3,5),(0,0,0)]
private theorem pairWitness_spec : ∀ x : D, Q x = 1 →
    let w := pairWitness (vectorIndex x)
    w.1 ≠ w.2 ∧ x = edge w.1 w.2 := by decide +kernel
private theorem tripleWitness_spec : ∀ x : D, Q x = 0 → x = 0 ∨
    let w := tripleWitness (vectorIndex x)
    w.1 ≠ 0 ∧ w.2.1 ≠ 0 ∧ w.2.2 ≠ 0 ∧ w.1 ≠ w.2.1 ∧ w.2.1 ≠ w.2.2 ∧
      w.2.2 ≠ w.1 ∧ x = point w.1 + point w.2.1 + point w.2.2 := by decide +kernel
private theorem nonsingular_exists (x : D) (hx : Q x = 1) :
    ∃ i j : Fin 8, i ≠ j ∧ x = edge i j :=
  ⟨_, _, pairWitness_spec x hx⟩
private theorem singular_exists (x : D) (hx : Q x = 0) : x = 0 ∨
    ∃ i j k : Fin 8, i ≠ 0 ∧ j ≠ 0 ∧ k ≠ 0 ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧
      x = point i + point j + point k := by
  rcases tripleWitness_spec x hx with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, _, _, h⟩
private theorem raw_point : ∀ i : Fin 8, raw (point i) = duadVector 0 i -
    (duadVector 0 i 7) • (fun _ : Fin 8 => (1 : ZMod 2)) := by
  decide +kernel
private theorem split_point (i : Fin 8) :
    splitEquiv (point i) = (Submodule.Quotient.mk (duad 0 i) : W) := by
  apply (Submodule.Quotient.eq constants).mpr
  apply Submodule.mem_span_singleton.mpr
  refine ⟨-(duadVector 0 i 7), ?_⟩
  apply Subtype.ext
  change -(duadVector 0 i 7) • (fun _ : Fin 8 => (1 : ZMod 2)) = raw (point i) - duadVector 0 i
  rw [raw_point]
  module
private theorem split_edge (i j : Fin 8) :
    splitEquiv (edge i j) = (Submodule.Quotient.mk (duad i j) : W) := by
  rw [edge, map_add, split_point, split_point, ← Submodule.Quotient.mk_add]
  congr 1
  apply Subtype.ext
  change duadVector 0 i + duadVector 0 j = duadVector i j
  funext k
  simp only [duadVector, Pi.add_apply]
  rw [add_add_add_comm, CharTwo.add_self_eq_zero, zero_add]
private theorem orthogonal_edge (p : Equiv.Perm (Fin 8)) (i j : Fin 8) :
    (orthogonalHom p).val (edge i j) = edge (p i) (p j) := by
  apply splitEquiv.injective
  change splitEquiv (splitEquiv.symm (quotientPerm p (splitEquiv (edge i j)))) = _
  rw [LinearEquiv.apply_symm_apply, split_edge, split_edge]
  change (Submodule.Quotient.mk (evenPerm p (duad i j)) : W) = _
  rw [duad_permute]
private theorem edge_transitive (q : QuadraticForm (ZMod 2) (VectorD 3 (ZMod 2)))
    (hinv : ∀ p : alternatingGroup (Fin 8), ∀ x,
      q ((orthogonalHom p.val).val x) = q x) (i j : Fin 8) (hij : i ≠ j) :
    q (edge i j) = q (edge 0 1) := by
  let p := Equiv.swap 0 i * Equiv.swap 1 (Equiv.swap 0 i j)
  have hp : p 0 = i ∧ p 1 = j := by
    have test : ∀ i j : Fin 8, i ≠ j →
        let p := Equiv.swap 0 i * Equiv.swap 1 (Equiv.swap 0 i j)
        p 0 = i ∧ p 1 = j := by decide +kernel
    exact test i j hij
  by_cases he : p ∈ alternatingGroup (Fin 8)
  · simpa only [orthogonal_edge, hp.1, hp.2] using hinv ⟨p, he⟩ (edge 0 1)
  · have hs : Equiv.Perm.sign p = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h
      · exact (he h).elim
      · exact h
    have he' : p * Equiv.swap 0 1 ∈ alternatingGroup (Fin 8) := by
      change Equiv.Perm.sign (p * Equiv.swap 0 1) = 1
      rw [map_mul, hs, Equiv.Perm.sign_swap (by decide)]
      decide
    have h := hinv ⟨p * Equiv.swap 0 1, he'⟩ (edge 0 1)
    rw [orthogonal_edge] at h
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, hp.1, hp.2, edge, add_comm] using h

/-- Every invariant quadratic form is a scalar multiple of the split form.
Duads have a common value; the three-vector quadratic identity makes every
singular vector have value zero. -/
private theorem invariant_form (q : QuadraticForm (ZMod 2) (VectorD 3 (ZMod 2)))
    (hinv : ∀ p : alternatingGroup (Fin 8), ∀ x,
      q ((orthogonalHom p.val).val x) = q x) :
    ∀ x, q x = q (edge 0 1) * formD 3 (ZMod 2) x := by
  intro x
  rcases Atlas.Codes.bit_cases (Q x) with hzero | hone
  · rw [hzero, mul_zero]
    rcases singular_exists x hzero with rfl | ⟨i,j,k,hi,hj,hk,hij,hjk,hki,rfl⟩
    · exact map_zero q
    · have hp (i : Fin 8) (hi : i ≠ 0) : q (point i) = q (edge 0 1) := by
        have h0 : point 0 = 0 := by decide +kernel
        simpa only [edge, h0, zero_add] using edge_transitive q hinv 0 i hi.symm
      have h := q.map_add_add_add_map (point i) (point j) (point k)
      change q (point i + point j + point k) + (q (point i) + q (point j) + q (point k)) =
        q (edge i j) + q (edge j k) + q (edge k i) at h
      rw [hp i hi, hp j hj, hp k hk, edge_transitive q hinv i j hij,
        edge_transitive q hinv j k hjk, edge_transitive q hinv k i hki] at h
      exact add_right_cancel (h.trans (zero_add _).symm)
  · obtain ⟨i,j,hij,rfl⟩ := nonsingular_exists x hone
    rw [edge_transitive q hinv i j hij, edge_value, if_neg hij, mul_one]

/-- An invertible linear map conjugating the alternating deleted action into itself
preserves the split quadratic form. No form-preservation premise is needed. -/
public theorem preserves_form (g : VectorD 3 (ZMod 2) ≃ₗ[ZMod 2] VectorD 3 (ZMod 2))
    (hconj : ∀ p : alternatingGroup (Fin 8), ∃ r : alternatingGroup (Fin 8),
      ∀ x, g ((orthogonalHom p.val).val x) = (orthogonalHom r.val).val (g x)) :
    ∀ x, formD 3 (ZMod 2) (g x) = formD 3 (ZMod 2) x := by
  have hi : ∀ p : alternatingGroup (Fin 8), ∀ x,
      (Q.comp g.toLinearMap) ((orthogonalHom p.val).val x) = (Q.comp g.toLinearMap) x := by
    intro p x
    obtain ⟨r, hr⟩ := hconj p
    change Q (g ((orthogonalHom p.val).val x)) = Q (g x)
    rw [hr]
    exact (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp
      (orthogonalHom r.val).property _
  have hq := invariant_form (Q.comp g.toLinearMap) hi
  have ha : Q (g (edge 0 1)) = 1 := by
    rcases Atlas.Codes.bit_cases (Q (g (edge 0 1))) with hzero | hone
    · have h := hq (g.symm (edge 0 1))
      change Q (g (g.symm (edge 0 1))) = Q (g (edge 0 1)) * Q (g.symm (edge 0 1)) at h
      rw [LinearEquiv.apply_symm_apply, edge_value, if_neg (by decide), hzero, zero_mul] at h
      exact (one_ne_zero h).elim
    · exact hone
  intro x
  change Q (g x) = Q x
  simpa only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, ha, one_mul] using hq x
end CFSG.Quasithin.ChapterK.Linear.OrthogonalSix.Normalizer
