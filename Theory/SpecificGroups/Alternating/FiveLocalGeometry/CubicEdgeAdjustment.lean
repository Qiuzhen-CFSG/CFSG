module
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicEdges
public import Mathlib.Data.Fintype.Perm

/-!
# Aligning an edge while retaining the cubic normalizer in A₅

The transposition of the two letters fixed by a cubic centralizes its
whole S₃ normalizer. This automorphism interchanges the two triples of
adjacent cubics; conjugation inside the cubic is transitive on each triple.
Transporting this six-element calculation aligns a prescribed neighbor
without changing the overlap map, except for the final inner adjustment.
The J₂ source comparison applies the same inner adjustment to both local maps.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267.
-/

public section
open Subgroup
namespace alternatingGroup.FiveLocalGeometry.CubicEdges
private def flipAut : MulAut A5 := MulAut.conjNormal (Equiv.swap 3 4)

private theorem flipAut_fixes (g : A5) (hg : g ∈ normalizer (C 0 : Set A5)) :
    flipAut g = g := by
  have hc : ∀ g : A5,
      (g * cycle 0 * g⁻¹ = 1 ∨ g * cycle 0 * g⁻¹ = cycle 0 ∨
        g * cycle 0 * g⁻¹ = (cycle 0)⁻¹) → flipAut g = g := by decide +kernel
  exact hc g ((mem_C _ _).mp ((hg _).mp (mem_zpowers _)))

private theorem six_neighbors (i : Fin 10) (hi : representative i = 1) :
    ∃ n : Fin 3, ∃ j : Fin 2,
      cycle 0 ^ n.val * (flipAut ^ j.val) (cycle i) * (cycle 0 ^ n.val)⁻¹ = cycle 1 ∨
      cycle 0 ^ n.val * (flipAut ^ j.val) (cycle i) * (cycle 0 ^ n.val)⁻¹ = (cycle 1)⁻¹ := by
  have h : ∀ i : Fin 10, representative i = 1 →
      ∃ n : Fin 3, ∃ j : Fin 2,
        cycle 0 ^ n.val * (flipAut ^ j.val) (cycle i) * (cycle 0 ^ n.val)⁻¹ = cycle 1 ∨
        cycle 0 ^ n.val * (flipAut ^ j.val) (cycle i) * (cycle 0 ^ n.val)⁻¹ = (cycle 1)⁻¹ := by
    decide +kernel
  exact h i hi

private theorem neighbor_representative (i : Fin 10)
    (hc : Nat.card (C 0 ⊔ C i : Subgroup A5) = 12) : representative i = 1 := by
  have hm := (adjustment_maps i).1
  have hn := (adjustment_maps i).2
  have he : Nat.card (C 0 ⊔ C (representative i) : Subgroup A5) = 12 := by
    rw [← hm, ← hn, ← Subgroup.map_sup, card_map_of_injective (MulAut.conj _).injective, hc]
  have cases : representative i = 0 ∨ representative i = 1 ∨ representative i = 5 := by
    have h : ∀ i, representative i = 0 ∨ representative i = 1 ∨ representative i = 5 := by
      decide +kernel
    exact h i
  rcases cases with h | h | h
  · rw [h, sup_idem, card_C] at he
    omega
  · exact h
  · rw [h, nonedge_join, card_top, card] at he
    omega

/-- An adjustment fixing the cubic normalizer pointwise, followed by conjugation
inside the cubic, takes any adjacent cubic to a prescribed adjacent cubic. -/
theorem adjust_neighbor {H : Type*} [Group H]
    (e : H ≃* A5) (P Q R : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) (hR : Nat.card R = 3)
    (ePQ : ↥(P ⊔ Q) ≃* alternatingGroup (Fin 4))
    (ePR : ↥(P ⊔ R) ≃* alternatingGroup (Fin 4)) :
    ∃ z : P, ∃ b : MulAut H,
      (∀ n : H, n ∈ normalizer (P : Set H) → b n = n) ∧
      Q.map (b.trans (MulAut.conj (z : H))).toMonoidHom = R := by
  obtain ⟨a, hp, hr⟩ := exists_marking e P R hP hR ePR
  obtain ⟨i, hi⟩ := cubic_representative (Q.map a.toMonoidHom)
    (by rw [card_map_of_injective a.injective, hQ])
  have hc : Nat.card (C 0 ⊔ C i : Subgroup A5) = 12 := by
    rw [← hp, ← hi, ← Subgroup.map_sup, card_map_of_injective a.injective,
      Nat.card_congr ePQ.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨n, j, hj⟩ := six_neighbors i (neighbor_representative i hc)
  let t : A5 := cycle 0 ^ n.val
  let d : MulAut A5 := flipAut ^ j.val
  have hd (x : A5) (hx : x ∈ normalizer (C 0 : Set A5)) : d x = x := by
    fin_cases j
    · rfl
    · exact flipAut_fixes x hx
  let z : P := ⟨a.symm t, by
    apply mem_map_equiv.mp
    rw [hp]
    exact pow_mem (mem_zpowers _) _⟩
  let b : MulAut H := a.trans (d.trans a.symm)
  refine ⟨z, b, ?_, ?_⟩
  · intro x hx
    have hn : a x ∈ normalizer (C 0 : Set A5) := by
      rw [← hp, ← map_equiv_normalizer_eq]
      exact mem_map_of_mem a.toMonoidHom hx
    change a.symm (d (a x)) = x
    rw [hd _ hn, a.symm_apply_apply]
  · apply map_injective (f := a.toMonoidHom) a.injective
    rw [hr]
    have he : (b.trans (MulAut.conj (z : H))).trans a =
        a.trans (d.trans (MulAut.conj t)) := by
      apply MulEquiv.ext
      intro x
      change a ((z : H) * a.symm (d (a x)) * (z : H)⁻¹) = t * d (a x) * t⁻¹
      simp only [map_mul, map_inv, z, a.apply_symm_apply]
    rw [map_map]
    change Q.map ((b.trans (MulAut.conj (z : H))).trans a).toMonoidHom = _
    rw [he]
    change Q.map ((MulAut.conj t).toMonoidHom.comp (d.toMonoidHom.comp a.toMonoidHom)) = _
    rw [← map_map, ← map_map, hi, C, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    change zpowers (t * d (cycle i) * t⁻¹) = C 1
    rcases hj with hj | hj <;> simp only [t, d, hj, C, zpowers_inv]
/-- An isomorphism carries the literal unordered cubic-pair stabilizer to
that of the two image subgroups. -/
theorem mem_pairStabilizer_map_iff {H J : Type*} [Group H] [Group J]
    (e : H ≃* J) (P Q : Subgroup H) (g : H) :
    g ∈ pairStabilizer P Q ↔
      e g ∈ pairStabilizer (P.map e.toMonoidHom) (Q.map e.toMonoidHom) := by
  have he (U V : Subgroup H) :
      (U.map (MulAut.conj g).toMonoidHom = V) ↔
        (U.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom = V.map e.toMonoidHom := by
    rw [← map_conj_equiv]
    exact (map_injective (f := e.toMonoidHom) e.injective).eq_iff.symm
  change ((_ ∧ _) ∨ (_ ∧ _)) ↔ ((_ ∧ _) ∨ (_ ∧ _))
  rw [he P P, he Q Q, he P Q, he Q P]

end alternatingGroup.FiveLocalGeometry.CubicEdges
