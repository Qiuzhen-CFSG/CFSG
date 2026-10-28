module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.PairNormalForm
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Representatives

/-!
# Four-pair actions in the degree-eight offender classification

A permutation group whose orbits all have size two lies in the group of all
permutations preserving each of those orbits. This overgroup contains every
individual pair swap. The pair normal form identifies it with `A_m`; absence
of fixed coordinates forces `m = 4`, so it is conjugate to `D 8`.

Transporting the original group along this conjugacy puts it inside `D 8`.
Order sixteen gives equality. Order eight gives a cover in the subgroup
lattice by Lagrange's theorem, hence either the even part or one of the other
hyperplanes listed in the source. The argument proves actual ambient
conjugacy, not just equality of orders. The standard order calculation is
reused from `Eight.Canonical.Representatives`.

This is the four-pair geometric branch of Aschbacher–Smith,
*The Classification of Quasithin Groups*, 1 March 2004 manuscript,
Proposition B.3.2(5), printed pp. 83–84. The orbit and order hypotheses are
supplied by the separate orbit-defect reduction.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
open Equiv Representation.BinaryOffender

private def orbitPreserving (A : Subgroup (Perm (Fin 8))) : Subgroup (Perm (Fin 8)) where
  carrier := {p | ∀ x, p x ∈ MulAction.orbit A x}
  one_mem' := fun x => MulAction.mem_orbit_self x
  mul_mem' := by
    intro p q hp hq x
    change p (q x) ∈ MulAction.orbit A x
    rw [← MulAction.orbit_eq_iff.mpr (hq x)]
    exact hp (q x)
  inv_mem' := by
    intro p hp x
    have h := hp (p⁻¹ x)
    simp only [Perm.inv_def, apply_symm_apply] at h
    exact MulAction.mem_orbit_symm.mp h

private theorem le_orbitPreserving (A : Subgroup (Perm (Fin 8))) :
    A ≤ orbitPreserving A := by
  intro p hp x
  exact MulAction.mem_orbit x (⟨p, hp⟩ : A)

private theorem orbitPreserving_orbit (A : Subgroup (Perm (Fin 8))) (x : Fin 8) :
    MulAction.orbit (orbitPreserving A) x = MulAction.orbit A x := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact p.property x
  · rintro ⟨p, rfl⟩
    exact MulAction.mem_orbit x (⟨p.val, le_orbitPreserving A p.property⟩ : orbitPreserving A)

private theorem orbitPreserving_swap (A : Subgroup (Perm (Fin 8)))
    (x y : Fin 8) (hy : y ∈ MulAction.orbit (orbitPreserving A) x) :
    swap x y ∈ orbitPreserving A := by
  rw [orbitPreserving_orbit] at hy
  intro z
  by_cases hx : z = x
  · subst z; simpa using hy
  by_cases hz : z = y
  · subst z; simpa using (MulAction.mem_orbit_symm.mp hy)
  · simp [swap_apply_of_ne_of_ne hx hz]

private theorem initial_fixes_seven (m : ℕ) (hm : m < 4)
    (p : Perm (Fin 8)) (hp : p ∈ disjointTranspositions 8 m) : p 7 = 7 := by
  have hle : disjointTranspositions 8 m ≤ MulAction.stabilizer (Perm (Fin 8)) (7 : Fin 8) := by
    apply (Subgroup.closure_le _).mpr
    rintro q ⟨i, hi, rfl⟩
    change pairSwap 8 i 7 = 7
    have : i.val < 3 := by omega
    fin_cases i <;> first | decide | (norm_num at this)
  exact hle hp

private theorem orbitPreserving_conjugate_D (A : Subgroup (Perm (Fin 8)))
    (horb : ∀ x : Fin 8, Nat.card (MulAction.orbit A x) = 2) :
    IsConjugateTo (orbitPreserving A) (D 8) := by
  classical
  have hmove (x : Fin 8) : ∃ a : A, a.val x ≠ x := by
    by_contra! h
    have he : MulAction.orbit A x = {x} := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩; exact h a
      · intro hy
        have hyx : y = x := hy
        subst y
        exact MulAction.mem_orbit_self x
    have hc := horb x
    rw [he] at hc
    simp at hc
  have hne : orbitPreserving A ≠ ⊥ := by
    intro he
    obtain ⟨a, ha⟩ := hmove 0
    have hmem := le_orbitPreserving A a.property
    rw [he, Subgroup.mem_bot] at hmem
    exact ha (congrArg (fun p : Perm (Fin 8) => p 0) hmem)
  obtain ⟨m, hm0, hm, g, hg⟩ := caseAFamily_of_pair_orbits rfl (orbitPreserving A) hne
    (fun x => by rw [orbitPreserving_orbit, horb]) (orbitPreserving_swap A)
  have hm4 : m = 4 := by
    by_contra h
    have hlt : m < 4 := by omega
    obtain ⟨a, ha⟩ := hmove (g 7)
    have hmem := le_orbitPreserving A a.property
    rw [hg] at hmem
    obtain ⟨p, hp, he⟩ := hmem
    apply ha
    have hp7 := initial_fixes_seven m hlt p hp
    rw [← he]
    simpa [MulAut.conj_apply] using congrArg g hp7
  exact ⟨g, by simpa [hm4] using hg⟩

private theorem card_D_pairGeometry : Nat.card (D 8) = 16 :=
  Eight.card_disjointTranspositions 4

/-- A four-pair action is conjugate to a subgroup of the full independent-flip group.
The conjugacy preserves its order. -/
theorem pair_orbits_conjugate_subgroup_D (A : Subgroup (Perm (Fin 8)))
    (horb : ∀ x : Fin 8, Nat.card (MulAction.orbit A x) = 2) :
    ∃ B : Subgroup (Perm (Fin 8)), B ≤ D 8 ∧ IsConjugateTo A B ∧ Nat.card B = Nat.card A := by
  obtain ⟨g, hg⟩ := orbitPreserving_conjugate_D A horb
  let e := MulAut.conj g
  let B := A.comap e.toMonoidHom
  have hconj : A = B.map e.toMonoidHom :=
    (Subgroup.map_comap_eq_self_of_surjective e.surjective A).symm
  refine ⟨B, ?_, ⟨g, hconj⟩, ?_⟩
  · have h := Subgroup.comap_mono (f := e.toMonoidHom) (le_orbitPreserving A)
    rw [hg, Subgroup.comap_map_eq_self_of_injective e.injective] at h
    exact h
  · conv_rhs => rw [hconj]
    exact (Subgroup.card_map_of_injective e.injective).symm

/-- In order sixteen, the conjugated four-pair action is the full group `D`. -/
theorem conjugate_D_of_pair_orbits_card_sixteen (A : Subgroup (Perm (Fin 8)))
    (horb : ∀ x : Fin 8, Nat.card (MulAction.orbit A x) = 2)
    (hcard : Nat.card A = 16) : IsConjugateTo A (D 8) := by
  obtain ⟨B, hBD, hconj, hc⟩ := pair_orbits_conjugate_subgroup_D A horb
  have he : B = D 8 := Subgroup.eq_of_le_of_card_ge hBD (by rw [hc, hcard, card_D_pairGeometry])
  rwa [he] at hconj

private theorem covBy_D_of_card_eight (B : Subgroup (Perm (Fin 8)))
    (hle : B ≤ D 8) (hc : Nat.card B = 8) : B ⋖ D 8 := by
  have hlt : B < D 8 := lt_of_le_of_ne hle (by
    intro he
    have := card_D_pairGeometry
    rw [← he, hc] at this
    contradiction)
  refine ⟨hlt, ?_⟩
  intro C hBC hCD
  have hlow := Subgroup.card_le_of_le hBC.le
  have hupp := Subgroup.card_le_of_le hCD.le
  have hdvd := Subgroup.card_dvd_of_le hBC.le
  rw [hc] at hlow hdvd
  rw [card_D_pairGeometry] at hupp
  have hstrict : Nat.card C < 16 := by
    by_contra h
    have he := Subgroup.eq_of_le_of_card_ge hCD.le (by rw [card_D_pairGeometry]; omega)
    exact hCD.ne he
  have hecard : Nat.card C = 8 := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd (by omega)
  exact hBC.ne (Subgroup.eq_of_le_of_card_ge hBC.le (by rw [hc, hecard]))

/-- In order eight, the conjugated four-pair action is a hyperplane of `D`. -/
theorem conjugate_hyperplane_of_pair_orbits_card_eight (A : Subgroup (Perm (Fin 8)))
    (horb : ∀ x : Fin 8, Nat.card (MulAction.orbit A x) = 2)
    (hcard : Nat.card A = 8) :
    ∃ B : Subgroup (Perm (Fin 8)), B ⋖ D 8 ∧ IsConjugateTo A B := by
  obtain ⟨B, hBD, hconj, hc⟩ := pair_orbits_conjugate_subgroup_D A horb
  exact ⟨B, covBy_D_of_card_eight B hBD (hc.trans hcard), hconj⟩

/-- Four pair orbits and order eight or sixteen give the source case-(b) family. -/
theorem caseBFamily_of_pair_orbits (A : Subgroup (Perm (Fin 8)))
    (_hA : IsElementaryTwo A)
    (horb : ∀ x : Fin 8, Nat.card (MulAction.orbit A x) = 2)
    (hcard : Nat.card A = 8 ∨ Nat.card A = 16) : CaseBFamily 8 (by decide) A := by
  classical
  rcases hcard with hcard | hcard
  · obtain ⟨B, hB, hconj⟩ := conjugate_hyperplane_of_pair_orbits_card_eight A horb hcard
    by_cases he : B = evenPart 8
    · exact Or.inr (Or.inr (Or.inl (he ▸ hconj)))
    · exact Or.inr (Or.inr (Or.inr ⟨B, hB, he, hconj⟩))
  · exact Or.inl ⟨4, by decide, by decide, conjugate_D_of_pair_orbits_card_sixteen A horb hcard⟩

end CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
