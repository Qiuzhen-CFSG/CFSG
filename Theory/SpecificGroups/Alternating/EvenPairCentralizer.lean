module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

/-!
# A two-subgroup with two-group permutation centralizer

Partition the letters into pairs and at most one singleton. The permutations
preserving each pair form an elementary abelian two-group. With at least three
pairs, a permutation centralizing its even part preserves every pair: the
supports of the double flips on pairs (i,j) and (i,k) intersect in pair i.
It also fixes the possible singleton. The centralizer therefore lies in the
original two-group. Transporting the partition gives the result on Fin m.

This is the permutation-group calculation behind the alternating Sylow-fixer
step in Aschbacher–Smith, combined manuscript (1 March 2004), B.1.13,
printed p.74 (PDF p.85). No classification of Sylow overgroups is used.
-/

open Equiv Subgroup
namespace Theory.SpecificGroups.Alternating.EvenPairCentralizer

variable {I R : Type*}
private abbrev Ω (I R : Type*) := (I × Bool) ⊕ R

private def label : Ω I R → I ⊕ R := Sum.map Prod.fst id

private def pairs : Subgroup (Perm (Ω I R)) where
  carrier := {g | ∀ x, label (g x) = label x}
  one_mem' _ := rfl
  mul_mem' := by
    intro g h hg hh x
    exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    simpa using (hg (g⁻¹ x)).symm

private theorem pairs_inl (g : pairs (I := I) (R := R)) (i : I) (b : Bool) :
    ∃ c, g.val (.inl (i,b)) = .inl (i,c) := by
  have h := g.property (.inl (i,b))
  cases he : g.val (.inl (i,b)) with
  | inr r => simp [he, label] at h
  | inl p =>
    have hp : p.1 = i := by simpa [he, label] using h
    exact ⟨p.2, by rw [← hp]⟩

private theorem pairs_inr (g : pairs (I := I) (R := R)) (r : R) :
    g.val (.inr r) = .inr r := by
  have h := g.property (.inr r)
  cases he : g.val (.inr r) with
  | inl p => simp [he, label] at h
  | inr s => simpa [he, label] using h

private theorem pairs_square (g : pairs (I := I) (R := R)) : g ^ 2 = 1 := by
  apply Subtype.ext
  ext x
  change g.val (g.val x) = x
  cases x with
  | inr r => rw [pairs_inr, pairs_inr]
  | inl p =>
    obtain ⟨c,hc⟩ := pairs_inl g p.1 p.2
    obtain ⟨d,hd⟩ := pairs_inl g p.1 c
    have hi := g.val.injective
    cases p with
    | mk i b =>
      cases b <;> cases c <;> cases d <;> simp_all
      all_goals have hh := hi (hc.trans hd.symm); simp at hh

private theorem pairs_two : IsPGroup 2 (pairs (I := I) (R := R)) := by
  intro g
  exact ⟨1, by simpa using pairs_square g⟩

variable [DecidableEq I] [DecidableEq R]

private def flip (i : I) : Perm (Ω I R) := swap (.inl (i,false)) (.inl (i,true))

private theorem flip_apply (i j : I) (b : Bool) :
    flip (R := R) i (.inl (j,b)) = .inl (j, if j = i then !b else b) := by
  by_cases h : j = i
  · subst j; cases b <;> simp [flip]
  · cases b <;> simp [flip, h, swap_apply_of_ne_of_ne]

private theorem flip_inr (i : I) (r : R) : flip i (.inr r) = .inr r := by simp [flip, swap_apply_of_ne_of_ne]

private theorem flip_mem (i : I) : flip (R := R) i ∈ pairs := by
  intro x
  cases x with
  | inl p => rcases p with ⟨j,b⟩; simp [flip_apply, label]
  | inr r => simp [flip_inr]

private theorem double_moved (i j k : I) (b : Bool) (hij : i ≠ j) :
    (flip (R := R) i * flip j : Perm (Ω I R)) (.inl (k,b)) ≠ .inl (k,b) ↔ k = i ∨ k = j := by
  simp only [Perm.mul_apply, flip_apply]
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all

private theorem double_fixed_inr (i j : I) (r : R) :
    (flip i * flip j : Perm (Ω I R)) (.inr r) = .inr r := by simp [Perm.mul_apply, flip_inr]

private theorem commuting_moved {α : Type*} (p q : Perm α) (h : p * q = q * p) (x : α) :
    q (p x) ≠ p x ↔ q x ≠ x := by
  have he := congrArg (fun g : Perm α => g x) h
  change p (q x) = q (p x) at he
  rw [← he, p.injective.ne_iff]

variable [Fintype I] [Fintype R]

private theorem double_even (i j : I) : flip (R := R) i * flip j ∈ alternatingGroup (Ω I R) := by
  simp [Perm.mem_alternatingGroup, flip]

private theorem centralizer_le_pairs [Subsingleton R] (hI : 3 ≤ Fintype.card I) :
    centralizer ((pairs (I := I) (R := R) ⊓ alternatingGroup (Ω I R) : Subgroup (Perm (Ω I R))) : Set (Perm (Ω I R))) ≤ pairs := by
  intro p hp
  have hc (i j : I) : p * (flip (R := R) i * flip j : Perm (Ω I R)) = (flip i * flip j : Perm (Ω I R)) * p :=
    (hp _ ⟨pairs.mul_mem (flip_mem i) (flip_mem j), double_even i j⟩).symm
  have himage (i : I) (b : Bool) : ∃ c, p (.inl (i,b)) = .inl (i,c) := by
    obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k : I, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
      have hcard : 1 < (Finset.univ.erase i).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
        omega
      obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hcard
      exact ⟨j,k,(Finset.mem_erase.mp hj).1.symm,(Finset.mem_erase.mp hk).1.symm,hjk⟩
    have hmj : (flip i * flip j : Perm (Ω I R)) (p (.inl (i,b))) ≠ p (.inl (i,b)) :=
      (commuting_moved _ _ (hc i j) _).mpr ((double_moved i j i b hij).mpr (Or.inl rfl))
    have hmk : (flip i * flip k : Perm (Ω I R)) (p (.inl (i,b))) ≠ p (.inl (i,b)) :=
      (commuting_moved _ _ (hc i k) _).mpr ((double_moved i k i b hik).mpr (Or.inl rfl))
    cases he : p (.inl (i,b)) with
    | inr r => simp [he, double_fixed_inr] at hmj
    | inl y =>
      rw [he, double_moved _ _ _ _ hij] at hmj
      rw [he, double_moved _ _ _ _ hik] at hmk
      have hy : y.1 = i := by
        rcases hmj with h | h
        · exact h
        rcases hmk with h' | h'
        · exact h'
        exact (hjk (h.symm.trans h')).elim
      exact ⟨y.2, by rw [← hy]⟩
  intro x
  cases x with
  | inl y => obtain ⟨c,hc⟩ := himage y.1 y.2; simp [hc, label]
  | inr r =>
    cases he : p (.inr r) with
    | inr s => simp [label, Subsingleton.elim s r]
    | inl y =>
      obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.erase y.1).card by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        omega)
      have hyj : y.1 ≠ j := (Finset.mem_erase.mp hj).1.symm
      have hm := (commuting_moved p (flip y.1 * flip j : Perm (Ω I R)) (hc y.1 j) (.inr r)).mp
        (show (flip y.1 * flip j : Perm (Ω I R)) (p (.inr r)) ≠ p (.inr r) by
          rw [he, double_moved _ _ _ _ hyj]
          exact Or.inl rfl)
      exact (hm (double_fixed_inr _ _ _)).elim


private theorem centralizer_map_two {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (D : Subgroup G) (h : IsPGroup 2 (centralizer (D : Set G))) :
    IsPGroup 2 (centralizer (D.map e.toMonoidHom : Set H)) := by
  let C := centralizer (D.map e.toMonoidHom : Set H)
  let f : C →* centralizer (D : Set G) :=
    (e.symm.toMonoidHom.comp C.subtype).codRestrict _ (by
      intro c d hd
      change d * e.symm c.val = e.symm c.val * d
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using
        c.property (e d) (mem_map_of_mem e.toMonoidHom hd))
  exact h.of_injective f (fun x y hxy => Subtype.ext
    (e.symm.injective (congrArg Subtype.val hxy)))

/-- For at least six letters, an actual two-subgroup of the alternating group
has a two-group centralizer in the full symmetric group. -/
public theorem exists_two_subgroup_centralizer (m : ℕ) (hm : 6 ≤ m) :
    ∃ D : Subgroup (alternatingGroup (Fin m)), IsPGroup 2 D ∧
      IsPGroup 2 (centralizer (D.map (alternatingGroup (Fin m)).subtype :
        Set (Perm (Fin m)))) := by
  classical
  let I := Fin (m / 2)
  let R := Fin (m % 2)
  have hR : Fintype.card R ≤ 1 := by simp [R]; omega
  let : Subsingleton R := Fintype.card_le_one_iff_subsingleton.mp hR
  let e : Ω I R ≃ Fin m := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, I, R, Fintype.card_fin]
    omega)
  let B : Subgroup (Perm (Ω I R)) := pairs ⊓ alternatingGroup (Ω I R)
  let D₀ : Subgroup (alternatingGroup (Ω I R)) := pairs.subgroupOf _
  let D := D₀.map e.altCongrHom.toMonoidHom
  have hD₀ : IsPGroup 2 D₀ := pairs_two.comap_of_injective
    (alternatingGroup (Ω I R)).subtype Subtype.val_injective
  have hB : IsPGroup 2 (centralizer (B : Set (Perm (Ω I R)))) :=
    pairs_two.to_le (centralizer_le_pairs (by simp [I]; omega))
  have he : D.map (alternatingGroup (Fin m)).subtype = B.map e.permCongrHom.toMonoidHom := by
    change (D₀.map e.altCongrHom.toMonoidHom).map _ = _
    rw [map_map]
    have heq : (alternatingGroup (Fin m)).subtype.comp e.altCongrHom.toMonoidHom =
        e.permCongrHom.toMonoidHom.comp (alternatingGroup (Ω I R)).subtype := by
      ext x
      rfl
    rw [heq, ← map_map, subgroupOf_map_subtype]
  exact ⟨D, hD₀.map _, by rw [he]; exact centralizer_map_two e.permCongrHom B hB⟩

end Theory.SpecificGroups.Alternating.EvenPairCentralizer
