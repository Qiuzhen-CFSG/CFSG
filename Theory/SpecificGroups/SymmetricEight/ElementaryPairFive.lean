module
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Theory.ElementaryAbelian.Basic
/-!
# An order-five element in two conjugates of an elementary S₈ actor

Every elementary subgroup of S₈ with at least eight elements and one conjugate
jointly contain an element of order five. If the subgroup contains an involution
with two or three transpositions, two explicit conjugate involutions suffice.
Otherwise conjugate into the binary-tree Sylow. Only 22 of its 128 words remain;
their commuting neighborhoods force a subgroup of order at least eight to be
one of the two regular eight-groups. A six-letter word in each regular group
and one explicit conjugate has order five.

The finite certificates check the 128 normal forms and neighborhoods on 22
indices, rather than enumerate subgroups of S₈. The resulting theorem includes
regular E₈ actors, whose involutions all have permutation type 2⁴.

Application: an alternative to the constituent argument in Guralnick--Malle,
Classification of 2F-modules I, Proposition 5.1, HS paragraph, pp.16--17;
Aschbacher--Smith K.4, printed p.457. The literal HS application is in
`M11HigmanSimsSourceHSOuterPairs`.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace Theory.SpecificGroups.SymmetricEight.ElementaryPairFive
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev S := Equiv.Perm (Fin 8)
private def good (x : S) : Prop := x.support.card = 4 ∨ x.support.card = 6
private instance (x : S) : Decidable (good x) := inferInstanceAs (Decidable (_ ∨ _))
private def badIndex : Fin 22 → Fin 128 := ![0,1,2,4,8,15,28,31,35,47,48,51,60,63,64,69,74,79,112,118,121,127]
private def badWord (i : Fin 22) : S := treeWord (badIndex i)
private theorem cover : ∀ i : Fin 128, (treeWord i)^2 = 1 → ¬good (treeWord i) →
    ∃ j : Fin 22, badIndex j = i := by decide +kernel
private theorem bad_injective : Function.Injective badWord := by
  apply treeWord_injective.comp
  decide +kernel

private def compatible (i j : Fin 22) : Prop :=
  badWord i * badWord j = badWord j * badWord i ∧ ¬good (badWord i * badWord j)
private instance (i j : Fin 22) : Decidable (compatible i j) := inferInstanceAs (Decidable (_ ∧ _))
private def neighbors (i : Fin 22) : Finset (Fin 22) := Finset.univ.filter (compatible i)
private theorem small : ∀ i : Fin 22, (neighbors i).card ≥ 8 →
    i = 0 ∨ i = 5 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ 14 ≤ i.val := by decide +kernel
private theorem large : ∀ i : Fin 22, 14 ≤ i.val →
    (neighbors i).card = 8 ∧
    ((14 ∈ neighbors i ∧ 10 ∈ neighbors i ∧ 5 ∈ neighbors i) ∨
    (15 ∈ neighbors i ∧ 11 ∈ neighbors i ∧ 5 ∈ neighbors i)) := by decide +kernel

private theorem regular_cases (B : Subgroup S) [IsElementaryAbelian 2 B]
    (hle : B ≤ treeGroup) (hcard : 8 ≤ Nat.card B)
    (hbad : ∀ x ∈ B, ¬good x) :
    (treeWord 15 ∈ B ∧ treeWord 48 ∈ B ∧ treeWord 64 ∈ B) ∨
    (treeWord 15 ∈ B ∧ treeWord 51 ∈ B ∧ treeWord 69 ∈ B) := by
  classical
  let : Fintype B := Fintype.ofFinite B
  have hex (x : B) : ∃ j, badWord j = (x : S) := by
    obtain ⟨i, hi⟩ := (mem_treeGroup (x : S)).mp (hle x.property)
    have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : S) x.property
    obtain ⟨j, hj⟩ := cover i (hi ▸ hs) (hi ▸ hbad x x.property)
    exact ⟨j, by rw [badWord, hj, hi]⟩
  let f : B → Fin 22 := fun x => (hex x).choose
  have hf (x : B) : badWord (f x) = (x : S) := (hex x).choose_spec
  have hfi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    rw [← hf x, ← hf y, he]
  let C := Finset.univ.image f
  have hCcard : 8 ≤ C.card := by
    rw [Finset.card_image_of_injective _ hfi]
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hcard
  have hmem {i} (hi : i ∈ C) : badWord i ∈ B := by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
    rw [hf]
    exact x.property
  have hsub {i} (hi : i ∈ C) : C ⊆ neighbors i := by
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    constructor
    · exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := B)).comm
          ⟨badWord i, hmem hi⟩ ⟨badWord j, hmem hj⟩)
    · exact hbad _ (B.mul_mem (hmem hi) (hmem hj))
  have hlarge : ∃ i ∈ C, 14 ≤ i.val := by
    by_contra hn
    push Not at hn
    have hsub' : C ⊆ {0,5,10,11,12,13} := by
      intro i hi
      have hh := small i (hCcard.trans (Finset.card_le_card (hsub hi)))
      have hh' : ¬14 ≤ i.val := not_le.mpr (hn i hi)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using (by simpa only [hh', or_false] using hh : i = 0 ∨ i = 5 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13)
    have hh := Finset.card_le_card hsub'
    have hs : ({0,5,10,11,12,13} : Finset (Fin 22)).card = 6 := by decide
    omega
  obtain ⟨i, hi, hil⟩ := hlarge
  obtain ⟨hni, hr | hr⟩ := large i hil
  all_goals
    have he : C = neighbors i := Finset.eq_of_subset_of_card_le (hsub hi) (by omega)
    have hm {j} (hj : j ∈ neighbors i) : badWord j ∈ B := hmem (he ▸ hj)
  · have h5 := hm hr.2.2
    have h10 := hm hr.2.1
    have h14 := hm hr.1
    simp only [badWord, badIndex] at h5 h10 h14
    exact Or.inl ⟨h5,h10,h14⟩
  · have h5 := hm hr.2.2
    have h11 := hm hr.2.1
    have h15 := hm hr.1
    simp only [badWord, badIndex] at h5 h11 h15
    exact Or.inr ⟨h5,h11,h15⟩
private def conjTwo : S := Equiv.swap 1 2 * Equiv.swap 3 4
private def conjThree : S := Equiv.swap 3 4 * Equiv.swap 5 6
private def conjRegular : S := Equiv.swap 3 4 * Equiv.swap 5 6 * Equiv.swap 6 7
private def regularWord (a b d : S) : S :=
  a * (MulAut.conj conjRegular) a * d * (MulAut.conj conjRegular) b * b *
    (MulAut.conj conjRegular) d
private theorem regular_word_five :
    (regularWord (treeWord 15) (treeWord 48) (treeWord 64)) ^ 5 = 1 ∧
    regularWord (treeWord 15) (treeWord 48) (treeWord 64) ≠ 1 ∧
    (regularWord (treeWord 15) (treeWord 51) (treeWord 69)) ^ 5 = 1 ∧
    regularWord (treeWord 15) (treeWord 51) (treeWord 69) ≠ 1 := by decide +kernel

private theorem regular_pair_five (B : Subgroup S) {a b d : S}
    (ha : a ∈ B) (hb : b ∈ B) (hd : d ∈ B)
    (hw : regularWord a b d ^ 5 = 1) (hn : regularWord a b d ≠ 1) :
    ∃ c x : S, x ∈ B ⊔ B.map (MulAut.conj c).toMonoidHom ∧ orderOf x = 5 := by
  refine ⟨conjRegular, regularWord a b d, ?_, orderOf_eq_prime hw hn⟩
  let K := B ⊔ B.map (MulAut.conj conjRegular).toMonoidHom
  have h₁ {x : S} (hx : x ∈ B) : x ∈ K := Subgroup.mem_sup_left hx
  have h₂ {x : S} (hx : x ∈ B) : (MulAut.conj conjRegular) x ∈ K :=
    Subgroup.mem_sup_right (mem_map_of_mem _ hx)
  exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem
    (h₁ ha) (h₂ ha)) (h₁ hd)) (h₂ hb)) (h₁ hb)) (h₂ hd)

private theorem good_pair_five (B : Subgroup S) [IsElementaryAbelian 2 B]
    {x : S} (hx : x ∈ B) (hg : good x) :
    ∃ c y : S, y ∈ B ⊔ B.map (MulAut.conj c).toMonoidHom ∧ orderOf y = 5 := by
  have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have hc := Equiv.Perm.cycleType_of_pow_prime_eq_one hs
  have hsum := x.sum_cycleType
  rw [hc, Multiset.sum_replicate] at hsum
  simp only [smul_eq_mul] at hsum
  have ht : x.cycleType = {2,2} ∨ x.cycleType = {2,2,2} := by
    rcases hg with hg | hg
    · have hn : x.cycleType.card = 2 := by omega
      left
      simpa [hn] using hc
    · have hn : x.cycleType.card = 3 := by omega
      right
      simpa [hn] using hc
  have hex : ∃ (z c : S), IsConj z x ∧ (z * (MulAut.conj c) z)^5 = 1 ∧
      z * (MulAut.conj c) z ≠ 1 := by
    rcases ht with ht | ht
    · refine ⟨treeWord 3, conjTwo, ?_, ?_, ?_⟩
      · apply Equiv.Perm.isConj_iff_cycleType_eq.mpr
        rw [ht]
        decide +kernel
      · decide +kernel
      · decide +kernel
    · refine ⟨treeWord 7, conjThree, ?_, ?_, ?_⟩
      · apply Equiv.Perm.isConj_iff_cycleType_eq.mpr
        rw [ht]
        decide +kernel
      · decide +kernel
      · decide +kernel
  obtain ⟨z, c, hz, h5, hn⟩ := hex
  obtain ⟨g, hg⟩ := isConj_iff.mp hz
  let f := MulAut.conj g
  have hfx : f z = x := hg
  have hfc : f ((MulAut.conj c) z) = (MulAut.conj (f c)) x := by
    change f (c * z * c⁻¹) = f c * x * (f c)⁻¹
    rw [map_mul, map_mul, map_inv, hfx]
  refine ⟨f c, f (z * (MulAut.conj c) z), ?_, ?_⟩
  · rw [map_mul, hfx, hfc]
    apply mul_mem (Subgroup.mem_sup_left hx)
    exact Subgroup.mem_sup_right (mem_map_of_mem _ hx)
  · exact (f.orderOf_eq _).trans (orderOf_eq_prime h5 hn)

/-- An elementary subgroup of S₈ of order at least eight and one conjugate
jointly contain an element of order five. Regular eight-groups are included. -/
theorem exists_order_five_in_pair (B : Subgroup (Equiv.Perm (Fin 8)))
    [IsElementaryAbelian 2 B] (hcard : 8 ≤ Nat.card B) :
    ∃ c x : Equiv.Perm (Fin 8),
      x ∈ B ⊔ B.map (MulAut.conj c).toMonoidHom ∧ orderOf x = 5 := by
  obtain ⟨P,hBP⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P treeSylow
  let f := MulAut.conj g
  let D := B.map f.toMonoidHom
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map f.toMonoidHom
  have hP : (P : Subgroup S).map f.toMonoidHom = treeGroup := by
    change ((g • P : Sylow 2 S) : Subgroup S) = treeGroup
    rw [hg,treeSylow_coe]
  have hD : D ≤ treeGroup := hP ▸ map_mono hBP
  have hd : 8 ≤ Nat.card D := by
    rw [card_map_of_injective f.injective]
    exact hcard
  have hex : ∃ c x : S, x ∈ D ⊔ D.map (MulAut.conj c).toMonoidHom ∧ orderOf x = 5 := by
    by_cases hh : ∃ x ∈ D, good x
    · obtain ⟨x,hx,hgood⟩ := hh
      exact good_pair_five D hx hgood
    · push Not at hh
      rcases regular_cases D hD hd hh with ⟨ha,hb,hd⟩ | ⟨ha,hb,hd⟩
      · exact regular_pair_five D ha hb hd regular_word_five.1 regular_word_five.2.1
      · exact regular_pair_five D ha hb hd regular_word_five.2.2.1 regular_word_five.2.2.2
  obtain ⟨c,x,hx,ho⟩ := hex
  refine ⟨f.symm c, f.symm x, ?_, (f.symm.orderOf_eq x).trans ho⟩
  let K := B ⊔ B.map (MulAut.conj (f.symm c)).toMonoidHom
  have hDback {y : S} (hy : y ∈ D) : f.symm y ∈ B := by
    obtain ⟨z,hz,rfl⟩ := hy
    change f.symm (f z) ∈ B
    rw [f.symm_apply_apply]
    exact hz
  have hle : D ⊔ D.map (MulAut.conj c).toMonoidHom ≤ K.comap f.symm.toMonoidHom := by
    apply sup_le
    · intro y hy
      exact Subgroup.mem_sup_left (hDback hy)
    · rintro y ⟨z,hz,rfl⟩
      change f.symm (c * z * c⁻¹) ∈ K
      rw [map_mul,map_mul,map_inv]
      exact Subgroup.mem_sup_right (mem_map_of_mem (MulAut.conj (f.symm c)).toMonoidHom (hDback hz))
  exact hle hx

end Theory.SpecificGroups.SymmetricEight.ElementaryPairFive
