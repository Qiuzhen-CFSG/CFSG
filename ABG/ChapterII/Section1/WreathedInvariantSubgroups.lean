module
public import ABG.ChapterII.Section1.WreathedNoncyclicInvolution
public import ABG.ChapterII.Section1.WreathedCenter
public import ABG.ChapterII.Section1.WreathedInvariantGeneration

/-!
# Invariant subgroups disjoint from a large cyclic subgroup

ABG Chapter II §1 Lemma 2(xiii), article p.10: if a subgroup X is normalized
by a cyclic subgroup A of order 2^n and is disjoint from A, then X is cyclic
or X and A generate the whole wreathed group.

A noncyclic X contains the central involution x, so A omits x and meets the
cyclic center trivially. Every outer element has central square; since the
generator of A has order at least four, A lies in the abelian base. X cannot
also lie there: a noncyclic base subgroup contains all base involutions and
would intersect A. An outer element of X therefore exists. The imported
commutator injection into X, followed by the disjoint product with A, has
exactly the cardinality of the whole group and proves generation.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem cyclic_le_U_of_not_x (A : Subgroup S) [IsCyclic A]
    (hcard : Nat.card A = 2 ^ n) (hx : P.x ∉ A) : A ≤ P.U := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  have hp : IsPGroup 2 S := IsPGroup.of_card P.card
  let : IsCyclic (Subgroup.center S) := P.center_cyclic
  have hd : Disjoint (Subgroup.center S) A :=
    hp.disjoint_of_involution_not_mem _ _ P.x_mem_center P.x_orderOf hx
  obtain ⟨a, rfl⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  apply Subgroup.zpowers_le_of_mem
  by_contra hau
  have haA : a ^ 2 ∈ Subgroup.zpowers a := Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _
  have haC : a ^ 2 ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro b
    exact (P.outer_square_commute hau b).symm.eq
  have ha2 : a ^ 2 = 1 := Subgroup.disjoint_def.mp hd haC haA
  have ho : orderOf a = 2 ^ n := by simpa only [Nat.card_zpowers] using hcard
  have hlo := orderOf_le_of_pow_eq_one (by omega : 0 < 2) ha2
  have h4 : 4 ≤ 2 ^ n := calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) P.height
  omega

private theorem noncyclic_not_le_U_of_disjoint (A X : Subgroup S)
    (hA : Nat.card A = 2 ^ n) (hAU : A ≤ P.U) (hdisj : Disjoint A X)
    (hcyc : ¬ IsCyclic X) : ¬ X ≤ P.U := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  intro hXU
  have hT := P.noncyclic_base_contains_T X hXU hcyc
  have hdvd : 2 ∣ Nat.card A := by
    rw [hA]
    exact dvd_pow_self _ (by have := P.height; omega)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hdvd
  have haU := hAU a.property
  have ha2 : (a : S) ^ 2 = 1 := by
    have he := pow_orderOf_eq_one a
    rw [ha] at he
    exact congrArg Subtype.val he
  have hane : (a : S) ≠ 1 := by
    intro he
    have : a = 1 := Subtype.ext he
    simp [this] at ha
  have hm : (a : S) ∈ X := by
    rcases P.base_involution_cases haU ha2 with h | h | h | h
    · exact (hane h).elim
    · rw [h]; exact hT (Subgroup.subset_closure (by simp))
    · rw [h]; exact hT (Subgroup.subset_closure (by simp))
    · rw [h]; exact hT (Subgroup.subset_closure (by simp))
  exact hane (Subgroup.disjoint_def.mp hdisj a.property hm)

include P in
public theorem invariant_disjoint_cyclic (X A : Subgroup S) [IsCyclic A] (hcard : Nat.card A = 2 ^ n)
    (hnormalizes : A ≤ Subgroup.normalizer (X : Set S)) (hdisjoint : Disjoint A X) :
    IsCyclic X ∨ X ⊔ A = ⊤ := by
  classical
  by_cases hcyc : IsCyclic X
  · exact Or.inl hcyc
  right
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  have hp : IsPGroup 2 S := IsPGroup.of_card P.card
  have hxX := P.noncyclic_contains_x X hcyc
  have hxA : P.x ∉ A := by
    intro hxA
    have hx1 := Subgroup.disjoint_def.mp hdisjoint hxA hxX
    have hxorder := P.x_orderOf
    simp [hx1] at hxorder
  have hAU := P.cyclic_le_U_of_not_x A hcard hxA
  let : IsCyclic (Subgroup.center S) := P.center_cyclic
  have hAC : Disjoint A (Subgroup.center S) :=
    (hp.disjoint_of_involution_not_mem _ _ P.x_mem_center P.x_orderOf hxA).symm
  have hXU := P.noncyclic_not_le_U_of_disjoint A X hcard hAU hdisjoint hcyc
  obtain ⟨g, hgX, hgU⟩ := SetLike.not_le_iff_exists.mp hXU
  exact P.sup_eq_top_of_outer_normalized A X hAU hAC hnormalizes hdisjoint hcard g hgX hgU
end ABG.Wreathed.Presentation
