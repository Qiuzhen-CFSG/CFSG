module

public import Theory.GroupTheory.PGroup.NormalAbelian
public import Theory.GroupTheory.PGroup.CyclicSelfCentralizerFour
public import Theory.GroupTheory.PGroup.Omega
public import Theory.Frattini.PGroup

/-!
# Normal four-groups in finite two-groups of rank at least three

A finite two-group containing an elementary abelian subgroup of order at least
eight has a normal elementary abelian subgroup of order four.

Choose a self-centralizing normal abelian subgroup `D`. If `D` is noncyclic,
its characteristic subgroup `Ω₁(D)` has order at least four: otherwise the
quotient of `D` by squares has order at most two, and Frattini nongeneration
would make `D` cyclic. The normal subgroup theorem for finite p-groups then
extracts the required four-group from `Ω₁(D)`. The cyclic case is supplied by
`IsPGroup.exists_normal_four_of_cyclic_selfcentralizer`.

This proves the binary rank-at-least-three consequence of
Gorenstein–Lyons–Solomon, *The Classification of the Finite Simple Groups*,
Number 2, Chapter C, Lemma 10.11 (`refs/KGroup/GLS2/ChapterC.tex`).
-/

open scoped IsMulCommutative

private theorem cyclic_of_square_kernel_bound
    {D : Type*} [CommGroup D] [Finite D] (hD : IsPGroup 2 D)
    (hker : Nat.card (powMonoidHom 2 : D →* D).ker ≤ 2) : IsCyclic D := by
  let : Fact (IsPGroup 2 D) := ⟨hD⟩
  let squares := (powMonoidHom 2 : D →* D).range
  have hindex : squares.index ≤ 2 := by rwa [Subgroup.index_range]
  have hpositive := Nat.card_pos (α := D ⧸ squares)
  have hdiv : Nat.card (D ⧸ squares) ∣ 2 := by
    change Nat.card (D ⧸ squares) ≤ 2 at hindex
    interval_cases Nat.card (D ⧸ squares) <;> norm_num
  let : IsCyclic (D ⧸ squares) := isCyclic_of_card_dvd_prime hdiv
  obtain ⟨q, hq⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (D ⧸ squares))
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective squares q
  have hmap : (Subgroup.zpowers d).map (QuotientGroup.mk' squares) = ⊤ := by
    simpa using hq
  have hsup : Subgroup.zpowers d ⊔ squares = ⊤ := by
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using
      congrArg (Subgroup.comap (QuotientGroup.mk' squares)) hmap
  have hsquares : squares ≤ frattini D := by
    rintro y ⟨d, rfl⟩
    exact pth_power_mem_frattini_of_isPGroup (p := 2) d
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨d, frattini_nongenerating (G := D) ?_⟩
  apply top_unique
  rw [← hsup]
  exact sup_le_sup_left hsquares _

namespace IsPGroup

/-- A finite two-group containing an elementary abelian subgroup of order at
least eight has a normal elementary abelian subgroup of order four. -/
public theorem exists_normal_elementaryAbelian_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A) :
    ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  classical
  obtain ⟨D, hDn, hDa, hDC⟩ := exists_normal_abelian_selfCentralizing hP
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  by_cases hDcyclic : IsCyclic D
  · let : IsCyclic D := hDcyclic
    exact hP.exists_normal_four_of_cyclic_selfcentralizer D hDC A hA
  let O := omega₁ (G := D) (p := 2)
  let : O.Characteristic := omega₁_characteristic D
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative D
  let N := O.map D.subtype
  let : N.Normal := inferInstance
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.map_subtype
  have hcardN : Nat.card N = Nat.card O :=
    Subgroup.card_map_of_injective D.subtype_injective
  obtain ⟨k, hk⟩ := (hP.to_subgroup N).exists_card_eq
  have hklarge : 2 ≤ k := by
    by_contra hsmall
    have hNsmall : Nat.card N ≤ 2 := by
      rw [hk]
      have hkone : k ≤ 1 := by omega
      exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hkone).trans (by norm_num)
    apply hDcyclic
    apply cyclic_of_square_kernel_bound (hP.to_subgroup D)
    have hker : (powMonoidHom 2 : D →* D).ker ≤ O := by
      intro x hx
      apply Subgroup.subset_closure
      change x ^ (2 ^ 1) = 1
      simpa only [pow_one] using (show x ^ 2 = 1 from hx)
    exact (Nat.le_of_dvd (Nat.card_pos (α := O))
      (Subgroup.card_dvd_of_le hker)).trans (hcardN ▸ hNsmall)
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  obtain ⟨E, hEn, hEN, hEcard⟩ :=
    exists_normal_subgroup_card_pow_of_normal (p := 2) N inferInstance hk 2 hklarge
  refine ⟨E, hEn, ?_, by simpa using hEcard⟩
  have hEa : IsMulCommutative E := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    exact congrArg (fun z : N => (z : P))
      (mul_comm (⟨x, hEN x.property⟩ : N) ⟨y, hEN y.property⟩)
  refine { toIsMulCommutative := hEa
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : P) (hEN x.property))

end IsPGroup
