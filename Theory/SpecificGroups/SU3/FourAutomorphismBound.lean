module

public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Unconditional
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions
public import Theory.SpecificGroups.SU3.ProjectiveGraphFixed
public import Theory.SpecificGroups.SU3.FourOuterAction
public import Theory.SpecificGroups.SU3.CyclicNormalOuter
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.ElementaryAbelian.Quotient
public import BenderSuzuki.External.Huppert.II.theorem_6_14


/-!
# Abelian two-subgroups of Aut(PSU₃(4))

An abelian automorphism two-subgroup of rank at least three contains a
noninner involution: the actual projective group has two-rank two. Every
such involution has fixed subgroup SL₂(4), of order sixty. The inner kernel
of the abelian subgroup therefore embeds in that fixed subgroup and has
order at most four. Its outer image has order at most four as well.

The latter bound follows from proved semilinear coverage. Unitary conjugation
is inner at this parameter, so the outer quotient is cyclic; the field
part has fourth power one. All groups, automorphisms, fixed subgroups and
quotients here are the literal ones attached to the stored Hermitian form.

Source: GLS4, Chapter 4, Lemmas 3.4(c) and 3.5(b), and the final paragraph
of Chapter 2, Section 13 (`refs/KGroup/GLS4/Chapter2.tex`).
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace BenderSuzuki.MatrixGroups.HermitianForm.FourAutomorphismBound

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
  (hcard : Nat.card E = 4 ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 4)

private instance : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

include hJ hcard hfixed in
/-- The actual outer quotient has order dividing four. -/
theorem outer_card_dvd_four :
    Nat.card (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) ∣ 4 := by
  have hconj := External.huppert_II_10_4_conj_eq_frobenius J 4 hcard hfixed
  have hcover := J.semilinear_coverage 2 (by decide) hJ hcard hfixed
  have hb : J.unitaryOuterHom.range = ⊥ := by
    apply bot_unique
    rintro _ ⟨u, rfl⟩
    apply mem_bot.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [J.unitaryConjHom_apply]
    exact J.unitaryConj_mem_inner_of_fourth_power_conj hconj u
  let := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hcover
  let := J.outer_mod_unitary_isCyclic_of_semilinear_coverage hJ hcover
  let e := (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
  let : IsCyclic (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    e.isCyclic.mp inferInstance
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)) x
  rw [← map_pow]
  obtain ⟨σ, hσ⟩ := hcover a
  exact (QuotientGroup.eq_one_iff _).mpr
    (J.fourth_power_mem_inner_of_semilinear hJ hcard hconj hσ)

include hJ hcard hfixed in
/-- Every noninner involution has a fixed subgroup of order sixty. -/
theorem outer_involution_fixed_card
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ b, a = MulAut.conj b) : Nat.card a.fixedSubgroup = 60 := by
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 4)
    (by norm_num [← Nat.card_eq_fintype_card] at hcard ⊢; exact hcard)
  obtain ⟨c, hc⟩ := J.outer_involution_conjugate 2 (by decide) hJ hcard hfixed
    (J.projectiveGraphAut_isEntrywiseConjugation hJ) a ha houter
  rw [← hc, ← Nat.card_congr
    (MulAut.fixedSubgroupCongr c (J.projectiveGraphAut hJ)).toEquiv]
  let e := (J.projectiveGraphFixedEquivSpecial hJ).trans
    (J.specialGraphFixedEquivSL2 hJ)
  rw [Nat.card_congr e.toEquiv, External.huppert614_card_specialLinearGroup]
  have hf : Nat.card (FixedBy.subfield E J.conj) = 4 := hfixed
  rw [hf]
  norm_num

private noncomputable def innerLift {G A : Type*} [Group G] [Group A]
    (hz : center G = ⊥) (f : A →* MulAut G)
    (hi : ∀ x, f x ∈ MulAut.innerSubgroup G) : A →* G :=
  (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)).symm.toMonoidHom.comp
    (f.codRestrict (MulAut.innerSubgroup G) hi)

private theorem conj_innerLift {G A : Type*} [Group G] [Group A]
    (hz : center G = ⊥) (f : A →* MulAut G)
    (hi : ∀ x, f x ∈ MulAut.innerSubgroup G) (x : A) :
    MulAut.conj (innerLift hz f hi x) = f x :=
  congrArg Subtype.val ((MonoidHom.ofInjective
    (MulAut.conj_injective_of_center_eq_bot hz)).apply_symm_apply ⟨f x, hi x⟩)

private theorem innerLift_injective {G A : Type*} [Group G] [Group A]
    (hz : center G = ⊥) (f : A →* MulAut G)
    (hi : ∀ x, f x ∈ MulAut.innerSubgroup G) (hf : Function.Injective f) :
    Function.Injective (innerLift hz f hi) := by
  intro x y h
  apply hf
  rw [← conj_innerLift hz f hi x, ← conj_innerLift hz f hi y, h]

private theorem exists_outer_involution {G : Type*} [Group G] [Finite G]
    (hz : center G = ⊥) (hr : primeRank 2 G ≤ 2)
    (B : Subgroup (MulAut G)) (hB : 3 ≤ primeRank 2 B) :
    ∃ a ∈ B, a ^ 2 = 1 ∧ ¬ ∃ b, a = MulAut.conj b := by
  by_contra! h
  obtain ⟨A, hA, hc⟩ := exists_elementaryAbelian_card_primeRank (G := B) (p := 2)
  let := hA
  let f : A →* MulAut G := B.subtype.comp A.subtype
  have hi : ∀ x, f x ∈ MulAut.innerSubgroup G := by
    intro x
    obtain ⟨b, hb⟩ := h x.val.val x.val.property
      (congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian x.val x.property))
    exact ⟨b, hb.symm⟩
  let g := innerLift hz f hi
  have hg : Function.Injective g := innerLift_injective hz f hi
    (Subtype.val_injective.comp Subtype.val_injective)
  let : IsElementaryAbelian 2 g.range :=
    IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have he : Nat.card g.range = 2 ^ primeRank 2 B :=
    (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm.trans hc
  have hl := IsElementaryAbelian.primeRank_ge_of_card g.range he
  omega

include hJ hcard hfixed in
/-- Rank-three abelian two-subgroups of Aut(PSU₃(4)) have order at most sixteen. -/
theorem abelian_twoGroup_card_le_sixteen
    (B : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hB : IsPGroup 2 B) (hcomm : IsMulCommutative B)
    (hr : 3 ≤ primeRank 2 B) : Nat.card B ≤ 16 := by
  let := hcomm
  have hconj := External.huppert_II_10_4_conj_eq_frobenius J 4 hcard hfixed
  have hz := EvenProjectiveComparison.center_eq_bot J (n := 2) (by decide) hcard hconj
  have hgr := EvenTwoRank.two_rank J (n := 2) (by decide) hcard hconj
  obtain ⟨a, haB, ha, hao⟩ := exists_outer_involution hz hgr.le B hr
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  let f := q.comp B.subtype
  let k : f.ker →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
    B.subtype.comp f.ker.subtype
  have hi : ∀ x, k x ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
    intro x
    exact (QuotientGroup.eq_one_iff _).mp x.property
  let g := innerLift hz k hi
  have hg : Function.Injective g := innerLift_injective hz k hi
    (Subtype.val_injective.comp Subtype.val_injective)
  have hfix (x : f.ker) : a (g x) = g x := by
    apply MulAut.conj_injective_of_center_eq_bot hz
    have he : MulAut.conj (a (g x)) = a * MulAut.conj (g x) * a⁻¹ := by
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    rw [he, conj_innerLift]
    have hcomm' : a * k x = k x * a :=
      congrArg Subtype.val (mul_comm (⟨a, haB⟩ : B) x.val)
    rw [hcomm', mul_inv_cancel_right]
  let ψ : f.ker →* a.fixedSubgroup := g.codRestrict _
    (fun x => (MulAut.mem_fixedSubgroup a _).mpr (hfix x))
  have hψ : Function.Injective ψ := fun x y h => hg (congrArg Subtype.val h)
  have hd : Nat.card f.ker ∣ 60 := by
    rw [← outer_involution_fixed_card J hJ hcard hfixed a ha hao]
    exact card_dvd_of_injective ψ hψ
  have hk : Nat.card f.ker ≤ 4 := by
    obtain ⟨m, hm⟩ := (hB.to_subgroup f.ker).exists_card_eq
    rw [hm] at hd ⊢
    have hm2 : m ≤ 2 := by
      by_contra! hh
      have h8 : 8 ∣ 60 := (pow_dvd_pow 2 hh).trans hd
      norm_num at h8
    exact Nat.pow_le_pow_right (by decide) hm2
  have him : Nat.card f.range ≤ 4 :=
    (card_le_card_group f.range).trans
      (Nat.le_of_dvd (by decide) (outer_card_dvd_four J hJ hcard hfixed))
  rw [← f.ker.card_mul_index, index_ker]
  exact Nat.mul_le_mul hk him

end BenderSuzuki.MatrixGroups.HermitianForm.FourAutomorphismBound
