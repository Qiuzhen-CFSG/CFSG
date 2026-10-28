module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Rows
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.PSL3Four.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ThreeRank
/-!
# Rank bounds in the retained PSL3(4) and J2 quotient models

Both models have cubic rank at least two, while every ordinary component fixed by an involution has cubic rank at most one. Their exact orders have no square of a prime at least seven, excluding two independent prime-field components.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.PrimeRows

private theorem three_rank_le_one_of_nine_not_dvd {D : Type*} [Group D] [Finite D]
    (h : ¬ 9 ∣ Nat.card D) : primeRank 3 D ≤ 1 := by
  let P : Sylow 3 D := default
  apply P.primeRank_le_one_of_isCyclic
  obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
  have hs : k ≤ 1 := by
    by_contra! hn
    exact h ((hk ▸ pow_dvd_pow 3 (show 2 ≤ k by omega)).trans
      (P : Subgroup D).card_subgroup_dvd_card)
  apply isCyclic_of_card_dvd_prime (p := 3)
  rw [hk]
  simpa using pow_dvd_pow 3 hs

private theorem perfect_le_two_residual {D : Type*} [Group D] [Finite D]
    (B : Subgroup D) [Group.IsPerfect B] : B ≤ pResidual 2 D := by
  let : Group.IsNilpotent (D ⧸ pResidual 2 D) :=
    (Subgroup.isPGroup_quotient_pResidual (G := D) 2).isNilpotent
  exact (le_solvableResidual_of_isPerfect B).trans
    (solvableResidual_le_of_solvable_quotient (pResidual 2 D))

/-- Every ordinary component fixed by any involution of PSL₃(4) has cubic rank at most one. -/
theorem linear_four_fixed_component_three_rank
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (a : MulAut PSL(3,F)) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) :
    primeRank 3 B ≤ 1 := by
  let : IsQuasisimple B := hB.2
  have hle := perfect_le_two_residual B
  apply three_rank_le_one_of_nine_not_dvd
  intro hd
  rcases Matrix.PSL3Even.InvolutionResidualRows.fixed_component_rows
    (by decide : 0 < 2) (by simpa using hF) a ha with hs | hf | hg | hu
  · let := hs
    exact hB.isCComponent.not_isSolvable inferInstance
  · obtain ⟨_,σ,_,_,_,_,m,hm,hnm,hK,⟨er⟩⟩ := hf
    have hm1 : m = 1 := by omega
    have hK2 : Nat.card (FixedBy.subfield F σ) = 2 := by simpa [hm1] using hK
    let f : B →* PSL(3,FixedBy.subfield F σ) :=
      (commutator PSL(3,FixedBy.subfield F σ)).subtype.comp
        (er.toMonoidHom.comp (inclusion hle))
    have hi : Function.Injective f := Subtype.val_injective.comp
      (er.injective.comp (inclusion_injective hle))
    have hc := Matrix.PSL3.LinearThree.card_projective_mul_scalar (FixedBy.subfield F σ)
    have hK2' : Nat.card {x : F // σ x = x} = 2 := hK2
    norm_num [hK2'] at hc
    have hdiv := hd.trans (card_dvd_of_injective f hi)
    rw [hc] at hdiv
    norm_num at hdiv
  · obtain ⟨_,_,_,⟨er⟩⟩ := hg
    let f : B →* PSL(2,F) := (commutator PSL(2,F)).subtype.comp
      (er.toMonoidHom.comp (inclusion hle))
    have hi : Function.Injective f := Subtype.val_injective.comp
      (er.injective.comp (inclusion_injective hle))
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
    norm_num [hF,Fin.prod_univ_succ] at hc
    have hdiv := hd.trans (card_dvd_of_injective f hi)
    omega
  · obtain ⟨m,_,hm,hnm,_⟩ := hu
    omega

/-- Every ordinary component fixed by any involution of J₂ has cubic rank at most one. -/
theorem j2_fixed_component_three_rank
    (a : MulAut Sporadic.LeechRelated.J2.Carrier) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) :
    primeRank 3 B ≤ 1 := by
  apply three_rank_le_one_of_nine_not_dvd
  by_cases hi : ∃ g, a = MulAut.conj g
  · obtain ⟨e⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Inner.inner_component_equiv
      a ha hi B hB
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  · have ho : a ∉ (MulAut.conj : Sporadic.LeechRelated.J2.Carrier →* _).range := by
      rintro ⟨g,hg⟩
      exact hi ⟨g,hg.symm⟩
    obtain ⟨e⟩ := Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.outer_component_equiv
      a ha ho B hB
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_PSL]
    decide

/-- The two retained quotient models have no involution-fixed ordinary component of cubic rank two. The new involution need not be the actor marking the retained row. -/
theorem prime_fixed_quotient_involution_component_three_rank
    {D : Type*} [Group D] [Finite D] (a : MulAut D)
    (hm : PrimeFixedQuotientModels D a) (b : MulAut D) (hb : orderOf b = 2)
    (B : Subgroup b.fixedSubgroup) (hB : IsComponent b.fixedSubgroup B) :
    primeRank 3 B ≤ 1 := by
  rcases hm with ⟨F,_,_,hF,e,_⟩ | ⟨e,_⟩
  · let f := MulAut.fixedSubgroupCongr e b
    rw [primeRank_equiv 3 (f.subgroupMap B)]
    exact linear_four_fixed_component_three_rank hF (MulAut.congr e b)
      (((MulAut.congr e).orderOf_eq b).trans hb) (B.map f.toMonoidHom) (hB.map_equiv f)
  · let f := MulAut.fixedSubgroupCongr e b
    rw [primeRank_equiv 3 (f.subgroupMap B)]
    exact j2_fixed_component_three_rank (MulAut.congr e b)
      (((MulAut.congr e).orderOf_eq b).trans hb) (B.map f.toMonoidHom) (hB.map_equiv f)
/-- Both retained central quotients have cubic rank at least two. -/
theorem prime_fixed_quotient_three_rank_ge_two
    {D : Type*} [Group D] [Finite D] (a : MulAut D)
    (hm : PrimeFixedQuotientModels D a) : 2 ≤ primeRank 3 D := by
  rcases hm with ⟨F,_,_,hF,e,_⟩ | ⟨e,_⟩
  · let : Fintype F := Fintype.ofFinite F
    let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite Matrix.PSL3Four.F
    let f : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
      simp only [← Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
    rw [primeRank_equiv 3 (e.trans (Atlas.fieldEquivPSL 3 f))]
    exact Matrix.PSL3Four.ThreeRank.three_rank_ge_two
  · rw [primeRank_equiv 3 e]
    exact Sporadic.LeechRelated.J2.three_rank_ge_two

/-- The retained quotient rows contain at most one factor of any prime at least seven. -/
theorem prime_fixed_quotient_prime_square_not_dvd
    {D : Type*} [Group D] [Finite D] (a : MulAut D)
    (hm : PrimeFixedQuotientModels D a) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ^ 2 ∣ Nat.card D := by
  have hcard : Nat.card D = 20160 ∨ Nat.card D = 604800 := by
    rcases hm with ⟨F,_,_,hF,e,_⟩ | ⟨e,_⟩
    · apply Or.inl
      rw [Nat.card_congr e.toEquiv]
      have hc := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
      norm_num [hF] at hc
      omega
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans
        Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier)
  intro hd
  have hpd : p ∣ Nat.card D := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  rcases hcard with hc | hc
  all_goals
    rw [hc] at hd hpd
    have hfac := Nat.mem_primeFactors.mpr ⟨hp,hpd,by omega⟩
  · have he : Nat.primeFactors 20160 = {2,3,5,7} := by decide +kernel
    rw [he] at hfac
    simp only [Finset.mem_insert,Finset.mem_singleton] at hfac
    have hp_eq : p = 7 := by omega
    subst p
    norm_num at hd
  · have he : Nat.primeFactors 604800 = {2,3,5,7} := by decide +kernel
    rw [he] at hfac
    simp only [Finset.mem_insert,Finset.mem_singleton] at hfac
    have hp_eq : p = 7 := by omega
    subst p
    norm_num at hd

/-- Two independent prime-field components cannot embed in either retained quotient. -/
theorem prime_fixed_quotient_no_prime_pair_embedding
    {D : Type*} [Group D] [Finite D] (a : MulAut D)
    (hm : PrimeFixedQuotientModels D a) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (f : PSL(2,ZMod p) × PSL(2,ZMod p) →* D) (hf : Function.Injective f) : False := by
  let : Fact p.Prime := ⟨hp⟩
  have hpc : p ∣ Nat.card PSL(2,ZMod p) := by
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := ZMod p) (by simpa using hp.odd_of_ne_two (by omega))
    rw [Nat.card_zmod] at hc
    have hd : p ∣ Nat.card PSL(2,ZMod p) * 2 := by rw [hc]; exact dvd_mul_right _ _
    rcases hp.dvd_mul.mp hd with hd | hd
    · exact hd
    · have := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega
  apply prime_fixed_quotient_prime_square_not_dvd a hm hp hp7
  have hd := card_dvd_of_injective f hf
  rw [Nat.card_prod] at hd
  have hs : p ^ 2 ∣ Nat.card PSL(2,ZMod p) * Nat.card PSL(2,ZMod p) := by
    simpa only [pow_two] using Nat.mul_dvd_mul hpc hpc
  exact hs.trans hd

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.PrimeRows
