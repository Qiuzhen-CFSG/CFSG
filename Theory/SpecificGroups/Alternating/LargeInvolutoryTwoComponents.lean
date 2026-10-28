module

public import Theory.GroupTheory.CComponent.TwoComponent.Involution
public import Theory.GroupTheory.CComponent.TwoComponent.SolvableOddCoreProducts
public import Theory.Alternating.proposition_5_2_7_8
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# B₂ for alternating groups of degree at least eight

Every automorphism is induced by a permutation. The fixed subgroup of an
involutory automorphism has a normal direct-product base: the trace-zero
permutation factor on the moved pairs and the alternating group on the fixed
points. Perfectness places a two-component in that base, retaining its relative
subnormality. For at least three moved pairs the trace-zero factor has trivial
odd core, since its normal two-group is self-centralizing. For fewer pairs it
is solvable. The fixed-point factor is likewise solvable or has trivial odd
core, so the product reduction makes the two-component quasisimple.

The argument uses the intrinsic odd core in `Subgroup.IsTwoComponent`; it does
not assume that a two-component is already an ordinary component.

Sources: GLS II, Definition 2.4; GLS III, Proposition 5.2.8(a) and the proof of
Proposition 5.2.9; Aschbacher--Smith, combined manuscript of 1 March 2004,
I.3, printed p.414.
-/

public section

open Subgroup Theory.GroupTheory
open GLS3.Chapter5

namespace alternatingGroup.InvolutionCentralizer

private theorem oddCore_eq_bot_of_twoGroup {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) : pPrimeCore 2 G = ⊥ := by
  rcases (hG.to_subgroup (pPrimeCore 2 G)).card_eq_or_dvd with h | h
  · exact (eq_bot_iff_card _).mpr h
  · exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card h).elim

/-- Faithful trace-zero permutation factors have trivial odd core. -/
theorem traceZero_factor_oddCore_eq_bot {G : Type*} [Group G] [Finite G]
    (R S : Subgroup G) (r : ℕ) (hr : 3 ≤ r)
    (hn : (R.subgroupOf (R ⊔ S)).Normal)
    (hm : IsTraceZeroPermutationModule R S r) :
    pPrimeCore 2 (R ⊔ S : Subgroup G) = ⊥ := by
  obtain ⟨eR, eS, hact⟩ := hm
  let : IsMulCommutative R := IsMulCommutative.of_comm fun a b =>
    eR.injective (by simp only [map_mul]; exact mul_comm _ _)
  have hp : IsPGroup 2 R := by
    let f : Multiplicative (traceZeroTwoSubgroup r) →*
        Multiplicative (Fin r → ZMod 2) :=
      (traceZeroTwoSubgroup r).subtype.toMultiplicative
    have hf : Function.Injective f := Subtype.val_injective
    exact (ZModModule.isPGroup_multiplicative.of_injective f hf).of_injective
      eR.toMonoidHom eR.injective
  have hc : centralizer (R : Set G) ⊓ (R ⊔ S) = R :=
    centralizer_inf_sup_eq_left_of_disjoint_complement R S
      (le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn))
      (traceZeroPermutationModule_disjoint_centralizer R S r hr ⟨eR, eS, hact⟩)
  let := hn
  apply pPrimeCore_eq_bot_of_selfCentralizing (R.subgroupOf (R ⊔ S))
  · apply oddCore_eq_bot_of_twoGroup
    exact hp.of_injective (subgroupOfEquivOfLe (show R ≤ R ⊔ S from le_sup_left)).toMonoidHom
      (subgroupOfEquivOfLe (show R ≤ R ⊔ S from le_sup_left)).injective
  · intro g hg
    apply hc.le
    refine ⟨?_, g.property⟩
    apply mem_centralizer_iff.mpr
    intro x hx
    exact congrArg Subtype.val
      (mem_centralizer_iff.mp hg ⟨x, (show R ≤ R ⊔ S from le_sup_left) hx⟩ hx)

private theorem alternating_solvable_or_oddCore (n : ℕ) :
    Group.IsSolvable (alternatingGroup (Fin n)) ∨
      pPrimeCore 2 (alternatingGroup (Fin n)) = ⊥ := by
  by_cases hn : 5 ≤ n
  · right
    let : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa)
    rcases (inferInstance : (pPrimeCore 2 (alternatingGroup (Fin n))).Normal).eq_bot_or_eq_top
        with h | h
    · exact h
    · have hcop := pPrimeCore_coprime_card (p := 2) (G := alternatingGroup (Fin n))
      rw [h, Nat.card_congr topEquiv.toEquiv] at hcop
      have hn2 : 2 ≤ n := by omega
      let : NeZero n := ⟨by omega⟩
      let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
      have h4 : 4 ∣ n.factorial := dvd_trans (by decide : 4 ∣ Nat.factorial 5)
        (Nat.factorial_dvd_factorial hn)
      have he : 2 ∣ Nat.card (alternatingGroup (Fin n)) := by
        rw [nat_card_alternatingGroup, Nat.card_fin]
        omega
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop he).elim
  · left
    have hn4 : n ≤ 4 := by omega
    by_cases h4 : n = 4
    · subst n
      exact alternatingGroup_fin_four_isSolvable
    · let := alternatingGroup.isMulCommutative_of_card_le_three
        (α := Fin n) (by simpa using (show n ≤ 3 by omega))
      exact Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)

/-- A genuine two-component of the even centralizer of a permutation involution is quasisimple. -/
theorem permutation_fixed_twoComponent (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hσ : orderOf σ = 2)
    (L : Subgroup (automorphismFixedSubgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) σ)))
    (hL : L.IsTwoComponent) : IsQuasisimple L := by
  obtain ⟨R, S, H1, H2, t, hfixed, hH1, hRn, hdis, hcomm, hmodule,
      hindex, _hR, _hS, ⟨eH2, _heH2⟩, _ht2, ht1, ht2, _hsmall, _hfull⟩ :=
    involutionAlternatingCentralizerCoreStructure n σ hσ
  let C := automorphismFixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin n)) σ)
  let I : Subgroup (alternatingGroup (Fin n)) := L.map C.subtype
  let := hL.1.perfect
  let : Group.IsPerfect I := Group.IsPerfect.map C.subtype
  have hIC : I ≤ C := (map_le_range _ _).trans (range_subtype C).le
  have hIB : I ≤ H1 ⊔ H2 := perfect_subgroup_le_extension_base H1 H2 I t
    (hfixed ▸ hIC) ht1 ht2
  have hBC : H1 ⊔ H2 ≤ C := by
    rw [show C = (H1 ⊔ H2) ⊔ zpowers t from hfixed]
    exact le_sup_left
  let B : Subgroup C := (H1 ⊔ H2).subgroupOf C
  have hLB : L ≤ B := fun x hx => hIB (mem_map_of_mem C.subtype hx)
  obtain ⟨eprod⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commute H1 H2 hdis hcomm
  let e : B ≃* H1 × H2 := (subgroupOfEquivOfLe hBC).trans eprod.symm
  have h1 : Group.IsSolvable H1 ∨ pPrimeCore 2 H1 = ⊥ := by
    by_cases hr : 3 ≤ Fintype.card σ.cycleFactorsFinset
    · right
      subst H1
      exact traceZero_factor_oddCore_eq_bot R S _ hr hRn hmodule
    · left
      obtain ⟨P, _hi, ⟨eP⟩⟩ := hindex
      let := involutionWreath_isSolvable_of_le_two
        (Fintype.card σ.cycleFactorsFinset) (by omega)
      exact Group.isSolvable_of_isSolvable_injective
        (f := eP.toMonoidHom) eP.injective
  have h2 : Group.IsSolvable H2 ∨ pPrimeCore 2 H2 = ⊥ := by
    rcases alternating_solvable_or_oddCore (Fintype.card (Function.fixedPoints σ)) with hs | ho
    · let := hs
      exact Or.inl (Group.isSolvable_of_isSolvable_injective
        (f := eH2.toMonoidHom) eH2.injective)
    · exact Or.inr (pPrimeCore_eq_bot_of_equiv eH2 ho)
  have hq := ((hL.subgroupOf hLB).map_equiv e).isQuasisimple_prod_of_solvable_or_oddCore h1 h2
  have hqB := IsQuasisimple.of_mulEquiv (e.subgroupMap (L.subgroupOf B)).symm (hG := hq)
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLB) (hG := hqB)

end alternatingGroup.InvolutionCentralizer

namespace alternatingGroup

/-- The involutory B₂ condition for every alternating group of degree at least eight. -/
theorem large_hasInvolutoryB2 (n : ℕ) (hn : 8 ≤ n) :
    HasInvolutoryB2 (alternatingGroup (Fin n)) := by
  intro a ha L hL
  let act : Equiv.Perm (Fin n) →* MulAut (alternatingGroup (Fin n)) := MulAut.conjNormal
  obtain ⟨σ, hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    n (by omega) (by omega)).surjective a
  have hs : orderOf σ = 2 := (orderOf_injective act
    (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)) σ).symm.trans
      (hσ ▸ ha)
  subst a
  have hf : (act σ).fixedSubgroup = automorphismFixedSubgroup (act σ) := by
    ext x
    rw [MulAut.mem_fixedSubgroup]
    rfl
  let e := MulEquiv.subgroupCongr hf
  have hq := InvolutionCentralizer.permutation_fixed_twoComponent n σ hs _ (hL.map_equiv e)
  exact IsQuasisimple.of_mulEquiv (e.subgroupMap L).symm (hG := hq)

end alternatingGroup
