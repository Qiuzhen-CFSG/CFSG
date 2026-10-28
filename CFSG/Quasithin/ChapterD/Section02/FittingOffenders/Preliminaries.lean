module

public import CFSG.Quasithin.ChapterD.Section02.Inheritance
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.GoldschmidtONan.Basic
public import CFSG.Quasithin.ChapterG.Section08.ThetaFaithfulness
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Preliminary reductions for Fitting offenders

A two-subgroup acts faithfully on the Fitting subgroup when `F* = F`
and the two-core is trivial: the kernel lies in both the odd Fitting
subgroup and the two-subgroup. A nontrivial such actor must act on an
odd prime core. A rank-one minimum actor has integral positive ratio at
most two. Finally, odd-order averaging and `V = [V,F(G)]` kill the common
fixed space, including the common fixed space of all starred actors when
they generate the group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.13(3), D.2.18 and D.2.20, printed pp.185, 188. The hypotheses below
are the parts of D.2.17 used in these reductions; no classification
conclusion is assumed.
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterD

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The rank-one part of D.2.13(3), independently of which odd core is moved. -/
theorem QhatStar.ratio_one_or_two_of_rank_one (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hr : rank A = 1) :
    cubicRatio ρ = 1 ∨ cubicRatio ρ = 2 := by
  have hpos := fixedCodim_pos_of_faithful ρ hf hA.1.2.1.1
  have hbound : fixedCodim ρ A ≤ 2 := by
    have h := (actionRatio_le_nat_iff ρ hA.1.2.1 2).mp
      (hA.1.2.2.2.trans_le hA.1.1)
    simpa only [hr, mul_one] using h
  have heq : cubicRatio ρ = (fixedCodim ρ A : ℝ≥0∞) := by
    rw [← hA.1.2.2.2, actionRatio, hr, Nat.cast_one, div_one]
  have hcases : fixedCodim ρ A = 1 ∨ fixedCodim ρ A = 2 := by omega
  rcases hcases with h | h <;> simp only [heq, h, Nat.cast_one, Nat.cast_ofNat] <;> simp

/-- D.2.18's ratio assertion for the actual order-two starred actor. -/
theorem source_lemma_D_2_18_ratio (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hc : Nat.card A = 2) :
    cubicRatio ρ = 1 ∨ cubicRatio ρ = 2 := by
  apply QhatStar.ratio_one_or_two_of_rank_one ρ hf hA
  simp only [rank, hc]
  exact Nat.log_pow (by decide : 1 < 2) 1

/-- The faithfulness reduction preceding D.2.18, on the literal Fitting subgroup. -/
theorem twoSubgroup_faithful_on_fitting
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
    (A : Subgroup G) (hA : IsPGroup 2 A) :
    A ⊓ centralizer (fittingSubgroup G : Set G) = ⊥ := by
  have hodd := ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hd : Disjoint A (fittingSubgroup G) :=
    disjoint_of_coprime_natCard (by rw [hn]; exact hodd.coprime_two_left.pow_left n)
  have hcentral : centralizer (fittingSubgroup G : Set G) ≤ fittingSubgroup G := by
    simpa only [hF] using centralizer_generalizedFitting_le G
  exact le_bot_iff.mp ((inf_le_inf_left A hcentral).trans hd.le_bot)

/-- Every nontrivial two-subgroup in the D.2.17 setup moves an odd prime core. -/
theorem exists_odd_primeCore_nontrivial_action
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hne : A ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ⁅pCore p G, A⁆ ≠ ⊥ := by
  by_contra! hn
  have hc : A ≤ centralizer (fittingSubgroup G : Set G) := by
    apply le_centralizer_iff.mpr
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    have hp : p.val.val.Prime := Nat.prime_of_mem_primeFactors p.val.property
    have hz : ⁅pCore p.val.val G, A⁆ = ⊥ := by
      by_cases he : p.val.val = 2
      · rw [he, hcore, commutator_bot_left]
      · exact hn _ hp (hp.odd_of_ne_two he)
    exact commutator_eq_bot_iff_le_centralizer.mp hz
  have hf := twoSubgroup_faithful_on_fitting hF hcore A hA
  exact hne (le_bot_iff.mp ((le_inf le_rfl hc).trans_eq hf))

/-- D.2.18: an order-two minimum actor moves an odd prime core and has ratio one or two. -/
theorem source_lemma_D_2_18 (hf : Function.Injective ρ)
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hc : Nat.card A = 2) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ⁅pCore p G, A⁆ ≠ ⊥) ∧
      (cubicRatio ρ = 1 ∨ cubicRatio ρ = 2) := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  exact ⟨exists_odd_primeCore_nontrivial_action hF hcore A
    (IsElementaryAbelian.isPGroup 2 A) hA.1.2.1.1,
    source_lemma_D_2_18_ratio ρ hf hA hc⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- The first assertion of D.2.20 follows from the genuine odd fixed/moved splitting. -/
theorem fixedSpace_top_eq_bot_of_fitting_moved (hcore : pCore 2 G = ⊥)
    (hV : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    fixedSpace ρ ⊤ = ⊥ := by
  have hs := Representation.GoldschmidtONan.isCompl_fixed_moved_of_odd
    (ρ := ρ) (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore)
  have he : Representation.RegularCyclicNormalClosure.displacementSpan
      ρ (fittingSubgroup G) ⊤ = subspaceCommutator ρ ⊤ (fittingSubgroup G) := by
    unfold Representation.RegularCyclicNormalClosure.displacementSpan subspaceCommutator
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq, eq_comm]
  rw [he] at hs
  have hz : fixedSpace ρ (fittingSubgroup G) = ⊥ := by
    simpa only [hV, inf_top_eq] using hs.disjoint.eq_bot
  exact le_bot_iff.mp ((fixedSpace_antitone ρ (le_top (a := fittingSubgroup G))).trans_eq hz)

omit [FiniteDimensional (ZMod 2) V] in
/-- D.2.20, including the assertion about every common centralized subspace. -/
theorem source_lemma_D_2_20 (hcore : pCore 2 G = ⊥)
    (hV : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) (hgen : Jhat ρ = ⊤) :
    fixedSpace ρ ⊤ = ⊥ ∧
      ∀ U : Submodule (ZMod 2) V,
        (∀ A ∈ QhatStar ρ, subspaceCommutator ρ U A = ⊥) → U = ⊥ := by
  have hz := fixedSpace_top_eq_bot_of_fitting_moved ρ hcore hV
  refine ⟨hz, fun U hU => le_bot_iff.mp ?_⟩
  apply le_trans (b := fixedSpace ρ ⊤) ?_ hz.le
  intro v hv a
  have ha : a.val ∈ sSup (QhatStar ρ) := by rw [← Jhat, hgen]; trivial
  rw [sSup_eq_iSup'] at ha
  refine Subgroup.iSup_induction (fun A : QhatStar ρ => A.val)
    (C := fun a => ρ a v = v) ha ?_ ?_ ?_
  · intro A a ha
    exact ((subspaceCommutator_eq_bot_iff ρ U A).mp (hU A A.property) hv) ⟨a, ha⟩
  · simp
  · intro a b ha hb
    simp only [map_mul, Module.End.mul_apply, ha, hb]

end CFSG.Quasithin.ChapterD
