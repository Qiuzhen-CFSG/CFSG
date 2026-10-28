module

public import Theory.GroupTheory.CComponent.TwoComponent.InvolutionOddCore
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived

/-!
# Two-components of binary triality involution fixed groups

Every outer involution of the genuine binary triality carrier has fixed group
isomorphic to the carrier over the half-sized field exponent. The proof combines
the established inner–coefficient coverage, normalization of the original
involution, and descent through the elementary group and its central quotient.
The smaller carrier is simple and has an explicit root involution, so its odd
core is trivial. Consequently every two-component of the original fixed group
is quasisimple. This includes the smaller exponent one.

The final conditional reduction leaves only the odd cores of centralizers of
inner involutions. It does not impose a Sylow-fixer hypothesis, nor identify the
auxiliary `Triality.Model` with the standard carrier. Odd characteristic is a
separate branch of the full-family consumer.

Sources: GLS II, Definition 2.4 and Lemma 4.11; GLS3, §§2.5 and 4.9
(`refs/KGroup/GLS2/ChapterA.tex`, `ChapterB.tex`, and
`refs/KGroup/GLS3/chapter2.tex`, `chapter4.tex`); Aschbacher–Smith,
16.1.4(4), printed p.1171 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.InvolutionTwoComponents
open EvenField EvenInvolutionGeometry OuterOdd

private theorem binary_oddCore_eq_bot (n : ℕ) (hn : 0 < n) :
    pPrimeCore 2 (BinaryCarrier n hn) = ⊥ := by
  rcases (inferInstance : (pPrimeCore 2 (BinaryCarrier n hn)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hc := pPrimeCore_coprime_card (p := 2) (G := BinaryCarrier n hn)
    rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
    have hd : 2 ∣ Nat.card (BinaryCarrier n hn) := by
      rw [← longRoot_orderOf n hn (t := 1) one_ne_zero]
      exact orderOf_dvd_natCard _
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hc hd).elim

/-- The literal fixed group of any outer involution is a genuine smaller carrier. -/
theorem binary_outer_fixed_equiv (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) (ha : orderOf a = 2)
    (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn)) :
    ∃ (m : ℕ) (hm : 0 < m), n = 2 * m ∧
      Nonempty (a.fixedSubgroup ≃* BinaryCarrier m hm) := by
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  obtain ⟨g, e, hform⟩ := Coverage.binary_inner_coefficient n hn a
  obtain ⟨m, hm, hnm, _, _, he, _⟩ :=
    fixed_model_and_residual_of_normalization_and_descent n hn a ha2 houter g e hform
      (fun m hm hnm => NormalForm.normalize_inner_coefficient n hn m hm hnm
        a ha2 houter g e hform)
      (fun m hm hnm => ⟨coefficientFixedEquivSmaller n hn m hm hnm⟩)
  exact ⟨m, hm, hnm, he⟩

/-- Descent and a concrete root involution eliminate the entire odd core. -/
theorem binary_outer_fixed_oddCore_eq_bot (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) (ha : orderOf a = 2)
    (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn)) :
    pPrimeCore 2 a.fixedSubgroup = ⊥ := by
  obtain ⟨m, hm, _, ⟨e⟩⟩ := binary_outer_fixed_equiv n hn a ha houter
  exact pPrimeCore_eq_bot_of_equiv e (binary_oddCore_eq_bot m hm)

/-- The outer-involution branch of B₂, for the genuine two-component predicate. -/
theorem binary_outer_twoComponent_quasisimple (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) (ha : orderOf a = 2)
    (houter : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn))
    (L : Subgroup a.fixedSubgroup) (hL : L.IsTwoComponent) : IsQuasisimple L :=
  (hL.isComponent_of_oddCore_eq_bot (binary_outer_fixed_oddCore_eq_bot n hn a ha houter)).2

/-- Only element-centralizer odd cores remain in the binary triality branch. -/
theorem binary_hasInvolutoryB2_of_inner_oddCore (n : ℕ) (hn : 0 < n)
    (hcore : ∀ x : BinaryCarrier n hn, orderOf x = 2 →
      pPrimeCore 2 (centralizer ({x} : Set (BinaryCarrier n hn))) = ⊥) :
    HasInvolutoryB2 (BinaryCarrier n hn) := by
  apply HasInvolutoryB2.of_fixed_oddCore_eq_bot
  intro a ha
  by_cases hi : a ∈ MulAut.innerSubgroup (BinaryCarrier n hn)
  · obtain ⟨x, hx⟩ := hi
    have ho : orderOf x = 2 :=
      (MulAut.conj_orderOf_of_center_eq_bot (binaryCarrier_center_eq_bot n hn) x).symm.trans
        ((congrArg orderOf hx).trans ha)
    change MulAut.conj x = a at hx
    rw [← hx, MulAut.fixedSubgroup_conj]
    exact hcore x ho
  · exact binary_outer_fixed_oddCore_eq_bot n hn a ha hi
end Triality.Standard.InvolutionTwoComponents
