module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FittingActions
public import Theory.GroupTheory.PGroup.HomocyclicPrimeAction.HigherExponent
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.PResidual.PrimeToNilpotent

/-!
# A higher homocyclic radical has prime greater than five

The original conjugation action on an abelian prime core has kernel F(K):
all other prime cores commute with it, and its own inner action is trivial.
The faithful Frattini action gives the reverse kernel inclusion. Thus the
actual quotient K/F(K)≅SL₂(5) embeds in the automorphism group of this
same core. At p=5 and exponent at least p², A.1.30 excludes that embedding.
The A.3.6 prime restrictions then imply p>5.

Source: Aschbacher--Smith 3.2.14, p.585, using A.3.6 and A.1.30.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.Section02.FittingActions
open LocalModels
variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

private theorem fitting_le_coreAction_ker [IsMulCommutative (pCore p K)] :
    fittingSubgroup K ≤ (coreAction p K).ker := by
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun q => ?_
  let : Fact q.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors q.val.property⟩
  intro g hg
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change g * (x : K) * g⁻¹ = (x : K)
  by_cases he : q.val.val = p
  · have hg' : g ∈ pCore p K := he ▸ hg
    rw [show g * (x : K) = (x : K) * g from
      congrArg Subtype.val (mul_comm (⟨g,hg'⟩ : pCore p K) x),mul_inv_cancel_right]
  · rw [pCore_commute_of_ne q.val.val p he g hg x x.property,mul_inv_cancel_right]

/-- The full conjugation kernel equals the Fitting subgroup for an abelian
core in the nilpotent A.3.6 alternative. -/
theorem abelian_coreAction_ker_eq_fitting [Group.IsPerfect K]
    [IsMulCommutative (pCore p K)]
    (hn : A36Nilpotent K) (hc : A36Common K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) :
    (coreAction p K).ker = fittingSubgroup K := by
  refine le_antisymm ?_ fitting_le_coreAction_ker
  have hk := ((nilpotent_frattini_actions hn hc).2.2 p hd).2.1
  rw [← hk]
  intro g hg
  change quotientAut (frattini (pCore p K)) (coreAction p K g) = 1
  rw [show coreAction p K g = 1 from hg,map_one]

/-- The actual faithful SL₂(5) action on the original abelian prime core. -/
theorem abelian_core_SL2Five_action [Group.IsPerfect K]
    [IsMulCommutative (pCore p K)]
    (hn : A36Nilpotent K) (hc : A36Common K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) :
    ∃ f : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) →* MulAut (pCore p K),
      Function.Injective f := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hn.2.2.1
  let : Fintype F := Fintype.ofFinite F
  let r : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let eQ : (K ⧸ fittingSubgroup K) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    (QuotientGroup.quotientMulEquivOfEq hn.1).symm.trans
      (e.trans (Atlas.fieldEquivSL 2 r.symm))
  let eA : (K ⧸ fittingSubgroup K) ≃* (coreAction p K).range :=
    (QuotientGroup.quotientMulEquivOfEq (abelian_coreAction_ker_eq_fitting hn hc hd).symm).trans
      (QuotientGroup.quotientKerEquivRange (coreAction p K))
  exact ⟨(coreAction p K).range.subtype.comp (eQ.symm.trans eA).toMonoidHom,
    (coreAction p K).range.subtype_injective.comp (eQ.symm.trans eA).injective⟩

/-- The prime bound used in the actual higher homocyclic branch of 3.2.14. -/
theorem higher_homocyclic_prime_gt_five [Group.IsPerfect K]
    (hn : A36Nilpotent K) (hc : A36Common K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) {a : ℕ} (ha : 2 ≤ a)
    (e : pCore p K ≃* Multiplicative (Fin 2 → ZMod (p^a))) : 5 < p := by
  have hp3 := (RadicalStructure.radical_core (Or.inr hn) hd).2.1
  have hp5 : p ≠ 5 := by
    intro he
    subst p
    let : IsMulCommutative (pCore 5 K) :=
      ⟨⟨fun x y => e.injective (by simp only [map_mul,mul_comm])⟩⟩
    obtain ⟨f,hf⟩ := abelian_core_SL2Five_action hn hc hd
    exact HomocyclicPrimeAction.not_injective_SL2_of_higher_exponent hp3 ha e f hf
  have hp := (Fact.out : p.Prime).eq_two_or_odd'
  rcases hp with hp | ⟨k,hk⟩ <;> omega


/-- In an original nonquasisimple A.3.6 component, a prime core not of
exponent p is a higher homocyclic plane at a prime greater than five. -/
theorem higher_core_structure {E : Type*} [Group E] [Finite E]
    {C : Subgroup E} (hC : C.IsCComponent) (h : A36Conclusion C)
    (hn : ¬ IsQuasisimple C) {q : ℕ} [Fact q.Prime]
    (hexp : ¬ ∀ x : pCore q C, x ^ q = 1) :
    5 < q ∧ ∃ a : ℕ, 2 ≤ a ∧
      Nonempty (pCore q C ≃* Multiplicative (Fin 2 → ZMod (q^a))) := by
  let := hC.perfect
  have hne : Nat.card (pCore q C) ≠ 1 := by
    intro hc
    have hbot := (card_le_one_iff_eq_bot _).mp hc.le
    apply hexp
    intro x
    have hx : x = 1 := Subtype.ext (mem_bot.mp (hbot ▸ x.property))
    rw [hx,one_pow]
  have hd : q ∣ Nat.card (fittingSubgroup C) :=
    (pCore_isPGroup.card_eq_or_dvd.resolve_left hne).trans
      (card_dvd_of_le (pCore_le_fitting C q))
  have hnil : A36Nilpotent C := by
    rcases RadicalStructure.nonsimple_radical h hn with hnat | hnil
    · have he := (RadicalStructure.natural_core hnat hd).2.1
      exact (hexp (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p)).elim
    · exact hnil
  obtain ⟨_,_,he | he | he⟩ := RadicalStructure.radical_core (Or.inr hnil) hd
  · exact (hexp (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.1.exponent_dvd_p)).elim
  · exact (hexp he.2).elim
  · obtain ⟨a,ha,⟨e⟩⟩ := he
    have ha2 : 2 ≤ a := by
      by_contra hsmall
      have ha1 : a = 1 := by omega
      apply hexp
      intro x
      apply e.injective
      rw [map_pow,map_one]
      apply Multiplicative.toAdd.injective
      funext i
      change q • (e x).toAdd i = 0
      have hz : (q ^ a) • (e x).toAdd i = 0 := by rw [nsmul_eq_mul]; simp
      simpa only [ha1,pow_one] using hz
    exact ⟨higher_homocyclic_prime_gt_five hnil h.2 hd ha2 e,a,ha2,⟨e⟩⟩


/-- The primary part of the original solvable radical maps to the actual
prime core in the two-core-free A.3.6 group. -/
theorem radical_primeToResidual_image (hc : A36Common K) (ho : Odd p) :
    (primeToResidual p (solvableRadical K)).map (solvableRadical K).subtype = pCore p K := by
  have hFR : fittingSubgroup K ≤ solvableRadical K :=
    le_solvableRadical _ inferInstance inferInstance
  let F := (fittingSubgroup K).subgroupOf (solvableRadical K)
  let e : F ≃* fittingSubgroup K := subgroupOfEquivOfLe hFR
  have hnil : Group.IsNilpotent F := Group.nilpotent_of_mulEquiv e.symm
  have hcop : Nat.Coprime p F.index := by
    rcases hc.2.2.1 with ⟨_,_,hi⟩ | ⟨_,he,_⟩
    · change Nat.Coprime p ((fittingSubgroup K).relIndex (solvableRadical K))
      rw [hi]
      exact ho.coprime_two_right
    · change Nat.Coprime p ((fittingSubgroup K).subgroupOf (solvableRadical K)).index
      rw [he,subgroupOf_self,index_top]
      exact Nat.coprime_one_right p
  rw [primeToResidual_eq_pCore_of_nilpotent_normal F hnil hcop]
  exact map_pCore_eq_of_normal_of_le _ ((pCore_le_fitting K p).trans hFR)

end CFSG.Quasithin.Chapter1.Section02.FittingActions
