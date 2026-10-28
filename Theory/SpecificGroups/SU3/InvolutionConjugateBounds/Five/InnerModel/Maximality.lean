module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.Inputs
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.Standard
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.GroupAction.SimpleCosets
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Maximality of every embedded A₇ in PSU₃(5)

The group order is 126000 and the projective split torus has order eight.
An embedded A₇ has index fifty. Faithful coset actions of the inherited
simple ambient group exclude proper overgroups of index two, five or ten;
thus a strict proper overgroup has index twenty-five and normalizes A₇.
The order-eight cyclic subgroup fixes a coset of any odd-index subgroup,
so this overgroup contains an element of order eight.

Every automorphism of A₇ is induced by a permutation on seven letters.
Such a permutation of two-power order has fourth power one. Consequently
the fourth power of our element is an involution centralizing A₇. This is
impossible: A₇ is perfect of three-rank at least two, whereas the first
commutator of each projective involution centralizer has three-rank at most
one. This proves maximality without any subgroup-classification premise.
The embedding itself remains to be constructed.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11; Huppert II.10.12 for the order and torus, GLS3 Theorem
5.2.1 for Aut(A₇), and Aschbacher–Smith A.3.21(a) for the centralizer calculation.
-/

public section

open Subgroup Equiv BenderSuzuki.MatrixGroups Theory.GroupTheory
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem field_card : Nat.card (GaloisField 5 (2 * 1)) = 5 ^ 2 :=
  GaloisField.card 5 (2 * 1) (by decide)

private theorem fixed_card : Nat.card {x : GaloisField 5 (2 * 1) // standardForm.conj x = x} = 5 := by
  simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
    standardForm.conj 5 1 (by decide) field_card
    (by intro x; simp only [standardForm, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one])

/-- The order of the actual projective matrix group, including division by its scalar kernel. -/
theorem standardGroup_card : Nat.card StandardGroup = 126000 := by
  simpa using Representation.SU3.BinaryDegree.card_projective standardForm field_card fixed_card

/-- The projective image of the standard split torus supplies an element of order eight. -/
theorem standardGroup_exists_order_eight : ∃ x : StandardGroup, orderOf x = 8 := by
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv standardForm 5 field_card fixed_card
  obtain ⟨_, _, _, _, _, _, ht, _⟩ := BenderSuzuki.External.huppert_II_10_12
    (FormTransport.standardForm standardForm) 5 field_card fixed_card rfl
  obtain ⟨R, H, _, _, _, _, _, hc, _, _, _, hH, _⟩ := ht
  let := hc
  have hH8 : Nat.card H = 8 := by simpa using hH
  let : Finite H := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hc
  refine ⟨e.symm (x : ProjectiveSpecialUnitaryMatrixGroup _), ?_⟩
  rw [e.symm.orderOf_eq, Subgroup.orderOf_coe, hx, hH8]

private theorem a7_card : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

private theorem perm_seven_pow_four (a : Perm (Fin 7)) (ha : a ^ 8 = 1) : a ^ 4 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have hd : n ∣ 8 := (Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one ha)
  have hle : n ≤ 7 := (Perm.le_card_support_of_mem_cycleType hn).trans
    ((Finset.card_le_univ _).trans_eq (Fintype.card_fin 7))
  interval_cases n <;> norm_num at hd <;> norm_num

private theorem aut_seven_pow_four (a : MulAut (alternatingGroup (Fin 7))) (ha : a ^ 8 = 1) :
    a ^ 4 = 1 := by
  let c : Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) := MulAut.conjNormal
  have hb := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide)
  obtain ⟨s, rfl⟩ := hb.surjective a
  have hs : s ^ 8 = 1 := hb.injective (by simpa only [map_pow, map_one] using ha)
  simpa only [map_pow, map_one] using congrArg c (perm_seven_pow_four s hs)

private theorem proper_overgroup_index {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 126000) (H K : Subgroup G) (hH : Nat.card H = 2520)
    (hHK : H < K) (hK : K ≠ ⊤) : K.index = 25 ∧ H.relIndex K = 2 := by
  have hi : H.index = 50 := by
    have hh := H.index_mul_card
    rw [hH, hG] at hh
    omega
  have hd : K.index ∣ 50 := hi ▸ index_dvd_of_le hHK.le
  have hn : K.index < 50 := hi ▸ index_strictAnti hHK
  have hfact := K.card_dvd_factorial_index_of_simple hK
  rw [hG] at hfact
  have hmem : K.index ∈ (50 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hcases : K.index = 1 ∨ K.index = 2 ∨ K.index = 5 ∨ K.index = 10 ∨
      K.index = 25 ∨ K.index = 50 := by
    simpa only [show (50 : ℕ).divisors = {1, 2, 5, 10, 25, 50} by decide,
      Finset.mem_insert, Finset.mem_singleton] using hmem
  have hk25 : K.index = 25 := by
    rcases hcases with hh | hh | hh | hh | hh | hh
    · exact False.elim (hK (index_eq_one.mp hh))
    · norm_num [hh, Nat.factorial] at hfact
    · norm_num [hh, Nat.factorial] at hfact
    · norm_num [hh, Nat.factorial] at hfact
    · exact hh
    · omega
  refine ⟨hk25, ?_⟩
  have hh := relIndex_mul_index hHK.le
  rw [hk25, hi] at hh
  omega

private theorem eight_in_odd_index {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hK : ¬ 2 ∣ K.index) (x : G) (hx : orderOf x = 8) :
    ∃ y : G, y ∈ K ∧ orderOf y = 8 := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_zpowers, hx]; rfl)
  obtain ⟨a, ha⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ K) hK
  obtain ⟨g, rfl⟩ := Quotient.mk_surjective a
  have he := ha (⟨x, mem_zpowers x⟩ : zpowers x)
  have hmem : g⁻¹ * x * g ∈ K := by
    have hh : (QuotientGroup.mk (x * g) : G ⧸ K) = QuotientGroup.mk g := he
    have hh' := QuotientGroup.eq.mp hh.symm
    simpa only [mul_assoc] using hh'
  refine ⟨g⁻¹ * x * g, hmem, ?_⟩
  simpa only [MulAut.conj_apply, inv_inv] using ((MulAut.conj g⁻¹).orderOf_eq x).trans hx

private theorem a7_not_centralizes_involution (f : alternatingGroup (Fin 7) →* StandardGroup)
    (hf : Function.Injective f) (z : StandardGroup) (hz : orderOf z = 2) :
    ¬ f.range ≤ centralizer ({z} : Set StandardGroup) := by
  intro h
  let : Finite StandardGroup := Nat.finite_of_card_ne_zero (by rw [standardGroup_card]; decide)
  let C := centralizer ({z} : Set StandardGroup)
  let g : alternatingGroup (Fin 7) →* C := f.codRestrict C (fun x => h ⟨x, rfl⟩)
  have hg : Function.Injective g := fun x y h => hf (congrArg Subtype.val h)
  have hperfect : commutator (alternatingGroup (Fin 7)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have hgmem : ∀ x, g x ∈ commutator C := by
    intro x
    have hh := mem_map_of_mem g (hperfect ▸ mem_top x)
    rw [map_commutator_eq] at hh
    exact commutator_mono le_top le_top hh
  let j : alternatingGroup (Fin 7) →* commutator C := g.codRestrict _ hgmem
  have hj : Function.Injective j := fun x y h => hg (congrArg Subtype.val h)
  have hlow := (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 7)).trans
    (primeRank_le_of_injective 3 j hj)
  have hup := Matrix.SU3.InnerThreeRank.standard_projective_centralizer_rank 5 (by decide) z hz
  change primeRank 3 (commutator C) ≤ 1 at hup
  omega

private theorem no_eight_normalizer (f : alternatingGroup (Fin 7) →* StandardGroup)
    (hf : Function.Injective f) (x : normalizer (f.range : Set StandardGroup))
    (hx : orderOf (x : StandardGroup) = 8) : False := by
  let : Finite StandardGroup := Nat.finite_of_card_ne_zero (by rw [standardGroup_card]; decide)
  let e := MonoidHom.ofInjective hf
  let a : MulAut (alternatingGroup (Fin 7)) := MulAut.congr e.symm (f.range.normalizerMonoidHom x)
  have hx8 : x ^ 8 = 1 := by
    apply Subtype.ext
    exact hx ▸ pow_orderOf_eq_one (x : StandardGroup)
  have ha8 : a ^ 8 = 1 := by
    change ((MulAut.congr e.symm).toMonoidHom.comp f.range.normalizerMonoidHom) x ^ 8 = 1
    rw [← map_pow, hx8, map_one]
  have ha4 := aut_seven_pow_four a ha8
  have hc4 : f.range.normalizerMonoidHom (x ^ 4) = 1 := by
    apply (MulAut.congr e.symm).injective
    simpa only [map_pow, map_one] using ha4
  have hc : (x : StandardGroup) ^ 4 ∈ centralizer (f.range : Set StandardGroup) := by
    have hh : x ^ 4 ∈ f.range.normalizerMonoidHom.ker := hc4
    rw [normalizerMonoidHom_ker] at hh
    exact hh
  have hz : orderOf ((x : StandardGroup) ^ 4) = 2 := by rw [orderOf_pow, hx]; decide
  apply a7_not_centralizes_involution f hf _ hz
  intro y hy
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc y hy)

/-- Every genuine embedding of A₇ has maximal proper image in the standard PSU₃(5). -/
theorem alternatingSeven_range_isCoatom [IsSimpleGroup StandardGroup]
    (f : alternatingGroup (Fin 7) →* StandardGroup) (hf : Function.Injective f) :
    IsCoatom f.range := by
  let : Finite StandardGroup := Nat.finite_of_card_ne_zero (by rw [standardGroup_card]; decide)
  have hH : Nat.card f.range = 2520 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv).trans a7_card
  refine ⟨?_, ?_⟩
  · intro htop
    have := hH
    rw [htop, Subgroup.card_top, standardGroup_card] at this
    omega
  · intro K hHK
    by_contra hK
    obtain ⟨hk25, hr2⟩ := proper_overgroup_index standardGroup_card f.range K hH hHK hK
    have hn : K ≤ normalizer (f.range : Set StandardGroup) :=
      (normal_subgroupOf_iff_le_normalizer hHK.le).mp
        (normal_of_index_eq_two (show (f.range.subgroupOf K).index = 2 from hr2))
    obtain ⟨x, hx⟩ := standardGroup_exists_order_eight
    obtain ⟨y, hy, hy8⟩ := eight_in_odd_index K (by rw [hk25]; decide) x hx
    exact no_eight_normalizer f hf ⟨y, hn hy⟩ hy8

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five
