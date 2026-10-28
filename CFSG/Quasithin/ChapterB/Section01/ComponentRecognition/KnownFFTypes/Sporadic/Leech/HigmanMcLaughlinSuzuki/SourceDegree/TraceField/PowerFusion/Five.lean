module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Five.Certificates
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.PrimeCases
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Contracts

/-!
# Square fusion in the odd five-divisibility branch of HS

Every odd-order element whose order is divisible by five and prime to three
is conjugate to its square, in the literal degree-100 ATLAS carrier.

The order-125 subgroup is Sylow by the checked carrier cardinality. Its
certified normal forms therefore cover every element of five-power order
up to conjugacy, and their square conjugators transfer to those elements.
Their fixed-point counts are zero or five for every element of order five.
A commuting element of order seven or eleven would fix the five-element's
fixed points and conversely, contradicting the respective counts two and one.
Taking powers excludes all mixed orders involving these primes. Lagrange's
theorem then leaves order dividing 125, so the finite certificate applies.

The final export supplies precisely `OddFiveSquareFusion` to the existing
`powerFusion_of_odd_branches` assembly. It neither assumes an element-order
classification nor depends on the independent three-divisibility branch.
Source: ATLAS HSG1-p100B0,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/.
-/

public section
namespace Sporadic.LeechRelated.HS.FiveFusion
open scoped Pointwise

private theorem five_not_dvd_index : ¬ 5 ∣ FiveSubgroup.subgroup.index := by
  have h := FiveSubgroup.subgroup.card_mul_index
  rw [FiveSubgroup.card_subgroup, NormalizerIndex.card_carrier] at h
  have hi : FiveSubgroup.subgroup.index = 354816 := by omega
  rw [hi]
  decide

private def sylow : Sylow 5 Carrier := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact FiveSubgroup.subgroup_isPGroup.toSylow five_not_dvd_index

/-- Every element of five-power order is conjugate to a certified normal form. -/
theorem exists_normalForm_conjugate (g : Carrier) (hg : orderOf g ∣ 5 ^ 3) :
    ∃ (t : Fin 125) (c : Carrier), g = c * normalForm t * c⁻¹ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hP : IsPGroup 5 (Subgroup.zpowers g) :=
    IsPGroup.of_card_dvd_pow (by rwa [Nat.card_zpowers])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Carrier sylow Q
  have hmem : g ∈ Q := hQ (Subgroup.mem_zpowers g)
  rw [← hc] at hmem
  change g ∈ (↑(c • sylow) : Set Carrier) at hmem
  rw [Sylow.coe_smul] at hmem
  obtain ⟨y, hy, he⟩ := hmem
  obtain ⟨t, ht⟩ := normalForm_cover hy
  refine ⟨t, c, ?_⟩
  change c * y * c⁻¹ = g at he
  rw [ht]
  exact he.symm

/-- Square fusion holds for every element whose order divides 125. -/
theorem square_of_order_dvd (g : Carrier) (hg : orderOf g ∣ 5 ^ 3) :
    IsConj g (g ^ 2) := by
  obtain ⟨t, c, hc⟩ := exists_normalForm_conjugate g hg
  have h : IsConj (normalForm t) g := isConj_iff.mpr ⟨c, hc.symm⟩
  exact (h.symm.trans (normalForm_square t)).trans (h.pow 2)

/-- An element of order five fixes either zero or five letters. -/
theorem orderFive_fixed_card (g : Carrier) (hg : orderOf g = 5) :
    Fintype.card (Function.fixedPoints (inclusion g)) = 0 ∨
      Fintype.card (Function.fixedPoints (inclusion g)) = 5 := by
  obtain ⟨t, c, hc⟩ := exists_normalForm_conjugate g (by rw [hg]; decide)
  have ht : t ≠ 0 := by
    intro ht
    have hg1 : g = 1 := by simpa [ht, normalForm] using hc
    simp [hg1] at hg
  have hs : (inclusion g).support.card = (inclusion (normalForm t)).support.card := by
    rw [hc, map_mul, map_mul, map_inv, Equiv.Perm.card_support_conj]
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType, hs]
  rcases normalForm_support t ht with h | h
  · exact Or.inr (by rw [h]; rfl)
  · exact Or.inl (by rw [h]; rfl)

private theorem fixedPoints_subset_of_commute {x y : Equiv.Perm (Fin 100)}
    (hc : Commute x y) {n : ℕ} (hy : y ^ n = 1)
    (hcop : n.Coprime (Fintype.card (Function.fixedPoints x)).factorial) :
    Function.fixedPoints x ⊆ Function.fixedPoints y := by
  let z : Equiv.Perm (Function.fixedPoints x) := y.subtypePerm
    (fun _ => Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer
      (Subgroup.mem_centralizer_singleton_iff.mpr hc.symm.eq))
  have hzn : z ^ n = 1 := by
    dsimp only [z]
    rw [Equiv.Perm.subtypePerm_pow]
    apply Equiv.ext
    intro t
    apply Subtype.ext
    change (y ^ n) t.val = t.val
    rw [hy]
    rfl
  have hzc : orderOf z ∣ (Fintype.card (Function.fixedPoints x)).factorial := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using orderOf_dvd_natCard z
  have hz : z = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hzn) hzc)
  intro t ht
  exact congrArg Subtype.val (congrArg (fun f : Equiv.Perm (Function.fixedPoints x) =>
    f ⟨t, ht⟩) hz)

private theorem not_commute_of_fixed_card (x y : Carrier)
    (hx : orderOf x = 5) {p k : ℕ} (hy : orderOf y = p)
    (hfixed : Fintype.card (Function.fixedPoints (inclusion y)) = k)
    (hk : 0 < k) (hk5 : k < 5)
    (hsmall : Nat.Coprime 5 k.factorial) (hlarge : Nat.Coprime p 120) :
    ¬ Commute x y := by
  intro hc
  have hc' := hc.map inclusion
  have hxy := fixedPoints_subset_of_commute hc'.symm (n := 5)
    (by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one])
    (by rwa [hfixed])
  have hle := Fintype.card_le_of_injective (Set.inclusion hxy) (Set.inclusion_injective hxy)
  rw [hfixed] at hle
  have hx5 : Fintype.card (Function.fixedPoints (inclusion x)) = 5 := by
    rcases orderFive_fixed_card x hx with h | h
    · omega
    · exact h
  have hyx := fixedPoints_subset_of_commute hc' (n := p)
    (by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one])
    (by simpa only [hx5, show Nat.factorial 5 = 120 from by decide] using hlarge)
  have hle' := Fintype.card_le_of_injective (Set.inclusion hyx) (Set.inclusion_injective hyx)
  rw [hx5, hfixed] at hle'
  omega

/-- Divisibility by five excludes divisibility by seven and eleven, including
all larger mixed orders; no element-order classification is assumed. -/
theorem no_seven_eleven_of_five (g : Carrier) (h5 : 5 ∣ orderOf g) :
    ¬ 7 ∣ orderOf g ∧ ¬ 11 ∣ orderOf g := by
  have ho := (orderOf_pos g).ne'
  let x := g ^ (orderOf g / 5)
  have hx : orderOf x = 5 := orderOf_pow_orderOf_div ho h5
  constructor
  · intro h7
    let y := g ^ (orderOf g / 7)
    have hy : orderOf y = 7 := orderOf_pow_orderOf_div ho h7
    exact not_commute_of_fixed_card x y hx hy
      (TracePowerFusion.orderSeven_fixed_card y hy) (by decide) (by decide)
      (by decide) (by decide) ((Commute.refl g).pow_pow _ _)
  · intro h11
    let y := g ^ (orderOf g / 11)
    have hy : orderOf y = 11 := orderOf_pow_orderOf_div ho h11
    exact not_commute_of_fixed_card x y hx hy
      (TracePowerFusion.orderEleven_fixed_card y hy) (by decide) (by decide)
      (by decide) (by decide) ((Commute.refl g).pow_pow _ _)

/-- The complete odd five-divisibility branch has five-power order. -/
theorem order_dvd_of_odd_five (g : Carrier) (ho : Odd (orderOf g))
    (h3 : ¬ 3 ∣ orderOf g) (h5 : 5 ∣ orderOf g) : orderOf g ∣ 5 ^ 3 := by
  obtain ⟨h7, h11⟩ := no_seven_eleven_of_five g h5
  have c2 : (orderOf g).Coprime (2 ^ 9) :=
    (Nat.coprime_two_right.mpr ho).pow_right _
  have c3 : (orderOf g).Coprime (3 ^ 2) :=
    (((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3).symm).pow_right _
  have c7 : (orderOf g).Coprime 7 :=
    ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr h7).symm
  have c11 : (orderOf g).Coprime 11 :=
    ((by decide : Nat.Prime 11).coprime_iff_not_dvd.mpr h11).symm
  have hd : orderOf g ∣ 2 ^ 9 * (3 ^ 2 * (7 * (11 * 5 ^ 3))) := by
    change orderOf g ∣ 44352000
    rw [← NormalizerIndex.card_carrier]
    exact orderOf_dvd_natCard g
  exact c11.dvd_of_dvd_mul_left (c7.dvd_of_dvd_mul_left
    (c3.dvd_of_dvd_mul_left (c2.dvd_of_dvd_mul_left hd)))

end Sporadic.LeechRelated.HS.FiveFusion

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField
open Sporadic.LeechRelated.HS

/-- Square fusion for the entire odd-order branch divisible by five and prime
to three, on the literal HS carrier. -/
theorem oddFiveSquareFusion : OddFiveSquareFusion := by
  intro g ho h3 h5
  exact FiveFusion.square_of_order_dvd g (FiveFusion.order_dvd_of_odd_five g ho h3 h5)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField
