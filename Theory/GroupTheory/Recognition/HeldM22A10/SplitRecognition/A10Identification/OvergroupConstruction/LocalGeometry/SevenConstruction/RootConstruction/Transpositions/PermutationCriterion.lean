module

public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# The finite permutation step in Held's transposition argument

An odd involution in S7 is a transposition or a product of three transpositions.
For three distinct commuting involutions in the latter conjugacy class, their
product is a transposition, whose centralizer has order 240. Thus the absence
of a factor five in that product's centralizer forces the first alternative.

To check the small commuting-triple calculation, a permutation centralizing
(01)(23)(45) is encoded by its values at 0, 2 and 4. The fixed point and the
other three values are forced. Kernel reduction checks these 343 possibilities
and the six remaining partners; S7 itself is not enumerated in the proof.

Source application: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, final paragraph of Lemma 5.10, printed p.238.
-/

open Equiv Equiv.Perm Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.PermutationCriterion
private def triple : Perm (Fin 7) := swap 0 1 * swap 2 3 * swap 4 5
private def partners : Fin 6 → Perm (Fin 7) := ![
  swap 0 1 * swap 2 4 * swap 3 5,
  swap 0 1 * swap 2 5 * swap 3 4,
  swap 0 2 * swap 1 3 * swap 4 5,
  swap 0 3 * swap 1 2 * swap 4 5,
  swap 0 4 * swap 1 5 * swap 2 3,
  swap 0 5 * swap 1 4 * swap 2 3]
private theorem triple_type : triple.cycleType = {2,2,2} := by decide +kernel
private theorem odd_square_types (a : Perm (Fin 7)) (ha : a ^ 2 = 1) (hs : sign a ≠ 1) :
    a.IsSwap ∨ IsConj a triple := by
  have hn : a ≠ 1 := by intro h; apply hs; simp [h]
  have ho : orderOf a = 2 := orderOf_eq_prime ha hn
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hb := a.sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hb
  have hb' : k ≤ 2 := by omega
  rw [sign_of_cycleType', hk] at hs
  interval_cases k <;> norm_num at hs
  · exact Or.inl (isSwap_iff_cycleType.mpr (by simpa using hk))
  · exact Or.inr (isConj_iff_cycleType_eq.mpr (by simpa [triple_type] using hk))

private def coded (x y z : Fin 7) : Fin 7 → Fin 7 :=
  ![x, triple x, y, triple y, z, triple z, 6]

private theorem coded_complete : ∀ x y z : Fin 7,
    (∀ j, coded x y z (coded x y z j) = j) →
    (Finset.univ.filter (fun j => coded x y z j ≠ j)).card = 6 →
    coded x y z ≠ (fun j => triple j) →
    ∃ i, coded x y z = (fun j => partners i j) := by decide +kernel

private theorem partners_complete (b : Perm (Fin 7))
    (hb : b ^ 2 = 1) (hcard : b.support.card = 6)
    (hcomm : triple * b = b * triple) (hne : b ≠ triple) :
    ∃ i, b = partners i := by
  have hact (i : Fin 7) : triple (b i) = b (triple i) :=
    congrArg (fun p : Perm (Fin 7) => p i) hcomm
  have h1 : b 1 = triple (b 0) := (hact 0).symm
  have h3 : b 3 = triple (b 2) := (hact 2).symm
  have h5 : b 5 = triple (b 4) := (hact 4).symm
  have h6 : b 6 = 6 := by
    have hfix : ∀ j : Fin 7, triple j = j → j = 6 := by decide +kernel
    exact hfix (b 6) (hact 6)
  have he : (fun j => b j) = coded (b 0) (b 2) (b 4) := by
    funext j
    fin_cases j <;> simp [coded, h1, h3, h5, h6]
  obtain ⟨i, hi⟩ := coded_complete (b 0) (b 2) (b 4)
    (by rw [← he]; intro j; exact congrArg (fun p : Perm (Fin 7) => p j) hb)
    (by simpa only [← he, support] using hcard)
    (by intro h; apply hne; exact Equiv.ext (congrFun (he.trans h)))
  exact ⟨i, Equiv.ext (congrFun (he.trans hi))⟩

private theorem partners_product : ∀ i j : Fin 6,
    partners i ≠ partners j → partners i * partners j = partners j * partners i →
    (triple * partners i * partners j).support.card = 2 := by decide +kernel

private theorem triple_product (b c : Perm (Fin 7))
    (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hbtype : b.cycleType = {2,2,2}) (hctype : c.cycleType = {2,2,2})
    (hab : Commute triple b) (hac : Commute triple c) (hbc : Commute b c)
    (hneab : triple ≠ b) (hneac : triple ≠ c) (hnebc : b ≠ c) :
    (triple * b * c).IsSwap := by
  have hbcard : b.support.card = 6 := by rw [← sum_cycleType, hbtype]; decide
  have hccard : c.support.card = 6 := by rw [← sum_cycleType, hctype]; decide
  obtain ⟨i, rfl⟩ := partners_complete b hb hbcard hab.eq hneab.symm
  obtain ⟨j, rfl⟩ := partners_complete c hc hccard hac.eq hneac.symm
  exact card_support_eq_two.mp (partners_product i j hnebc hbc.eq)

/-- Three distinct commuting conjugate odd involutions in S7 are swaps if
the centralizer of their product has order prime to five. -/
public theorem isSwap_of_odd_commuting_triple (a b c : Perm (Fin 7))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hs : sign a ≠ 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (hneab : a ≠ b) (hneac : a ≠ c) (hnebc : b ≠ c)
    (hconjb : IsConj a b) (hconjc : IsConj a c)
    (hfive : ¬ 5 ∣ Nat.card (centralizer ({a*b*c} : Set (Perm (Fin 7))))) :
    a.IsSwap := by
  rcases odd_square_types a ha hs with h | h
  · exact h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  let f := MulAut.conj g
  have hfa : f a = triple := hg
  have hbt : (f b).cycleType = {2,2,2} := by
    rw [← triple_type, ← hfa]
    exact (isConj_iff_cycleType_eq.mp (f.toMonoidHom.map_isConj hconjb)).symm
  have hct : (f c).cycleType = {2,2,2} := by
    rw [← triple_type, ← hfa]
    exact (isConj_iff_cycleType_eq.mp (f.toMonoidHom.map_isConj hconjc)).symm
  have hswap : (triple * f b * f c).IsSwap := triple_product (f b) (f c)
    (by rw [← map_pow, hb, map_one]) (by rw [← map_pow, hc, map_one]) hbt hct
    (hfa ▸ hab.map f.toMonoidHom) (hfa ▸ hac.map f.toMonoidHom) (hbc.map f.toMonoidHom)
    (by rw [← hfa]; exact fun h => hneab (f.injective h))
    (by rw [← hfa]; exact fun h => hneac (f.injective h))
    (fun h => hnebc (f.injective h))
  have htype : (a*b*c).cycleType = {2} := by
    rw [isSwap_iff_cycleType] at hswap
    rw [← hfa, ← map_mul, ← map_mul] at hswap
    simpa only [f, MulAut.conj_apply, cycleType_conj] using hswap
  apply (hfive ?_).elim
  rw [nat_card_centralizer, htype]
  decide +kernel
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.PermutationCriterion
