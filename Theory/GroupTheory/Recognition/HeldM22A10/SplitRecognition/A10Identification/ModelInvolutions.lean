module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# The two involution classes of A10

The cycle type of an involution in A10 is either (2,2) or (2,2,2,2).
Conjugators in the symmetric group can be made even by multiplying by
(89), which centralizes both chosen representatives. Thus these are the
two actual conjugacy classes in A10, not just cycle-type labels.

The centralizers have orders 2880 and 384 respectively. We restrict the
sign homomorphism to each symmetric-group centralizer; (89) makes this map
surjective, and its kernel is the alternating-group centralizer. Mathlib's
cycle-type centralizer formula then gives the two orders without enumerating
A10. These are exactly the model facts used in the final exhaustion step.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), DOI 10.1215/ijm/1256053756,
Theorem B, Section 1 and Lemma 5.12, pp.224--225 and 239.
-/

open Subgroup Equiv.Perm
namespace Theory.GroupTheory.HeldM22A10.A10Identification

public theorem central_cycleType :
    (CentralizerModels.a10Involution : Equiv.Perm (Fin 10)).cycleType = {2, 2, 2, 2} := by
  decide +kernel

public theorem noncentral_cycleType :
    (doubleTransposition : Equiv.Perm (Fin 10)).cycleType = {2, 2} := by
  decide +kernel

public theorem involution_cycleType (x : alternatingGroup (Fin 10)) (hx : orderOf x = 2) :
    (x : Equiv.Perm (Fin 10)).cycleType = {2, 2} ∨
      (x : Equiv.Perm (Fin 10)).cycleType = {2, 2, 2, 2} := by
  have ho : orderOf (x : Equiv.Perm (Fin 10)) = 2 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := (x : Equiv.Perm (Fin 10)).sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hsign := mem_alternatingGroup.mp x.property
  rw [sign_of_cycleType', hk] at hsign
  have hkbound : k ≤ 4 := by omega
  interval_cases k <;> norm_num at hsign
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (by simpa using hk)

private theorem alternating_isConj_of_swap_centralizes
    {x y : alternatingGroup (Fin 10)}
    (hxs : Equiv.swap (8 : Fin 10) 9 * (x : Equiv.Perm (Fin 10)) * (Equiv.swap (8 : Fin 10) 9)⁻¹ = (x : Equiv.Perm (Fin 10)))
    (hxy : IsConj (x : Equiv.Perm (Fin 10)) (y : Equiv.Perm (Fin 10))) : IsConj x y := by
  obtain ⟨p, hp⟩ := isConj_iff.mp hxy
  by_cases hpe : p ∈ alternatingGroup (Fin 10)
  · exact isConj_iff.mpr ⟨⟨p, hpe⟩, Subtype.ext hp⟩
  · have hps : sign p = -1 := by
      rcases Int.units_eq_one_or (sign p) with h | h
      · exact (hpe (mem_alternatingGroup.mpr h)).elim
      · exact h
    have hqe : p * Equiv.swap (8 : Fin 10) 9 ∈ alternatingGroup (Fin 10) := by
      rw [mem_alternatingGroup, map_mul, hps]
      norm_num [sign_swap']
      decide
    apply isConj_iff.mpr
    refine ⟨⟨p * Equiv.swap (8 : Fin 10) 9, hqe⟩, Subtype.ext ?_⟩
    change (p * Equiv.swap (8 : Fin 10) 9) * (x : Equiv.Perm (Fin 10)) * (p * Equiv.swap (8 : Fin 10) 9)⁻¹ = (y : Equiv.Perm (Fin 10))
    calc
      _ = p * (Equiv.swap (8 : Fin 10) 9 * (x : Equiv.Perm (Fin 10)) * (Equiv.swap (8 : Fin 10) 9)⁻¹) * p⁻¹ := by group
      _ = (y : Equiv.Perm (Fin 10)) := by rw [hxs, hp]

public theorem involution_classes (x : alternatingGroup (Fin 10)) (hx : orderOf x = 2) :
    IsConj CentralizerModels.a10Involution x ∨ IsConj doubleTransposition x := by
  rcases involution_cycleType x hx with h | h
  · apply Or.inr
    apply alternating_isConj_of_swap_centralizes (by decide +kernel)
    exact isConj_of_cycleType_eq (noncentral_cycleType.trans h.symm)
  · apply Or.inl
    apply alternating_isConj_of_swap_centralizes (by decide +kernel)
    exact isConj_of_cycleType_eq (central_cycleType.trans h.symm)

public theorem model_involutions_not_isConj :
    ¬ IsConj CentralizerModels.a10Involution doubleTransposition := by
  intro h
  have hc : IsConj (CentralizerModels.a10Involution : Equiv.Perm (Fin 10))
      (doubleTransposition : Equiv.Perm (Fin 10)) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    exact isConj_iff.mpr ⟨g, congrArg Subtype.val hg⟩
  have ht := isConj_iff_cycleType_eq.mp hc
  rw [central_cycleType, noncentral_cycleType] at ht
  have hc := congrArg Multiset.card ht
  norm_num at hc

private def centralizerEquivSignKer (x : alternatingGroup (Fin 10)) :
    centralizer ({x} : Set (alternatingGroup (Fin 10))) ≃*
      (sign.comp (centralizer ({(x : Equiv.Perm (Fin 10))} : Set (Equiv.Perm (Fin 10)))).subtype).ker where
  toFun y := ⟨⟨y.1.1, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp y.2))⟩,
    mem_alternatingGroup.mp y.1.2⟩
  invFun y := ⟨⟨y.1.1, mem_alternatingGroup.mpr y.2⟩,
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp y.1.2))⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl

private theorem twice_card_centralizer (x : alternatingGroup (Fin 10))
    (hxs : Commute (Equiv.swap (8 : Fin 10) 9) (x : Equiv.Perm (Fin 10))) :
    2 * Nat.card (centralizer ({x} : Set (alternatingGroup (Fin 10)))) =
      Nat.card (centralizer ({(x : Equiv.Perm (Fin 10))} : Set (Equiv.Perm (Fin 10)))) := by
  let C := centralizer ({(x : Equiv.Perm (Fin 10))} : Set (Equiv.Perm (Fin 10)))
  let f : C →* ℤˣ := sign.comp C.subtype
  let t : C := ⟨Equiv.swap (8 : Fin 10) 9, mem_centralizer_singleton_iff.mpr hxs.eq⟩
  have hft : f t = -1 := sign_swap (show (8 : Fin 10) ≠ 9 by decide)
  have hrange : f.range = ⊤ := by
    ext z
    simp only [Subgroup.mem_top, iff_true]
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨t, hft⟩
  have hc := f.ker.card_mul_index
  have hint : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  rw [Subgroup.index_ker, hrange, Subgroup.card_top, hint] at hc
  have he := Nat.card_congr (centralizerEquivSignKer x).toEquiv
  rw [he, Nat.mul_comm]
  exact hc

public theorem centralizer_central_card : Nat.card CentralizerModels.a10Centralizer = 384 := by
  have h := twice_card_centralizer CentralizerModels.a10Involution (by change _ * _ = _ * _; decide +kernel)
  rw [nat_card_centralizer, central_cycleType] at h
  norm_num [Nat.factorial] at h
  change 2 * Nat.card CentralizerModels.a10Centralizer = 768 at h
  omega

public theorem centralizer_noncentral_card :
    Nat.card (centralizer ({doubleTransposition} : Set (alternatingGroup (Fin 10)))) = 2880 := by
  have h := twice_card_centralizer doubleTransposition (by change _ * _ = _ * _; decide +kernel)
  rw [nat_card_centralizer, noncentral_cycleType] at h
  norm_num [Nat.factorial] at h
  omega

end Theory.GroupTheory.HeldM22A10.A10Identification
