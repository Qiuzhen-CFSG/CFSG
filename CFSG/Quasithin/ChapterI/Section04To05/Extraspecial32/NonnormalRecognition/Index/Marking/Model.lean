module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Reduction
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# The two involution classes of the marked eight-point model

The only nontrivial even involution cycle types in degree eight are 2² and
2⁴. An odd transposition centralizes each chosen representative, so symmetric
conjugacy lifts to alternating conjugacy. Restricting the sign homomorphism
to the double-transposition centralizer gives its alternating order 96.
These calculations justify the model marking in Aschbacher, “A 2-local
characterization of M12”, Proposition 3.3, printed p.38.
-/

open Subgroup Equiv Equiv.Perm
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.Marking

private theorem involution_cycleType (x : Eight) (hx : orderOf x = 2) :
    (x : Perm (Fin 8)).cycleType = {2, 2} ∨
      (x : Perm (Fin 8)).cycleType = {2, 2, 2, 2} := by
  have ho : orderOf (x : Perm (Fin 8)) = 2 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := (x : Perm (Fin 8)).sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  have hsign := mem_alternatingGroup.mp x.property
  rw [sign_of_cycleType', hk] at hsign
  have hkbound : k ≤ 3 := by omega
  interval_cases k <;> norm_num at hsign
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (by simpa using hk)

private theorem alternating_isConj_of_swap_centralizes {x y : Eight}
    (hxs : swap (0 : Fin 8) 1 * (x : Perm (Fin 8)) * (swap (0 : Fin 8) 1)⁻¹ = x)
    (hxy : IsConj (x : Perm (Fin 8)) (y : Perm (Fin 8))) : IsConj x y := by
  obtain ⟨p, hp⟩ := isConj_iff.mp hxy
  by_cases hpe : p ∈ alternatingGroup (Fin 8)
  · exact isConj_iff.mpr ⟨⟨p, hpe⟩, Subtype.ext hp⟩
  · have hps : sign p = -1 := (Int.units_eq_one_or _).resolve_left
      (fun h => hpe (mem_alternatingGroup.mpr h))
    have hqe : p * swap (0 : Fin 8) 1 ∈ alternatingGroup (Fin 8) := by
      simp [mem_alternatingGroup, map_mul, hps]
    apply isConj_iff.mpr
    refine ⟨⟨p * swap (0 : Fin 8) 1, hqe⟩, Subtype.ext ?_⟩
    change (p * swap (0 : Fin 8) 1) * (x : Perm (Fin 8)) *
      (p * swap (0 : Fin 8) 1)⁻¹ = y
    calc
      _ = p * (swap (0 : Fin 8) 1 * (x : Perm (Fin 8)) *
        (swap (0 : Fin 8) 1)⁻¹) * p⁻¹ := by group
      _ = (y : Perm (Fin 8)) := by rw [hxs, hp]

/-- The two specified elements represent every involution class in A₈. -/
public theorem involution_classes (x : Eight) (hx : orderOf x = 2) :
    IsConj z8 x ∨ IsConj t8 x := by
  rcases involution_cycleType x hx with h | h
  · apply Or.inr
    apply alternating_isConj_of_swap_centralizes (by decide +kernel)
    exact isConj_of_cycleType_eq ((by decide :
      (t8 : Perm (Fin 8)).cycleType = {2, 2}).trans h.symm)
  · apply Or.inl
    apply alternating_isConj_of_swap_centralizes (by decide +kernel)
    exact isConj_of_cycleType_eq ((by decide :
      (z8 : Perm (Fin 8)).cycleType = {2, 2, 2, 2}).trans h.symm)

private def centralizerEquivSignKer (x : Eight) :
    Centralizer x ≃*
      (sign.comp (centralizer ({(x : Perm (Fin 8))} : Set (Perm (Fin 8)))).subtype).ker where
  toFun y := ⟨⟨y.1.1, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp y.2))⟩,
    mem_alternatingGroup.mp y.1.2⟩
  invFun y := ⟨⟨y.1.1, mem_alternatingGroup.mpr y.2⟩,
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp y.1.2))⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl

private theorem twice_card_centralizer (x : Eight)
    (hxs : Commute (swap (0 : Fin 8) 1) (x : Perm (Fin 8))) :
    2 * Nat.card (Centralizer x) =
      Nat.card (centralizer ({(x : Perm (Fin 8))} : Set (Perm (Fin 8)))) := by
  let C := centralizer ({(x : Perm (Fin 8))} : Set (Perm (Fin 8)))
  let f : C →* ℤˣ := sign.comp C.subtype
  let t : C := ⟨swap (0 : Fin 8) 1, mem_centralizer_singleton_iff.mpr hxs.eq⟩
  have hft : f t = -1 := sign_swap (show (0 : Fin 8) ≠ 1 by decide)
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

/-- The double-transposition centralizer in A₈ has order 96. -/
public theorem t8_centralizer_card : Nat.card (Centralizer t8) = 96 := by
  have h := twice_card_centralizer t8 (by change _ * _ = _ * _; decide +kernel)
  rw [nat_card_centralizer, show (t8 : Perm (Fin 8)).cycleType = {2, 2} by decide] at h
  norm_num [Nat.factorial] at h
  omega

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index.Marking
