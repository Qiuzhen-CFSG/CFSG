module

public import Theory.GroupTheory.PGroup.RankTwoNormalFour

/-!
# Fusion inside a noncentral normal four-group

If a normal four-group contains a central involution but is not central,
its other two involutions are conjugate. A nontrivial conjugation action
fixes the central involution and interchanges the other two.

This is the elementary part of the two fusion cases in Janko–Thompson,
Math. Z. 113 (1970), §6, p.395.
-/

namespace Subgroup

/-- The two involutions other than a central involution of a noncentral
normal four-group are conjugate. -/
public theorem isConj_of_mem_normal_four_of_ne_central_involution
    {P : Type*} [Group P] [Finite P]
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (hnc : ¬ E ≤ center P)
    (z u v : P) (hzE : z ∈ E) (hzC : z ∈ center P) (hz1 : z ≠ 1)
    (huE : u ∈ E) (hvE : v ∈ E)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huz : u ≠ z) (hvz : v ≠ z) :
    IsConj u v := by
  classical
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour E := ⟨hE, IsElementaryAbelian.exponent_eq_prime⟩
  let : Fintype E := Fintype.ofFinite E
  let a : E := ⟨z, hzE⟩
  let b : E := ⟨u, huE⟩
  let c : E := ⟨v, hvE⟩
  have ha : a ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hb : b ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hab : a ≠ b := fun h => huz (congrArg Subtype.val h).symm
  have huC : u ∉ center P := by
    intro huC
    apply hnc
    intro x hx
    have hm : (⟨x, hx⟩ : E) ∈ ({a * b, a, b, 1} : Finset E) := by
      rw [IsKleinFour.eq_finset_univ ha hb hab]
      exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h
    · simpa only [show x = z * u from congrArg Subtype.val h] using
        (center P).mul_mem hzC huC
    · simpa only [show x = z from congrArg Subtype.val h] using hzC
    · simpa only [show x = u from congrArg Subtype.val h] using huC
    · simpa only [show x = 1 from congrArg Subtype.val h] using (center P).one_mem
  rw [mem_center_iff] at huC
  push Not at huC
  obtain ⟨g, hg⟩ := huC
  by_cases huv : u = v
  · exact huv ▸ IsConj.refl u
  let f : MulAut E := MulAut.conjNormal g
  have hfa : f a = a := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp hzC g)
  have hfb : f b ≠ b := by
    intro h
    exact hg (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h))
  have hf1 : f b ≠ 1 := fun h => hb (f.injective (h.trans f.map_one.symm))
  have hfb_a : f b ≠ a := fun h => hab (f.injective (h.trans hfa.symm)).symm
  have hfc : f b = c := by
    have hc1 : c ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
    have hca : c ≠ a := fun h => hvz (congrArg Subtype.val h)
    have hcb : c ≠ b := fun h => huv (congrArg Subtype.val h).symm
    exact (IsKleinFour.eq_mul_of_ne_all ha hb hab hf1 hfb_a hfb).trans
      (IsKleinFour.eq_mul_of_ne_all ha hb hab hc1 hca hcb).symm
  exact isConj_iff.mpr ⟨g, congrArg Subtype.val hfc⟩

end Subgroup
