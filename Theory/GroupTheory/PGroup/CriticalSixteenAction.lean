module

public import Theory.GroupTheory.PGroup.CriticalSubgroup
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.GroupTheory.Index

/-!
# Conjugation on a critical subgroup of order sixteen

Let C be a critical subgroup of a finite two-group, with order sixteen and
an elementary abelian center of order four. The image of conjugation on C
has order at most thirty-two.

The critical commutator condition makes the action trivial on C/Z(C), which
is a Klein four group. Restrict the action to Z(C). Its image is a two-subgroup
of the Klein-four automorphism group of order six, so has order at most two.
An element of the restriction kernel fixes the center pointwise. Its central
displacements on lifts of two generators of C/Z(C) determine it, embedding
the kernel in Z(C) × Z(C) and bounding its order by sixteen. The kernel-image
formula gives the result. No assumption on involutions outside the center
and no classification of groups of order sixteen is needed.

Sources: Gorenstein, *Finite Groups*, Theorem 5.3.11, for the critical-subgroup
conditions; Janko–Thompson (1970), Theorem 1.3, printed p.386, for the local
order bound in the three-involution setting.
-/

open Subgroup

private theorem exists_pair_cover {Q : Type*} [Group Q] [Finite Q] [IsKleinFour Q] :
    ∃ a b : Q, ∀ q : Q, q = 1 ∨ q = a ∨ q = b ∨ q = a * b := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  let : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [IsKleinFour.card_four]; decide)
  obtain ⟨a, ha⟩ := exists_ne (1 : Q)
  have hcard : ({1, a} : Finset Q).card < (Finset.univ : Finset Q).card := by
    rw [Finset.card_univ, IsKleinFour.card_four']
    have hle := Finset.card_insert_le (1 : Q) {a}
    simp only [Finset.card_singleton] at hle
    omega
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hb' : b ≠ 1 ∧ b ≠ a := by simpa using hb
  refine ⟨a, b, fun q => ?_⟩
  by_cases hq1 : q = 1
  · exact Or.inl hq1
  by_cases hqa : q = a
  · exact Or.inr (Or.inl hqa)
  by_cases hqb : q = b
  · exact Or.inr (Or.inr (Or.inl hqb))
  exact Or.inr (Or.inr (Or.inr
    (IsKleinFour.eq_mul_of_ne_all ha hb'.1 hb'.2.symm hq1 hqa hqb)))

private theorem restriction_kernel_bound
    {G : Type*} [Group G] [Finite G] [IsKleinFour (G ⧸ center G)]
    (H : Subgroup (MulAut G))
    (hmod : ∀ f ∈ H, ∀ x : G,
      QuotientGroup.mk' (center G) (f x) = QuotientGroup.mk' (center G) x) :
    Nat.card ((MulAut.characteristic (center G)).comp H.subtype).ker ≤
      Nat.card (center G) ^ 2 := by
  classical
  let q := QuotientGroup.mk' (center G)
  obtain ⟨a, b, hab⟩ := exists_pair_cover (Q := G ⧸ center G)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center G) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center G) b
  let r := (MulAut.characteristic (center G)).comp H.subtype
  have hfix (f : r.ker) (z : center G) : (f.val.val : MulAut G) z = z := by
    have h := DFunLike.congr_fun f.property z
    exact congrArg Subtype.val h
  let d : r.ker → G → center G := fun f t =>
    ⟨t⁻¹ * (f.val.val : MulAut G) t, QuotientGroup.eq.mp (hmod _ f.val.property t).symm⟩
  let encode : r.ker → center G × center G := fun f => (d f x, d f y)
  have hinj : Function.Injective encode := by
    intro f g hfg
    have hx : (f.val.val : MulAut G) x = (g.val.val : MulAut G) x :=
      mul_left_cancel (congrArg (fun p : center G × center G => (p.1 : G)) hfg)
    have hy : (f.val.val : MulAut G) y = (g.val.val : MulAut G) y :=
      mul_left_cancel (congrArg (fun p : center G × center G => (p.2 : G)) hfg)
    have hcoset (t v : G) (ht : (f.val.val : MulAut G) t = (g.val.val : MulAut G) t)
        (hv : q v = q t) : (f.val.val : MulAut G) v = (g.val.val : MulAut G) v := by
      have hz : t⁻¹ * v ∈ center G := QuotientGroup.eq.mp hv.symm
      have hf := hfix f ⟨t⁻¹ * v, hz⟩
      have hg := hfix g ⟨t⁻¹ * v, hz⟩
      change (f.val.val : MulAut G) (t⁻¹ * v) = t⁻¹ * v at hf
      change (g.val.val : MulAut G) (t⁻¹ * v) = t⁻¹ * v at hg
      rw [map_mul, map_inv] at hf hg
      rw [ht] at hf
      exact mul_left_cancel (hf.trans hg.symm)
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    rcases hab (q v) with hv | hv | hv | hv
    · exact hcoset 1 v (by simp) (by simpa only [map_one] using hv)
    · exact hcoset x v hx hv
    · exact hcoset y v hy hv
    · exact hcoset (x * y) v (by simp only [map_mul, hx, hy])
        (by simpa only [map_mul] using hv)
  have hc := Nat.card_le_card_of_injective encode hinj
  simpa only [Nat.card_prod, pow_two] using hc

private theorem two_subgroup_kleinFour_aut_bound
    {Z : Type*} [Group Z] [Finite Z] [IsKleinFour Z]
    (A : Subgroup (MulAut Z)) (hA : IsPGroup 2 A) : Nat.card A ≤ 2 := by
  have hd : Nat.card A ∣ 6 := IsKleinFour.card_mulAut Z ▸ A.card_subgroup_dvd_card
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
  have hthree : ¬ 3 ∣ Nat.card A := by
    obtain ⟨n, hn⟩ := hA.exists_card_eq
    rw [hn]
    intro h
    have hh := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at hh
  interval_cases Nat.card A <;> norm_num at *

private theorem action_bound
    {G : Type*} [Group G] [Finite G]
    [IsKleinFour (center G)] [IsKleinFour (G ⧸ center G)]
    (H : Subgroup (MulAut G)) (hH : IsPGroup 2 H)
    (hmod : ∀ f ∈ H, ∀ x : G,
      QuotientGroup.mk' (center G) (f x) = QuotientGroup.mk' (center G) x) :
    Nat.card H ≤ 32 := by
  let r := (MulAut.characteristic (center G)).comp H.subtype
  have hk : Nat.card r.ker ≤ 16 := by
    simpa only [IsKleinFour.card_four, Nat.reducePow] using restriction_kernel_bound H hmod
  have hi : Nat.card r.range ≤ 2 := two_subgroup_kleinFour_aut_bound r.range
    (hH.of_surjective r.rangeRestrict r.rangeRestrict_surjective)
  have hc := r.ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  calc
    Nat.card H = Nat.card r.ker * Nat.card r.range := hc.symm
    _ ≤ 16 * 2 := Nat.mul_le_mul hk hi
    _ = 32 := rfl

open scoped commutatorElement

namespace IsCriticalPSubgroup

/-- Conjugation on a critical subgroup of order sixteen with elementary center
of order four has image of order at most thirty-two. -/
public theorem card_conjNormal_range_le_thirtytwo
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {C : Subgroup P} (hcrit : IsCriticalPSubgroup 2 C)
    (hC : Nat.card C = 16) (hCZ : Nat.card (center C) = 4)
    [IsElementaryAbelian 2 (center C)] :
    letI : C.Characteristic := hcrit.characteristic
    Nat.card (MulAut.conjNormal : P →* MulAut C).range ≤ 32 := by
  let : C.Characteristic := hcrit.characteristic
  let : IsElementaryAbelian 2 (C ⧸ center C) := hcrit.quotient_elementary
  have hquot : Nat.card (C ⧸ center C) = 4 := by
    have hh := (center C).card_eq_card_quotient_mul_card_subgroup
    rw [hC, hCZ] at hh
    omega
  let : Nontrivial (center C) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial (C ⧸ center C) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour (center C) := ⟨hCZ, IsElementaryAbelian.exponent_eq_prime⟩
  let : IsKleinFour (C ⧸ center C) := ⟨hquot, IsElementaryAbelian.exponent_eq_prime⟩
  let f : P →* MulAut C := MulAut.conjNormal
  apply action_bound f.range (hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  rintro a ⟨g, rfl⟩ x
  let q := QuotientGroup.mk' (center C)
  have hmem : f g x * x⁻¹ ∈ center C := by
    have hh := hcrit.commutator_le
      (commutator_mem_commutator (mem_top g) x.property)
    obtain ⟨z, hz, he⟩ := hh
    have he' : z = f g x * x⁻¹ := by
      apply Subtype.ext
      simpa only [f, MulAut.conjNormal_apply, coe_mul, coe_inv,
        commutatorElement_def, Subgroup.subtype_apply] using he
    exact he' ▸ hz
  have hh : q (f g x * x⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff (N := center C) _).mpr hmem
  rw [map_mul, map_inv] at hh
  exact eq_of_mul_inv_eq_one hh

end IsCriticalPSubgroup
