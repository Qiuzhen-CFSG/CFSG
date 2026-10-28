module

public import Theory.Representation.BinaryPermutation.OrbitFixedSpace
public import Theory.Representation.BinaryPermutation.OddOffenderTransport
public import Mathlib.GroupTheory.PGroup

/-!
# A two-group fixes a plane in the deleted seven-letter binary module

Every two-group on seven letters has a fixed point and every orbit has
size at most four. Two orbits would therefore cover at most five letters.
There are at least three orbits, giving fixed dimension at least two after
removing the constant summand. In particular a one-dimensional fixed space
of the actual extraspecial-kernel image excludes this marked module.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped BigOperators
namespace BinaryPermutation

private theorem seven_orbits_ge_three (A : Subgroup (Equiv.Perm (Fin 7)))
    (hA : IsPGroup 2 A) : 3≤Nat.card (MulAction.orbitRel.Quotient A (Fin 7)) := by
  classical
  let Q := MulAction.orbitRel.Quotient A (Fin 7)
  let : Fintype Q := Fintype.ofFinite _
  have hsum : (∑ q : Q, Nat.card q.orbit)=7 := by
    simpa only [Nat.card_sigma,Nat.card_fin] using
      (Nat.card_congr (MulAction.selfEquivSigmaOrbits' A (Fin 7))).symm
  have hbound (q : Q) : Nat.card q.orbit≤4 := by
    have he : q.orbit=MulAction.orbit A q.out :=
      MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq'
    obtain ⟨n,hn⟩ := hA.card_orbit (q.out : Fin 7)
    have hb : Nat.card (MulAction.orbit A q.out)≤7 :=
      (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans_eq (Nat.card_fin 7)
    have hle : n≤2 := by
      by_contra! hh
      have hp := Nat.pow_le_pow_right (by decide : 0<2) hh
      rw [hn] at hb
      omega
    rw [he,hn]
    exact Nat.pow_le_pow_right (by decide) hle
  obtain ⟨x,hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Fin 7) (by simp)
  let q : Q := Quotient.mk'' x
  have hq : Nat.card q.orbit=1 := by
    rw [show q.orbit=MulAction.orbit A x from MulAction.orbitRel.Quotient.orbit_mk x]
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mp hx
  have he := Finset.sum_erase_add (Finset.univ : Finset Q) (fun q => Nat.card q.orbit)
    (Finset.mem_univ q)
  have hb : (∑ r∈(Finset.univ : Finset Q).erase q, Nat.card r.orbit)≤
      ((Finset.univ : Finset Q).erase q).card*4 := by
    calc
      _ ≤ ∑ _r∈(Finset.univ : Finset Q).erase q, 4 :=
        Finset.sum_le_sum (fun r _ => hbound r)
      _ = _ := by simp
  have hcard : ((Finset.univ : Finset Q).erase q).card=Nat.card Q-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ q),Finset.card_univ,Nat.card_eq_fintype_card]
  rw [hq,hsum] at he
  rw [hcard] at hb
  change 3≤Nat.card Q
  omega

/-- Every actual two-subgroup of S7 fixes at least a binary plane in its
augmentation six-space. -/
theorem seven_twoGroup_core_fixed_finrank (A : Subgroup (Equiv.Perm (Fin 7)))
    (hA : IsPGroup 2 A) :
    2≤Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 7)) A) := by
  have horb := seven_orbits_ge_three A hA
  have hfull := finrank_full_fixedSpace_eq_card_orbits A
  have hc := finrank_full_fixedSpace_odd (Fin 7) (by decide) A
  omega

/-- Every actual two-subgroup of S7 fixes at least a binary plane in its
natural deleted six-space. -/
theorem seven_twoGroup_fixed_finrank (A : Subgroup (Equiv.Perm (Fin 7)))
    (hA : IsPGroup 2 A) :
    2≤Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 7)) A) := by
  have horb := seven_orbits_ge_three A hA
  have hfull := finrank_full_fixedSpace_eq_card_orbits A
  have hc := fixedCodim_natural_eq_full_odd (Fin 7) (by decide) A
  have hn := fixedCodim_add_finrank (naturalRepresentation (Fin 7)) A
  have hf := fixedCodim_add_finrank (representation (Fin 7)) A
  rw [finrank_natural_odd (Fin 7) (by decide)] at hn
  rw [finrank_full] at hf
  norm_num at hn hf
  omega

end BinaryPermutation
