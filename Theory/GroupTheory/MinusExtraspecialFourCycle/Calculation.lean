module
public import Theory.GroupTheory.MinusExtraspecialOddCentralizer.Relations

/-!
# A central fourth power in a four-cycle coset

The intrinsic singular-point action has five points. For the fixed four-cycle
(0 1 2 3), the four generator images range over the previously checked
quaternion–dihedral automorphism table. Given a fixed d with fourth power
acting as conjugation by d, a core correction makes the fourth norm central.
Every finite case is checked by kernel reduction, once, in this module.
The cases are checked sequentially to bound memory use; a representative
case took 32 seconds and 2.4 GB including imports, and the full Scratch
check took 466 seconds and 2.5 GB. The group transport is in `Model`.
Source application: Aschbacher–Smith 14.2.17(1), printed p.987.
-/

set_option Elab.async false
@[expose] public section
namespace MinusExtraspecial.FixedFourCalculation.FourCycle
open Outside OddCentralizer

def cyclic (u v r s : B) : Bool :=
  word u v r s 8 &&& 29 == 16 && word u v r s 16 &&& 29 == 25 &&
  word u v r s 25 &&& 29 == 28 && word u v r s 28 &&& 29 == 8 &&
  word u v r s 29 &&& 29 == 29

def fourthInner (u v r s d : B) : Bool :=
  gens.all fun x => word u v r s (word u v r s (word u v r s (word u v r s x))) == conj d x

def norm (u v r s q d : B) : B :=
  mul (mul (mul (mul q (word u v r s q)) (word u v r s (word u v r s q)))
    (word u v r s (word u v r s (word u v r s q)))) d

private def certificate (u : B) : Bool :=
  (row u).all fun (v,r,s) => !cyclic u v r s ||
    all.all fun d => word u v r s d != d || !fourthInner u v r s d ||
      all.any fun q => norm u v r s q d &&& 29 == 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_0 : certificate 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_1 : certificate 1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_2 : certificate 2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_3 : certificate 3 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_4 : certificate 4 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_5 : certificate 5 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_6 : certificate 6 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_7 : certificate 7 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_8 : certificate 8 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_9 : certificate 9 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_10 : certificate 10 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_11 : certificate 11 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_12 : certificate 12 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_13 : certificate 13 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_14 : certificate 14 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_15 : certificate 15 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_16 : certificate 16 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_17 : certificate 17 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_18 : certificate 18 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_19 : certificate 19 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_20 : certificate 20 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_21 : certificate 21 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_22 : certificate 22 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_23 : certificate 23 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_24 : certificate 24 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_25 : certificate 25 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_26 : certificate 26 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_27 : certificate 27 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_28 : certificate 28 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_29 : certificate 29 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_30 : certificate 30 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked_31 : certificate 31 := by decide +kernel
private theorem checked (u : B) : certificate u := by
  have hu : u.toNat < 32 := u.isLt
  interval_cases h : u.toNat
  · have he : u = 0 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_0
  · have he : u = 1 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_1
  · have he : u = 2 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_2
  · have he : u = 3 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_3
  · have he : u = 4 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_4
  · have he : u = 5 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_5
  · have he : u = 6 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_6
  · have he : u = 7 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_7
  · have he : u = 8 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_8
  · have he : u = 9 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_9
  · have he : u = 10 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_10
  · have he : u = 11 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_11
  · have he : u = 12 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_12
  · have he : u = 13 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_13
  · have he : u = 14 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_14
  · have he : u = 15 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_15
  · have he : u = 16 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_16
  · have he : u = 17 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_17
  · have he : u = 18 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_18
  · have he : u = 19 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_19
  · have he : u = 20 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_20
  · have he : u = 21 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_21
  · have he : u = 22 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_22
  · have he : u = 23 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_23
  · have he : u = 24 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_24
  · have he : u = 25 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_25
  · have he : u = 26 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_26
  · have he : u = 27 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_27
  · have he : u = 28 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_28
  · have he : u = 29 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_29
  · have he : u = 30 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_30
  · have he : u = 31 := BitVec.eq_of_toNat_eq h
    exact he ▸ checked_31

theorem calculation (u v r s d : B) (hr : relations u v r s)
    (hc : cyclic u v r s) (hd : word u v r s d = d)
    (hi : fourthInner u v r s d) :
    ∃ q : B, norm u v r s q d = 0 ∨ norm u v r s q d = 2 := by
  have hh := List.all_eq_true.mp (checked u) (v,r,s) (mem_row u v r s hr)
  simp only [hc,Bool.not_true,Bool.false_or] at hh
  have hh := List.all_eq_true.mp hh d ((by decide +kernel : ∀ x : B, x ∈ all) d)
  simp only [hd,bne_self_eq_false,hi,Bool.not_true,Bool.false_or] at hh
  obtain ⟨q,_,hq⟩ := List.any_eq_true.mp hh
  exact ⟨q,(by decide +kernel : ∀ x : B, x &&& 29 = 0 → x=0 ∨ x=2) _ (beq_iff_eq.mp hq)⟩
end MinusExtraspecial.FixedFourCalculation.FourCycle
