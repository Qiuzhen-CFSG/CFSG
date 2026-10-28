module
public import Theory.GroupTheory.MinusExtraspecialOddCentralizer.Table
/-!
# Characteristic roots in transposition fixed cores

For every involutory automorphism inducing a transposition, its fixed core
contains a square root of the central involution. If that core contains a
noncentral involution d, its two order-four elements form an inverse pair,
and d does not centralize either root. This finite check supplies the
structural square argument without enumerating pairs of automorphisms.
The actual extension consumer is in `MinusExtraspecialOddCentralizer`.
Source: Aschbacher–Smith 14.2.17(1), printed p.987.
-/
set_option Elab.async false
@[expose] public section
namespace MinusExtraspecial.FixedFourCalculation.OddCentralizer
open Outside OddInvolution

def rootPair (u v r s d x : B) : Bool :=
  word u v r s x == x && mul x x == 2 && conj d x != x &&
    (all.all fun y => word u v r s y != y || mul y y != 2 || y == x || y == inv x)

def fixedCertificate (u : B) : Bool :=
  (row u).all fun (v,r,s) =>
    !(Outside.invol u v r s && moved u v r s == 2) ||
    ((all.any fun x => word u v r s x == x && mul x x == 2) &&
    all.all fun d => d == 0 || d == 2 || mul d d != 0 || word u v r s d != d ||
      all.any (rootPair u v r s d))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_0 : fixedCertificate 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_1 : fixedCertificate 1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_2 : fixedCertificate 2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_3 : fixedCertificate 3 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_4 : fixedCertificate 4 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_5 : fixedCertificate 5 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_6 : fixedCertificate 6 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_7 : fixedCertificate 7 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_8 : fixedCertificate 8 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_9 : fixedCertificate 9 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_10 : fixedCertificate 10 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_11 : fixedCertificate 11 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_12 : fixedCertificate 12 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_13 : fixedCertificate 13 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_14 : fixedCertificate 14 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_15 : fixedCertificate 15 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_16 : fixedCertificate 16 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_17 : fixedCertificate 17 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_18 : fixedCertificate 18 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_19 : fixedCertificate 19 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_20 : fixedCertificate 20 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_21 : fixedCertificate 21 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_22 : fixedCertificate 22 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_23 : fixedCertificate 23 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_24 : fixedCertificate 24 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_25 : fixedCertificate 25 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_26 : fixedCertificate 26 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_27 : fixedCertificate 27 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_28 : fixedCertificate 28 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_29 : fixedCertificate 29 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_30 : fixedCertificate 30 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fixed_checked_31 : fixedCertificate 31 := by decide +kernel

theorem fixed_checked (u : B) : fixedCertificate u := by
  have hu : u.toNat < 32 := u.isLt
  interval_cases h : u.toNat
  · have he : u = 0 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_0
  · have he : u = 1 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_1
  · have he : u = 2 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_2
  · have he : u = 3 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_3
  · have he : u = 4 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_4
  · have he : u = 5 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_5
  · have he : u = 6 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_6
  · have he : u = 7 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_7
  · have he : u = 8 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_8
  · have he : u = 9 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_9
  · have he : u = 10 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_10
  · have he : u = 11 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_11
  · have he : u = 12 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_12
  · have he : u = 13 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_13
  · have he : u = 14 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_14
  · have he : u = 15 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_15
  · have he : u = 16 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_16
  · have he : u = 17 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_17
  · have he : u = 18 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_18
  · have he : u = 19 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_19
  · have he : u = 20 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_20
  · have he : u = 21 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_21
  · have he : u = 22 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_22
  · have he : u = 23 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_23
  · have he : u = 24 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_24
  · have he : u = 25 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_25
  · have he : u = 26 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_26
  · have he : u = 27 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_27
  · have he : u = 28 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_28
  · have he : u = 29 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_29
  · have he : u = 30 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_30
  · have he : u = 31 := BitVec.eq_of_toNat_eq h
    exact he ▸ fixed_checked_31
end MinusExtraspecial.FixedFourCalculation.OddCentralizer
