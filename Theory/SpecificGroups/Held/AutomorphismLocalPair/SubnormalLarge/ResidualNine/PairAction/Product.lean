module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.PairAction.CenterImage.SmallPerm
public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.Definitions

/-!
# Explicit product coordinates for the small Held center action

The two rotations are mapped to the separate S₃ factors. The first involution
reflects the second factor, and the second reflects both. With word coordinates
(a,b,c,d) of radices (3,3,2,2), the product has coordinates
(a+(-1)^d A, b+(-1)^(c+d) B, c+C, d+D), reduced in those radices.
The same multiplication formula is checked on the actual sixteen-point action
and the proposed S₃ × S₃ images. This is an explicit group comparison, not an
identification by order. The generator-action certificates in CenterImage.Action
connect these permutations to the original Held pair.

Sources: the extracted PureInnerCore center-action certificates, unchanged
ResidualRoots.Pair00 words, GLS3 Table 5.3p; source consumer Aschbacher--Smith
2.3.9(7), printed p.526. Each finite multiplication row is kernel-checked.
-/

set_option Elab.async false
@[expose] public section
namespace Held.AutomorphismLocalPair.ResidualNine.PairActionCertificate.CenterImageCertificate

def rotation : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
def reflection : Equiv.Perm (Fin 3) := Equiv.swap 0 1

def targetGenerator : Fin 4 → QuotientModel :=
  ![(rotation, 1), (1, rotation), (1, reflection), (reflection, reflection)]

def targetWord (v : Fin 36) : QuotientModel := word v targetGenerator

def mulIndex (v w : Fin 36) : Fin 36 :=
  ⟨(v.val % 3 + (if v.val / 18 = 0 then w.val % 3 else 3 - w.val % 3)) % 3 +
    3 * ((v.val / 3 % 3 +
      (if (v.val / 9 % 2 + v.val / 18) % 2 = 0 then w.val / 3 % 3
        else 3 - w.val / 3 % 3)) % 3) +
    9 * ((v.val / 9 % 2 + w.val / 9 % 2) % 2) +
    18 * ((v.val / 18 + w.val / 18) % 2), by omega⟩

theorem targetWord_injective : Function.Injective targetWord := by
  decide +kernel

theorem target_card : Nat.card QuotientModel = 36 := by
  rw [Nat.card_eq_fintype_card]
  simp [QuotientModel, Fintype.card_prod, Fintype.card_perm, Nat.factorial]

theorem targetWord_surjective : Function.Surjective targetWord :=
  ((Nat.bijective_iff_injective_and_card targetWord).mpr
    ⟨targetWord_injective, by rw [Nat.card_fin, target_card]⟩).surjective

private theorem smallWord_mul_0 : ∀ w : Fin 36,
    smallWord 0 * smallWord w = smallWord (mulIndex 0 w) := by
  decide +kernel

private theorem smallWord_mul_1 : ∀ w : Fin 36,
    smallWord 1 * smallWord w = smallWord (mulIndex 1 w) := by
  decide +kernel

private theorem smallWord_mul_2 : ∀ w : Fin 36,
    smallWord 2 * smallWord w = smallWord (mulIndex 2 w) := by
  decide +kernel

private theorem smallWord_mul_3 : ∀ w : Fin 36,
    smallWord 3 * smallWord w = smallWord (mulIndex 3 w) := by
  decide +kernel

private theorem smallWord_mul_4 : ∀ w : Fin 36,
    smallWord 4 * smallWord w = smallWord (mulIndex 4 w) := by
  decide +kernel

private theorem smallWord_mul_5 : ∀ w : Fin 36,
    smallWord 5 * smallWord w = smallWord (mulIndex 5 w) := by
  decide +kernel

private theorem smallWord_mul_6 : ∀ w : Fin 36,
    smallWord 6 * smallWord w = smallWord (mulIndex 6 w) := by
  decide +kernel

private theorem smallWord_mul_7 : ∀ w : Fin 36,
    smallWord 7 * smallWord w = smallWord (mulIndex 7 w) := by
  decide +kernel

private theorem smallWord_mul_8 : ∀ w : Fin 36,
    smallWord 8 * smallWord w = smallWord (mulIndex 8 w) := by
  decide +kernel

private theorem smallWord_mul_9 : ∀ w : Fin 36,
    smallWord 9 * smallWord w = smallWord (mulIndex 9 w) := by
  decide +kernel

private theorem smallWord_mul_10 : ∀ w : Fin 36,
    smallWord 10 * smallWord w = smallWord (mulIndex 10 w) := by
  decide +kernel

private theorem smallWord_mul_11 : ∀ w : Fin 36,
    smallWord 11 * smallWord w = smallWord (mulIndex 11 w) := by
  decide +kernel

private theorem smallWord_mul_12 : ∀ w : Fin 36,
    smallWord 12 * smallWord w = smallWord (mulIndex 12 w) := by
  decide +kernel

private theorem smallWord_mul_13 : ∀ w : Fin 36,
    smallWord 13 * smallWord w = smallWord (mulIndex 13 w) := by
  decide +kernel

private theorem smallWord_mul_14 : ∀ w : Fin 36,
    smallWord 14 * smallWord w = smallWord (mulIndex 14 w) := by
  decide +kernel

private theorem smallWord_mul_15 : ∀ w : Fin 36,
    smallWord 15 * smallWord w = smallWord (mulIndex 15 w) := by
  decide +kernel

private theorem smallWord_mul_16 : ∀ w : Fin 36,
    smallWord 16 * smallWord w = smallWord (mulIndex 16 w) := by
  decide +kernel

private theorem smallWord_mul_17 : ∀ w : Fin 36,
    smallWord 17 * smallWord w = smallWord (mulIndex 17 w) := by
  decide +kernel

private theorem smallWord_mul_18 : ∀ w : Fin 36,
    smallWord 18 * smallWord w = smallWord (mulIndex 18 w) := by
  decide +kernel

private theorem smallWord_mul_19 : ∀ w : Fin 36,
    smallWord 19 * smallWord w = smallWord (mulIndex 19 w) := by
  decide +kernel

private theorem smallWord_mul_20 : ∀ w : Fin 36,
    smallWord 20 * smallWord w = smallWord (mulIndex 20 w) := by
  decide +kernel

private theorem smallWord_mul_21 : ∀ w : Fin 36,
    smallWord 21 * smallWord w = smallWord (mulIndex 21 w) := by
  decide +kernel

private theorem smallWord_mul_22 : ∀ w : Fin 36,
    smallWord 22 * smallWord w = smallWord (mulIndex 22 w) := by
  decide +kernel

private theorem smallWord_mul_23 : ∀ w : Fin 36,
    smallWord 23 * smallWord w = smallWord (mulIndex 23 w) := by
  decide +kernel

private theorem smallWord_mul_24 : ∀ w : Fin 36,
    smallWord 24 * smallWord w = smallWord (mulIndex 24 w) := by
  decide +kernel

private theorem smallWord_mul_25 : ∀ w : Fin 36,
    smallWord 25 * smallWord w = smallWord (mulIndex 25 w) := by
  decide +kernel

private theorem smallWord_mul_26 : ∀ w : Fin 36,
    smallWord 26 * smallWord w = smallWord (mulIndex 26 w) := by
  decide +kernel

private theorem smallWord_mul_27 : ∀ w : Fin 36,
    smallWord 27 * smallWord w = smallWord (mulIndex 27 w) := by
  decide +kernel

private theorem smallWord_mul_28 : ∀ w : Fin 36,
    smallWord 28 * smallWord w = smallWord (mulIndex 28 w) := by
  decide +kernel

private theorem smallWord_mul_29 : ∀ w : Fin 36,
    smallWord 29 * smallWord w = smallWord (mulIndex 29 w) := by
  decide +kernel

private theorem smallWord_mul_30 : ∀ w : Fin 36,
    smallWord 30 * smallWord w = smallWord (mulIndex 30 w) := by
  decide +kernel

private theorem smallWord_mul_31 : ∀ w : Fin 36,
    smallWord 31 * smallWord w = smallWord (mulIndex 31 w) := by
  decide +kernel

private theorem smallWord_mul_32 : ∀ w : Fin 36,
    smallWord 32 * smallWord w = smallWord (mulIndex 32 w) := by
  decide +kernel

private theorem smallWord_mul_33 : ∀ w : Fin 36,
    smallWord 33 * smallWord w = smallWord (mulIndex 33 w) := by
  decide +kernel

private theorem smallWord_mul_34 : ∀ w : Fin 36,
    smallWord 34 * smallWord w = smallWord (mulIndex 34 w) := by
  decide +kernel

private theorem smallWord_mul_35 : ∀ w : Fin 36,
    smallWord 35 * smallWord w = smallWord (mulIndex 35 w) := by
  decide +kernel

theorem smallWord_mul (v w : Fin 36) :
    smallWord v * smallWord w = smallWord (mulIndex v w) := by
  fin_cases v
  · exact smallWord_mul_0 w
  · exact smallWord_mul_1 w
  · exact smallWord_mul_2 w
  · exact smallWord_mul_3 w
  · exact smallWord_mul_4 w
  · exact smallWord_mul_5 w
  · exact smallWord_mul_6 w
  · exact smallWord_mul_7 w
  · exact smallWord_mul_8 w
  · exact smallWord_mul_9 w
  · exact smallWord_mul_10 w
  · exact smallWord_mul_11 w
  · exact smallWord_mul_12 w
  · exact smallWord_mul_13 w
  · exact smallWord_mul_14 w
  · exact smallWord_mul_15 w
  · exact smallWord_mul_16 w
  · exact smallWord_mul_17 w
  · exact smallWord_mul_18 w
  · exact smallWord_mul_19 w
  · exact smallWord_mul_20 w
  · exact smallWord_mul_21 w
  · exact smallWord_mul_22 w
  · exact smallWord_mul_23 w
  · exact smallWord_mul_24 w
  · exact smallWord_mul_25 w
  · exact smallWord_mul_26 w
  · exact smallWord_mul_27 w
  · exact smallWord_mul_28 w
  · exact smallWord_mul_29 w
  · exact smallWord_mul_30 w
  · exact smallWord_mul_31 w
  · exact smallWord_mul_32 w
  · exact smallWord_mul_33 w
  · exact smallWord_mul_34 w
  · exact smallWord_mul_35 w

private theorem targetWord_mul_0 : ∀ w : Fin 36,
    targetWord 0 * targetWord w = targetWord (mulIndex 0 w) := by
  decide +kernel

private theorem targetWord_mul_1 : ∀ w : Fin 36,
    targetWord 1 * targetWord w = targetWord (mulIndex 1 w) := by
  decide +kernel

private theorem targetWord_mul_2 : ∀ w : Fin 36,
    targetWord 2 * targetWord w = targetWord (mulIndex 2 w) := by
  decide +kernel

private theorem targetWord_mul_3 : ∀ w : Fin 36,
    targetWord 3 * targetWord w = targetWord (mulIndex 3 w) := by
  decide +kernel

private theorem targetWord_mul_4 : ∀ w : Fin 36,
    targetWord 4 * targetWord w = targetWord (mulIndex 4 w) := by
  decide +kernel

private theorem targetWord_mul_5 : ∀ w : Fin 36,
    targetWord 5 * targetWord w = targetWord (mulIndex 5 w) := by
  decide +kernel

private theorem targetWord_mul_6 : ∀ w : Fin 36,
    targetWord 6 * targetWord w = targetWord (mulIndex 6 w) := by
  decide +kernel

private theorem targetWord_mul_7 : ∀ w : Fin 36,
    targetWord 7 * targetWord w = targetWord (mulIndex 7 w) := by
  decide +kernel

private theorem targetWord_mul_8 : ∀ w : Fin 36,
    targetWord 8 * targetWord w = targetWord (mulIndex 8 w) := by
  decide +kernel

private theorem targetWord_mul_9 : ∀ w : Fin 36,
    targetWord 9 * targetWord w = targetWord (mulIndex 9 w) := by
  decide +kernel

private theorem targetWord_mul_10 : ∀ w : Fin 36,
    targetWord 10 * targetWord w = targetWord (mulIndex 10 w) := by
  decide +kernel

private theorem targetWord_mul_11 : ∀ w : Fin 36,
    targetWord 11 * targetWord w = targetWord (mulIndex 11 w) := by
  decide +kernel

private theorem targetWord_mul_12 : ∀ w : Fin 36,
    targetWord 12 * targetWord w = targetWord (mulIndex 12 w) := by
  decide +kernel

private theorem targetWord_mul_13 : ∀ w : Fin 36,
    targetWord 13 * targetWord w = targetWord (mulIndex 13 w) := by
  decide +kernel

private theorem targetWord_mul_14 : ∀ w : Fin 36,
    targetWord 14 * targetWord w = targetWord (mulIndex 14 w) := by
  decide +kernel

private theorem targetWord_mul_15 : ∀ w : Fin 36,
    targetWord 15 * targetWord w = targetWord (mulIndex 15 w) := by
  decide +kernel

private theorem targetWord_mul_16 : ∀ w : Fin 36,
    targetWord 16 * targetWord w = targetWord (mulIndex 16 w) := by
  decide +kernel

private theorem targetWord_mul_17 : ∀ w : Fin 36,
    targetWord 17 * targetWord w = targetWord (mulIndex 17 w) := by
  decide +kernel

private theorem targetWord_mul_18 : ∀ w : Fin 36,
    targetWord 18 * targetWord w = targetWord (mulIndex 18 w) := by
  decide +kernel

private theorem targetWord_mul_19 : ∀ w : Fin 36,
    targetWord 19 * targetWord w = targetWord (mulIndex 19 w) := by
  decide +kernel

private theorem targetWord_mul_20 : ∀ w : Fin 36,
    targetWord 20 * targetWord w = targetWord (mulIndex 20 w) := by
  decide +kernel

private theorem targetWord_mul_21 : ∀ w : Fin 36,
    targetWord 21 * targetWord w = targetWord (mulIndex 21 w) := by
  decide +kernel

private theorem targetWord_mul_22 : ∀ w : Fin 36,
    targetWord 22 * targetWord w = targetWord (mulIndex 22 w) := by
  decide +kernel

private theorem targetWord_mul_23 : ∀ w : Fin 36,
    targetWord 23 * targetWord w = targetWord (mulIndex 23 w) := by
  decide +kernel

private theorem targetWord_mul_24 : ∀ w : Fin 36,
    targetWord 24 * targetWord w = targetWord (mulIndex 24 w) := by
  decide +kernel

private theorem targetWord_mul_25 : ∀ w : Fin 36,
    targetWord 25 * targetWord w = targetWord (mulIndex 25 w) := by
  decide +kernel

private theorem targetWord_mul_26 : ∀ w : Fin 36,
    targetWord 26 * targetWord w = targetWord (mulIndex 26 w) := by
  decide +kernel

private theorem targetWord_mul_27 : ∀ w : Fin 36,
    targetWord 27 * targetWord w = targetWord (mulIndex 27 w) := by
  decide +kernel

private theorem targetWord_mul_28 : ∀ w : Fin 36,
    targetWord 28 * targetWord w = targetWord (mulIndex 28 w) := by
  decide +kernel

private theorem targetWord_mul_29 : ∀ w : Fin 36,
    targetWord 29 * targetWord w = targetWord (mulIndex 29 w) := by
  decide +kernel

private theorem targetWord_mul_30 : ∀ w : Fin 36,
    targetWord 30 * targetWord w = targetWord (mulIndex 30 w) := by
  decide +kernel

private theorem targetWord_mul_31 : ∀ w : Fin 36,
    targetWord 31 * targetWord w = targetWord (mulIndex 31 w) := by
  decide +kernel

private theorem targetWord_mul_32 : ∀ w : Fin 36,
    targetWord 32 * targetWord w = targetWord (mulIndex 32 w) := by
  decide +kernel

private theorem targetWord_mul_33 : ∀ w : Fin 36,
    targetWord 33 * targetWord w = targetWord (mulIndex 33 w) := by
  decide +kernel

private theorem targetWord_mul_34 : ∀ w : Fin 36,
    targetWord 34 * targetWord w = targetWord (mulIndex 34 w) := by
  decide +kernel

private theorem targetWord_mul_35 : ∀ w : Fin 36,
    targetWord 35 * targetWord w = targetWord (mulIndex 35 w) := by
  decide +kernel

theorem targetWord_mul (v w : Fin 36) :
    targetWord v * targetWord w = targetWord (mulIndex v w) := by
  fin_cases v
  · exact targetWord_mul_0 w
  · exact targetWord_mul_1 w
  · exact targetWord_mul_2 w
  · exact targetWord_mul_3 w
  · exact targetWord_mul_4 w
  · exact targetWord_mul_5 w
  · exact targetWord_mul_6 w
  · exact targetWord_mul_7 w
  · exact targetWord_mul_8 w
  · exact targetWord_mul_9 w
  · exact targetWord_mul_10 w
  · exact targetWord_mul_11 w
  · exact targetWord_mul_12 w
  · exact targetWord_mul_13 w
  · exact targetWord_mul_14 w
  · exact targetWord_mul_15 w
  · exact targetWord_mul_16 w
  · exact targetWord_mul_17 w
  · exact targetWord_mul_18 w
  · exact targetWord_mul_19 w
  · exact targetWord_mul_20 w
  · exact targetWord_mul_21 w
  · exact targetWord_mul_22 w
  · exact targetWord_mul_23 w
  · exact targetWord_mul_24 w
  · exact targetWord_mul_25 w
  · exact targetWord_mul_26 w
  · exact targetWord_mul_27 w
  · exact targetWord_mul_28 w
  · exact targetWord_mul_29 w
  · exact targetWord_mul_30 w
  · exact targetWord_mul_31 w
  · exact targetWord_mul_32 w
  · exact targetWord_mul_33 w
  · exact targetWord_mul_34 w
  · exact targetWord_mul_35 w

end Held.AutomorphismLocalPair.ResidualNine.PairActionCertificate.CenterImageCertificate
