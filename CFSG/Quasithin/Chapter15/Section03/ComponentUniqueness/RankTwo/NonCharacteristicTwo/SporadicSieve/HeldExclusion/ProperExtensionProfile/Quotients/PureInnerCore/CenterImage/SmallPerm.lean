module
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic

/-!
# The small permutation certificate for the pure Held center action

These four permutations encode the proposed action on the sixteen binary
central words. The 36 mixed-radix words are distinct. A fourth-power test
excludes every nonidentity word from a normal two-subgroup of order dividing
36. The Action module connects these permutations to literal conjugation;
this finite certificate alone makes no claim about Held.

Source: PureInnerCore/source/discover.py, with columns obtained from the
certified ResidualRoots.Pair00 conjugation identities.
-/
@[expose] public section

set_option Elab.async false
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CenterImageCertificate

def forward : Fin 4 → Fin 16 → Fin 16 :=
  ![![0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10],
    ![0, 8, 12, 4, 7, 15, 11, 3, 9, 1, 5, 13, 14, 6, 2, 10],
    ![0, 1, 2, 3, 7, 6, 5, 4, 9, 8, 11, 10, 14, 15, 12, 13],
    ![0, 2, 1, 3, 7, 5, 6, 4, 14, 12, 15, 13, 9, 11, 8, 10]]

def backward : Fin 4 → Fin 16 → Fin 16 :=
  ![![0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5],
    ![0, 9, 14, 7, 3, 10, 13, 4, 1, 8, 15, 6, 2, 11, 12, 5],
    ![0, 1, 2, 3, 7, 6, 5, 4, 9, 8, 11, 10, 14, 15, 12, 13],
    ![0, 2, 1, 3, 7, 5, 6, 4, 14, 12, 15, 13, 9, 11, 8, 10]]

theorem left_inverse : ∀ k v, backward k (forward k v) = v := by
  decide +kernel

theorem right_inverse : ∀ k v, forward k (backward k v) = v := by
  decide +kernel

def smallGenerator (k : Fin 4) : Equiv.Perm (Fin 16) where
  toFun := forward k
  invFun := backward k
  left_inv := left_inverse k
  right_inv := right_inverse k

def word {G : Type*} [Group G] (v : Fin 36) (a : Fin 4 → G) : G :=
  a 0 ^ (v.val % 3) * a 1 ^ (v.val / 3 % 3) *
    a 2 ^ (v.val / 9 % 2) * a 3 ^ (v.val / 18)

theorem map_word {G H : Type*} [Group G] [Group H] (f : G →* H)
    (v : Fin 36) (a : Fin 4 → G) : f (word v a) = word v (fun k => f (a k)) := by
  simp only [word, map_mul, map_pow]

def smallWord (v : Fin 36) : Equiv.Perm (Fin 16) := word v smallGenerator

theorem smallWord_injective : Function.Injective smallWord := by
  decide +kernel

/-- Normality puts w(rwr⁻¹) in every normal subgroup containing w.
The fourth-power tests for r₀ and r₁ exclude every nonidentity word. -/
theorem fourth_power_test : ∀ v : Fin 36, smallWord v ^ 4 = 1 →
    (smallWord v * smallGenerator 0 * smallWord v * (smallGenerator 0)⁻¹) ^ 4 = 1 →
    (smallWord v * smallGenerator 1 * smallWord v * (smallGenerator 1)⁻¹) ^ 4 = 1 →
    v = 0 := by
  decide +kernel

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CenterImageCertificate
