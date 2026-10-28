/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechTwoFour.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.SupportSigns

/-!
Leech coordinate vectors with absolute values two and four.
Their support and sign data give exact norm and lattice-membership formulas.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def twoFourVector (T U : Finset Omega) (s : T → Bit) (t : U → Bit) : IntegerCoordinates :=
  fun i => 2 * signedSupport T s i + 4 * signedSupport U t i

theorem twoFour_parity (T U : Finset Omega) (s : T → Bit) (t : U → Bit) (i : Omega) :
    twoFourVector T U s t i % 2 = 0 := by unfold twoFourVector; omega

theorem twoFour_residue (T U : Finset Omega) (s : T → Bit) (t : U → Bit) :
    halfResidue (twoFourVector T U s t) 0 = supportWord T := by
  have hh : halfResidue (twoFourVector T U s t) 0 = integerReduction (signedSupport T s) := by
    ext i
    change (((twoFourVector T U s t i - 0) / 2 : ℤ) : Bit) = _
    have he : twoFourVector T U s t i = 2 * (signedSupport T s i + 2 * signedSupport U t i) := by
      unfold twoFourVector; ring
    rw [sub_zero,he,Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
    simp [integerReduction]
  exact hh.trans (signedSupport_reduction T s)

theorem twoFour_norm (T U : Finset Omega) (hd : Disjoint T U) (s : T → Bit) (t : U → Bit) :
    integerDot (twoFourVector T U s t) (twoFourVector T U s t) =
      4 * (T.card : ℤ) + 16 * (U.card : ℤ) := by
  have hh (i : Omega) : twoFourVector T U s t i * twoFourVector T U s t i =
      4 * (signedSupport T s i * signedSupport T s i) +
      16 * (signedSupport U t i * signedSupport U t i) := by
    have h : ¬(i ∈ T ∧ i ∈ U) := fun h => Finset.disjoint_left.mp hd h.1 h.2
    simp only [twoFourVector,signedSupport]
    split_ifs <;> simp_all
  simp only [integerDot,hh,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [← integerDot,← integerDot,signedSupport_norm,signedSupport_norm]

theorem twoFour_sum (T U : Finset Omega) (s : T → Bit) (t : U → Bit) :
    (∑ i, twoFourVector T U s t i) = 2 * (T.card : ℤ) + 4 * (U.card : ℤ) -
      4 * ∑ i : T, (if s i = 0 then (0 : ℤ) else 1) -
      8 * ∑ i : U, (if t i = 0 then (0 : ℤ) else 1) := by
  simp only [twoFourVector,Finset.sum_add_distrib,← Finset.mul_sum,signedSupport_sum]
  ring

theorem twoFour_mem_iff (T U : Finset Omega) (s : T → Bit) (t : U → Bit)
    (hc : supportWord T ∈ golay) :
    twoFourVector T U s t ∈ leech ↔ ∑ i : T, s i = (U.card : Bit) := by
  have hw : (T.card : ℤ) % 4 = 0 := by
    have h := golay_doublyEven (supportWord T) hc
    have ht : hammingNorm (supportWord T) = T.card := by simp [hammingNorm,supportWord]
    rw [ht] at h
    omega
  have hp := signedSupport_negative_parity T s
  have he : (∑ i : T, s i = (U.card : Bit)) ↔
      (∑ i : T, (if s i = 0 then (0 : ℤ) else 1)) % 2 = (U.card : ℤ) % 2 := by
    rw [← hp]
    simpa only [Int.cast_natCast,Nat.cast_ofNat] using (ZMod.intCast_eq_intCast_iff' (∑ i : T, (if s i = 0 then (0 : ℤ) else 1)) (U.card : ℤ) 2)
  rw [he]
  constructor
  · intro hx
    obtain ⟨m,(rfl | rfl),hh,_,hs⟩ := (mem_leech _).mp hx
    · rw [twoFour_sum] at hs
      omega
    · have hh := hh ((0,0),0)
      have hz := twoFour_parity T U s t ((0,0),0)
      omega
  · intro hs
    apply (mem_leech _).mpr
    refine ⟨0,Or.inl rfl,twoFour_parity T U s t,?_,?_⟩
    · rw [twoFour_residue]; exact hc
    · rw [twoFour_sum]; omega

end Atlas.Lattices
