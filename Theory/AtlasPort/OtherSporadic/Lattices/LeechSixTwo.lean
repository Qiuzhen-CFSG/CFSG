/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechSixTwo.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechTwoFourRecovery

/-!
Leech vectors with one coordinate of magnitude six and remaining support of magnitude two.
Coordinate sums and residues characterize exactly which signed supports lie in the lattice.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sixTwoVector (T : Finset Omega) (a : T) (s : T → Bit) : IntegerCoordinates :=
  fun i => (if i = a.val then 6 else 2) * signedSupport T s i

theorem sixTwo_parity (T : Finset Omega) (a : T) (s : T → Bit) (i : Omega) :
    sixTwoVector T a s i % 2 = 0 := by
  simp only [sixTwoVector]
  split_ifs <;> omega

theorem sixTwo_residue (T : Finset Omega) (a : T) (s : T → Bit) :
    halfResidue (sixTwoVector T a s) 0 = supportWord T := by
  ext i
  simp only [halfResidue,integerReduction,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
    sixTwoVector,signedSupport,supportWord]
  split_ifs <;> decide

theorem sixTwo_sum (T : Finset Omega) (a : T) (s : T → Bit) :
    (∑ i, sixTwoVector T a s i) = 2 * (T.card : ℤ) -
      4 * ∑ i : T, (if s i = 0 then (0 : ℤ) else 1) +
      4 * (if s a = 0 then (1 : ℤ) else -1) := by
  have he (i : Omega) : sixTwoVector T a s i =
      2 * signedSupport T s i + if i = a.val then 4 * (if s a = 0 then 1 else -1) else 0 := by
    by_cases hi : i = a.val
    · subst i; simp only [sixTwoVector,signedSupport,a.prop,dif_pos,ite_true]; split_ifs <;> ring
    · simp [sixTwoVector,hi]
  simp only [he,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [signedSupport_sum]
  simp
  ring

theorem sixTwo_norm (T : Finset Omega) (a : T) (s : T → Bit) :
    integerDot (sixTwoVector T a s) (sixTwoVector T a s) = 4 * (T.card : ℤ) + 32 := by
  have he (i : Omega) : sixTwoVector T a s i * sixTwoVector T a s i =
      4 * (signedSupport T s i * signedSupport T s i) + if i = a.val then 32 else 0 := by
    by_cases hi : i = a.val
    · subst i
      simp only [sixTwoVector,ite_true,signedSupport,dif_pos a.prop]
      split_ifs <;> norm_num
    · simp [sixTwoVector,hi]; ring
  simp only [integerDot,he,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [← integerDot,signedSupport_norm]
  simp

theorem sixTwo_mem_iff (T : Finset Omega) (a : T) (s : T → Bit)
    (hc : supportWord T ∈ golay) : sixTwoVector T a s ∈ leech ↔ ∑ i, s i = 1 := by
  have hw : (T.card : ℤ) % 4 = 0 := by
    have h := golay_doublyEven (supportWord T) hc
    have ht : hammingNorm (supportWord T) = T.card := by simp [hammingNorm,supportWord]
    rw [ht] at h
    omega
  have he : (∑ i : T, s i = 1) ↔
      (∑ i : T, (if s i = 0 then (0 : ℤ) else 1)) % 2 = 1 := by
    rw [← signedSupport_negative_parity]
    simpa only [Int.cast_one,Nat.cast_ofNat,Int.one_emod_two] using
      (ZMod.intCast_eq_intCast_iff' (∑ i : T, (if s i = 0 then (0 : ℤ) else 1)) 1 2)
  rw [he]
  constructor
  · intro hx
    obtain ⟨m,(rfl | rfl),hp,_,hs⟩ := (mem_leech _).mp hx
    · rw [sixTwo_sum] at hs
      split_ifs at hs <;> omega
    · have hp := hp ((0,0),0)
      have hz := sixTwo_parity T a s ((0,0),0)
      omega
  · intro hs
    apply (mem_leech _).mpr
    refine ⟨0,Or.inl rfl,sixTwo_parity T a s,?_,?_⟩
    · rw [sixTwo_residue]; exact hc
    · rw [sixTwo_sum]
      split_ifs <;> omega

end Atlas.Lattices
