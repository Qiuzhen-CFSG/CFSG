/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechOddExhaustion.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechOddProfiles

/-!
Exhaustion of odd Leech vectors of squared norms four, six, and eight.
The small norm bounds the magnitudes, and the norm equation restricts the possible support sizes.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def oddThreeSupport (x : IntegerCoordinates) : Finset Omega := Finset.univ.filter (fun i => x i * x i = 9)
def oddFiveSupport (x : IntegerCoordinates) : Finset Omega := Finset.univ.filter (fun i => x i * x i = 25)

theorem odd_small_coordinate (x : IntegerCoordinates) (hp : ∀ i, x i % 2 = 1)
    (hn : integerDot x x ≤ 64) (i : Omega) :
    x i = -5 ∨ x i = -3 ∨ x i = -1 ∨ x i = 1 ∨ x i = 3 ∨ x i = 5 := by
  have hh (j : Omega) : 0 ≤ x j * x j - 1 := by
    have h := hp j
    have hj : x j ≤ -1 ∨ 1 ≤ x j := by omega
    rcases hj with hj | hj <;> nlinarith
  have hb : x i * x i - 1 ≤ ∑ j, (x j * x j - 1) :=
    Finset.single_le_sum (fun j _ => hh j) (Finset.mem_univ i)
  have hs : (∑ j, (x j * x j - 1)) = integerDot x x - 24 := by
    simp [integerDot,Finset.sum_sub_distrib,Omega,HexIndex]
  rw [hs] at hb
  have hi : -6 ≤ x i ∧ x i ≤ 6 := by constructor <;> nlinarith
  have h := hp i
  omega

theorem odd_supports_disjoint (x : IntegerCoordinates) : Disjoint (oddThreeSupport x) (oddFiveSupport x) := by
  apply Finset.disjoint_left.mpr
  intro i ht hf
  simp only [oddThreeSupport,oddFiveSupport,Finset.mem_filter,Finset.mem_univ,true_and] at ht hf
  omega

theorem odd_profile_reconstruction (x : IntegerCoordinates) (hx : x ∈ leech)
    (hp : ∀ i, x i % 2 = 1) (hn : integerDot x x ≤ 64) :
    ∃ c : golay, x = signedOddProfile (oddThreeSupport x) (oddFiveSupport x) c := by
  have he : x - oddGlue ((0,0),0) ∈ evenGolayLattice := by
    have hc := (mem_leech x).mp hx
    obtain ⟨m,(rfl | rfl),hh,hr,hs⟩ := hc
    · have h0 := hh ((0,0),0)
      have h1 := hp ((0,0),0)
      omega
    · exact (odd_congruences ((0,0),0) x).mpr ⟨hp,hr,by simpa using hs⟩
  let c : golay := ⟨halfResidue x 1,((odd_congruences ((0,0),0) x).mp he).2.1⟩
  refine ⟨c,?_⟩
  ext i
  rcases odd_small_coordinate x hp hn i with h | h | h | h | h | h <;>
    simp [signedOddProfile,signChange,c,halfResidue,integerReduction,oddProfileBase,
      oddThreeSupport,oddFiveSupport,h] ; decide

theorem odd_small_norm_equation (x : IntegerCoordinates) (hx : x ∈ leech)
    (hp : ∀ i, x i % 2 = 1) (hn : integerDot x x ≤ 64) :
    integerDot x x = 24 + 8 * ((oddThreeSupport x).card : ℤ) + 24 * ((oddFiveSupport x).card : ℤ) := by
  obtain ⟨c,hc⟩ := odd_profile_reconstruction x hx hp hn
  conv_lhs => rw [hc]
  exact signedOddProfile_norm _ _ (odd_supports_disjoint x) c

theorem odd_minimal_profile (x : IntegerCoordinates) (hx : x ∈ leech)
    (hp : ∀ i, x i % 2 = 1) (hn : integerDot x x = 32) :
    (oddThreeSupport x).card = 1 ∧ (oddFiveSupport x).card = 0 := by
  have h := odd_small_norm_equation x hx hp (by omega)
  omega

theorem odd_six_profiles (x : IntegerCoordinates) (hx : x ∈ leech)
    (hp : ∀ i, x i % 2 = 1) (hn : integerDot x x = 48) :
    ((oddThreeSupport x).card = 3 ∧ (oddFiveSupport x).card = 0) ∨
    ((oddThreeSupport x).card = 0 ∧ (oddFiveSupport x).card = 1) := by
  have h := odd_small_norm_equation x hx hp (by omega)
  omega

theorem odd_eight_profiles (x : IntegerCoordinates) (hx : x ∈ leech)
    (hp : ∀ i, x i % 2 = 1) (hn : integerDot x x = 64) :
    ((oddThreeSupport x).card = 5 ∧ (oddFiveSupport x).card = 0) ∨
    ((oddThreeSupport x).card = 2 ∧ (oddFiveSupport x).card = 1) := by
  have h := odd_small_norm_equation x hx hp (by omega)
  omega

end Atlas.Lattices
