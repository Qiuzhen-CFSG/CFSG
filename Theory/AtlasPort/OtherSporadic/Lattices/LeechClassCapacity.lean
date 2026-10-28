/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechClassCapacity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechShortClassBounds
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
Capacity bounds for short-shell fibers over mod-two classes.
Short fibers are antipodal; norm-eight antipodal pairs give independent orthogonal vectors.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev ShellClassFiber (r : ℤ) (a : LeechModTwo) := {x : LeechShell r // leechReduction x.val = a}
instance (r : ℤ) (a : LeechModTwo) : Fintype (ShellClassFiber r a) := Fintype.ofFinite _

def shellClassVector (r : ℤ) (a : LeechModTwo) (x : ShellClassFiber r a) : leech := x.val.val

theorem shellClassVector_injective (r : ℤ) (a : LeechModTwo) : Function.Injective (shellClassVector r a) := by
  intro x y h
  apply Subtype.ext; apply Subtype.ext; exact h

def antipodalPair (x : leech) : Finset leech := {x,-x}

theorem antipodalPair_card_le (x : leech) : (antipodalPair x).card ≤ 2 := by
  have h := Finset.card_pair_eq_one_or_two (a := x) (b := -x)
  change ({x,-x} : Finset leech).card ≤ 2
  omega

theorem antipodalPair_neg (x : leech) : antipodalPair (-x) = antipodalPair x := by
  simp [antipodalPair,Finset.pair_comm]

theorem short_class_capacity (r : ℤ) (hr : r < 8) (a : LeechModTwo) :
    Nat.card (ShellClassFiber r a) ≤ 2 := by
  by_cases he : Nonempty (ShellClassFiber r a)
  · obtain ⟨x⟩ := he
    let S := Finset.univ.image (shellClassVector r a)
    have hs : S ⊆ antipodalPair x.val.val := by
      intro y hy
      obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hy
      have hn1 := leech_shell_halfNorm r x.val
      have hn2 := leech_shell_halfNorm r z.val
      have h := leech_congruent_short_unique z.val.val x.val.val (z.prop.trans x.prop.symm) (by omega)
      simpa only [antipodalPair,Finset.mem_insert,Finset.mem_singleton,shellClassVector] using h
    have hc : S.card = Nat.card (ShellClassFiber r a) := by
      rw [Finset.card_image_of_injective _ (shellClassVector_injective r a),Finset.card_univ,Nat.card_eq_fintype_card]
    rw [← hc]
    exact (Finset.card_le_card hs).trans (antipodalPair_card_le _)
  · have : IsEmpty (ShellClassFiber r a) := not_nonempty_iff.mp he
    simp

theorem norm_eight_representative_bound {ι : Type*} [Fintype ι] (f : ι → leech)
    (hn : ∀ i, leechHalfNorm (f i) = 4)
    (hc : ∀ i j, leechReduction (f i) = leechReduction (f j))
    (he : ∀ i j, i ≠ j → f i ≠ f j ∧ f i ≠ -(f j)) : Fintype.card ι ≤ 24 := by
  have hi : LinearIndependent ℚ (fun i => rationalEmbedding (f i).val) := by
    apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := rationalForm)
    · intro i j hij
      change rationalForm (rationalEmbedding (f i).val) (rationalEmbedding (f j).val) = 0
      rw [← leechIntegralPairing_rational]
      rw [leech_norm_eight_congruent_orthogonal _ _ (hn i) (hn j) (hc i j) (he i j hij).1 (he i j hij).2]
      simp
    · intro i
      rw [← leechIntegralPairing_rational,leechIntegralPairing_self,hn i]
      norm_num
  have hb := hi.fintype_card_le_finrank
  simpa [RationalCoordinates,Module.finrank_pi,Omega,HexIndex] using hb

def normEightPairs (a : LeechModTwo) : Finset (Finset leech) :=
  Finset.univ.image (fun x : ShellClassFiber 8 a => antipodalPair x.val.val)

def normEightPairRepresentative (a : LeechModTwo) (p : normEightPairs a) : ShellClassFiber 8 a :=
  Classical.choose (Finset.mem_image.mp p.prop)

theorem normEightPairRepresentative_pair (a : LeechModTwo) (p : normEightPairs a) :
    antipodalPair (normEightPairRepresentative a p).val.val = p.val :=
  (Classical.choose_spec (Finset.mem_image.mp p.prop)).2

theorem normEightPairs_card (a : LeechModTwo) : (normEightPairs a).card ≤ 24 := by
  have hb := norm_eight_representative_bound (fun p : normEightPairs a => (normEightPairRepresentative a p).val.val)
    (by intro p; have h := leech_shell_halfNorm 8 (normEightPairRepresentative a p).val; omega)
    (fun p q => (normEightPairRepresentative a p).prop.trans (normEightPairRepresentative a q).prop.symm)
    (by
      intro p q hpq
      constructor
      · intro h
        apply hpq
        apply Subtype.ext
        rw [← normEightPairRepresentative_pair a p,← normEightPairRepresentative_pair a q,h]
      · intro h
        apply hpq
        apply Subtype.ext
        rw [← normEightPairRepresentative_pair a p,← normEightPairRepresentative_pair a q,h,antipodalPair_neg])
  simpa using hb

theorem norm_eight_class_pair_bound (a : LeechModTwo) :
    Nat.card (ShellClassFiber 8 a) ≤ 2 * (normEightPairs a).card := by
  let S := Finset.univ.image (shellClassVector 8 a)
  have hs : S ⊆ (normEightPairs a).biUnion id := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_biUnion.mpr
    refine ⟨antipodalPair y.val.val,Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩,?_⟩
    simp [antipodalPair,shellClassVector]
  have hc : S.card = Nat.card (ShellClassFiber 8 a) := by
    rw [Finset.card_image_of_injective _ (shellClassVector_injective 8 a),Finset.card_univ,Nat.card_eq_fintype_card]
  rw [← hc]
  calc
    S.card ≤ ((normEightPairs a).biUnion id).card := Finset.card_le_card hs
    _ ≤ ∑ p ∈ normEightPairs a, p.card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ normEightPairs a, 2 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hp
      exact antipodalPair_card_le _
    _ = 2 * (normEightPairs a).card := by simp [mul_comm]


theorem norm_eight_class_capacity (a : LeechModTwo) : Nat.card (ShellClassFiber 8 a) ≤ 48 := by
  have h := norm_eight_class_pair_bound a
  have hp := normEightPairs_card a
  omega

end Atlas.Lattices
