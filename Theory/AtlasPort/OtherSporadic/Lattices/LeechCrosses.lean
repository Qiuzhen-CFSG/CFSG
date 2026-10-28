/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechCrosses.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechClassSaturation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Intrinsic Leech crosses are classes of minimum squared norm eight.
Saturated fibers contain twenty-four antipodal pairs whose representatives form an orthogonal rational basis.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def MinimumEightClass (a : LeechModTwo) : Prop :=
  (∃ x : leech, leechReduction x = a ∧ leechHalfNorm x = 4) ∧
  ∀ y : leech, leechReduction y = a → 4 ≤ leechHalfNorm y

theorem minimumEightClass_iff (a : LeechModTwo) : MinimumEightClass a ↔ a ∈ shellClasses 8 := by
  constructor
  · rintro ⟨⟨x,hx,hn⟩,_⟩
    have hs : integerDot x.val x.val = 64 := by have h := leechHalfNorm_mul x; omega
    exact Finset.mem_image.mpr ⟨⟨x,hs⟩,Finset.mem_univ _,hx⟩
  · intro ha
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp ha
    have hn : leechHalfNorm x.val = 4 := by have h := leech_shell_halfNorm 8 x; omega
    refine ⟨⟨x.val,hx,hn⟩,?_⟩
    intro y hy
    by_contra h
    have he := leech_congruent_short_unique y x.val (hy.trans hx.symm) (by omega)
    rcases he with he | he
    · rw [he] at h; omega
    · rw [he,leechHalfNorm_neg] at h; omega

/-- An intrinsic cross is a class of minimum squared norm eight in the actual quotient. -/
abbrev LeechCross := {a : LeechModTwo // MinimumEightClass a}
instance : Fintype LeechCross := inferInstance

def leechCrossEquiv : LeechCross ≃ {a // a ∈ shellClasses 8} :=
  Equiv.subtypeEquivRight minimumEightClass_iff

theorem leechCross_card : Nat.card LeechCross = 8292375 := by
  rw [Nat.card_congr leechCrossEquiv,Nat.card_eq_fintype_card,Fintype.card_coe,shellClasses_counts.2.2]

def crossVectors (c : LeechCross) : Finset leech := Finset.univ.image (shellClassVector 8 c.val)

theorem crossVectors_mem (c : LeechCross) (x : leech) :
    x ∈ crossVectors c ↔ leechReduction x = c.val ∧ integerDot x.val x.val = 64 := by
  constructor
  · intro hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨y.prop,y.val.prop⟩
  · rintro ⟨hc,hn⟩
    exact Finset.mem_image.mpr ⟨⟨⟨x,hn⟩,hc⟩,Finset.mem_univ _,rfl⟩

theorem crossVectors_card (c : LeechCross) : (crossVectors c).card = 48 := by
  rw [crossVectors,Finset.card_image_of_injective _ (shellClassVector_injective 8 c.val),
    Finset.card_univ,← Nat.card_eq_fintype_card,norm_eight_fiber_card c.val ((minimumEightClass_iff c.val).mp c.prop)]

theorem crossPairs_card (c : LeechCross) : (normEightPairs c.val).card = 24 := by
  have hb := norm_eight_class_pair_bound c.val
  have hp := normEightPairs_card c.val
  rw [norm_eight_fiber_card c.val ((minimumEightClass_iff c.val).mp c.prop)] at hb
  omega

theorem leechReduction_neg (x : leech) : leechReduction (-x) = leechReduction x := by
  apply (leechReduction_eq_iff _ _).mpr
  exact ⟨-x,by rw [two_nsmul]; abel⟩

theorem crossVectors_neg (c : LeechCross) (x : leech) (hx : x ∈ crossVectors c) : -x ∈ crossVectors c := by
  rw [crossVectors_mem] at hx ⊢
  refine ⟨by rw [leechReduction_neg]; exact hx.1,?_⟩
  simpa [integerDot] using hx.2

theorem crossVectors_orthogonal (c : LeechCross) (x y : leech)
    (hx : x ∈ crossVectors c) (hy : y ∈ crossVectors c) (he : x ≠ y) (hn : x ≠ -y) :
    rationalForm (rationalEmbedding x.val) (rationalEmbedding y.val) = 0 := by
  rw [crossVectors_mem] at hx hy
  have hnx : leechHalfNorm x = 4 := by have h := leechHalfNorm_mul x; omega
  have hny : leechHalfNorm y = 4 := by have h := leechHalfNorm_mul y; omega
  rw [← leechIntegralPairing_rational,leech_norm_eight_congruent_orthogonal _ _ hnx hny (hx.1.trans hy.1.symm) he hn]
  simp

def crossRepresentativeVector (c : LeechCross) (p : normEightPairs c.val) : RationalCoordinates :=
  rationalEmbedding (normEightPairRepresentative c.val p).val.val.val

theorem crossRepresentatives_independent (c : LeechCross) :
    LinearIndependent ℚ (crossRepresentativeVector c) := by
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := rationalForm)
  · intro p q hpq
    change rationalForm (crossRepresentativeVector c p) (crossRepresentativeVector c q) = 0
    apply crossVectors_orthogonal c
    · exact (crossVectors_mem _ _).mpr ⟨(normEightPairRepresentative c.val p).prop,
        (normEightPairRepresentative c.val p).val.prop⟩
    · exact (crossVectors_mem _ _).mpr ⟨(normEightPairRepresentative c.val q).prop,
        (normEightPairRepresentative c.val q).val.prop⟩
    · intro h
      apply hpq; apply Subtype.ext
      rw [← normEightPairRepresentative_pair c.val p,← normEightPairRepresentative_pair c.val q,h]
    · intro h
      apply hpq; apply Subtype.ext
      rw [← normEightPairRepresentative_pair c.val p,← normEightPairRepresentative_pair c.val q,h,antipodalPair_neg]
  · intro p
    change rationalForm (rationalEmbedding _) (rationalEmbedding _) ≠ 0
    rw [rationalForm_integer,(normEightPairRepresentative c.val p).val.prop]
    norm_num

theorem crossRepresentatives_span (c : LeechCross) :
    Submodule.span ℚ (Set.range (crossRepresentativeVector c)) = ⊤ := by
  apply (crossRepresentatives_independent c).span_eq_top_of_card_eq_finrank'
  simp [crossPairs_card,RationalCoordinates,Omega,HexIndex]

end Atlas.Lattices
