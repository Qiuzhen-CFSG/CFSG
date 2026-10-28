/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalLineSigns.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolayPairSetSemidirect

/-!
The shortened Golay sign subgroup in the orthogonal-line stabilizer.
The concrete semidirect equivalence supplies its cardinality, normality, and split quotient.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalLineSigns.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- The actual Golay sign subgroup in the full local line stabilizer. -/
def orthogonalLineSignEmbedding (a : Omega) (b : Mathieu23Points a) :
    Multiplicative (GolayPairSetKernel a b) →* orthogonalLineStabilizer a b.val :=
  (fullOrthogonalLineSemidirectEquiv a b).toMonoidHom.comp SemidirectProduct.inl

def orthogonalLineSigns (a : Omega) (b : Mathieu23Points a) :
    Subgroup (orthogonalLineStabilizer a b.val) := (orthogonalLineSignEmbedding a b).range

def orthogonalLinePairProjection (a : Omega) (b : Mathieu23Points a) :
    orthogonalLineStabilizer a b.val →* Mathieu22PairModel a b :=
  SemidirectProduct.rightHom.comp (fullOrthogonalLineSemidirectEquiv a b).symm.toMonoidHom

def orthogonalLinePairSection (a : Omega) (b : Mathieu23Points a) :
    Mathieu22PairModel a b →* orthogonalLineStabilizer a b.val :=
  (fullOrthogonalLineSemidirectEquiv a b).toMonoidHom.comp SemidirectProduct.inr

theorem orthogonalLineSignEmbedding_injective (a : Omega) (b : Mathieu23Points a) :
    Function.Injective (orthogonalLineSignEmbedding a b) :=
  (fullOrthogonalLineSemidirectEquiv a b).injective.comp SemidirectProduct.inl_injective

theorem orthogonalLineSigns_card (a : Omega) (b : Mathieu23Points a) :
    Nat.card (orthogonalLineSigns a b) = 1024 := by
  change Nat.card (orthogonalLineSignEmbedding a b).range = 1024
  rw [← Nat.card_congr (MonoidHom.ofInjective (orthogonalLineSignEmbedding_injective a b)).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (GolayPairSetKernel a b) ≃ GolayPairSetKernel a b)]
  exact golay_two_coordinate_kernel_card a b.val (Ne.symm b.prop)

theorem orthogonalLinePairProjection_section (a : Omega) (b : Mathieu23Points a)
    (g : Mathieu22PairModel a b) :
    orthogonalLinePairProjection a b (orthogonalLinePairSection a b g) = g := by
  change SemidirectProduct.rightHom
    ((fullOrthogonalLineSemidirectEquiv a b).symm
      (fullOrthogonalLineSemidirectEquiv a b (SemidirectProduct.inr g))) = g
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem orthogonalLinePairProjection_surjective (a : Omega) (b : Mathieu23Points a) :
    Function.Surjective (orthogonalLinePairProjection a b) :=
  fun g => ⟨orthogonalLinePairSection a b g,orthogonalLinePairProjection_section a b g⟩

theorem orthogonalLinePairProjection_kernel (a : Omega) (b : Mathieu23Points a) :
    (orthogonalLinePairProjection a b).ker = orthogonalLineSigns a b := by
  ext g
  constructor
  · intro hg
    let x := (fullOrthogonalLineSemidirectEquiv a b).symm g
    have hx : x.right = 1 := hg
    have he : SemidirectProduct.inl x.left = x := by
      apply SemidirectProduct.ext
      · rfl
      · exact hx.symm
    refine ⟨x.left,?_⟩
    change fullOrthogonalLineSemidirectEquiv a b (SemidirectProduct.inl x.left) = g
    rw [he]
    exact (fullOrthogonalLineSemidirectEquiv a b).apply_symm_apply g
  · rintro ⟨c,rfl⟩
    change SemidirectProduct.rightHom
      ((fullOrthogonalLineSemidirectEquiv a b).symm
        (fullOrthogonalLineSemidirectEquiv a b (SemidirectProduct.inl c))) = 1
    rw [MulEquiv.symm_apply_apply]
    rfl

instance orthogonalLineSigns_normal (a : Omega) (b : Mathieu23Points a) :
    (orthogonalLineSigns a b).Normal := by
  rw [← orthogonalLinePairProjection_kernel]
  infer_instance

theorem orthogonalLineSigns_commute (a : Omega) (b : Mathieu23Points a)
    (g h : orthogonalLineSigns a b) : g*h = h*g := by
  obtain ⟨c,hc⟩ := g.prop
  obtain ⟨d,hd⟩ := h.prop
  apply Subtype.ext
  change g.val*h.val = h.val*g.val
  rw [← hc,← hd,← map_mul,← map_mul,mul_comm c d]

end Atlas.Conway
