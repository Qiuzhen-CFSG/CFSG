/-
The Golay and affine sextet constructions used here are by Gerald Höhn and
ATLAS contributors, under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt. Their source modules record revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.HexacodeDual.Actions

/-!
# Translations on the middle sextet cocode layer

The class of a word constant on each column is its six column values' sum
times the common tetrad class. Translating the four rows changes an even
column by a constant column. Thus every actual affine translation acts
trivially on the middle quotient, with displacement in the specified line.
Only the four-bit identity is a finite calculation; the passage to the
Golay quotient uses the proved equality of all six tetrad classes.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.3(1),
printed p.400; the licensed ATLAS Golay and affine hexacode constructions.
-/

@[expose] public section

open scoped BigOperators
open Atlas.Codes
namespace MathieuCode.SextetLayers
noncomputable section

/-- A column-constant word has the indicated scalar tetrad class. -/
lemma atlasColumnConstant_class (v : AtlasCore) (hv : ∀ i k, v.val (i,k) = v.val (i,0)) :
    atlasCodeInCore.mkQ v = (∑ i, v.val (i,0)) •
      atlasCodeInCore.mkQ (atlasTetradCore (0,0)) := by
  have he : v = ∑ i, v.val (i,0) • atlasTetradCore i := by
    apply Subtype.ext
    funext p
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      atlasTetradCore, smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hv p.1 p.2
  conv_lhs => rw [he]
  rw [map_sum]
  simp_rw [map_smul, atlasTetradClass_eq _ (0,0)]
  exact Finset.sum_smul.symm

/-- Every column-constant core word represents an element of the tetrad line. -/
lemma atlasColumnConstant_class_mem (v : AtlasCore) (hv : ∀ i k, v.val (i,k) = v.val (i,0)) :
    atlasCodeInCore.mkQ v ∈ atlasTetradLine := by
  rw [atlasColumnConstant_class v hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

private lemma blockTranslation_constant : ∀ (u : K) (w : Fin 4 → Bit), (∑ k, w k) = 0 →
    ∀ k, w (rowLabel.symm (rowLabel k - u)) - w k =
      w (rowLabel.symm (rowLabel 0 - u)) - w 0 := by decide +kernel

/-- Actual translations displace pair-space vectors only along the actual tetrad line. -/
lemma atlasTranslation_displacement (t : Multiplicative hexacode) {v : AtlasCocode}
    (hv : v ∈ atlasPairSpace) :
    atlasCocodeRepresentation (sextetTranslation t) v - v ∈ atlasTetradLine := by
  obtain ⟨w, hw, rfl⟩ := hv
  rw [atlasCocodeRepresentation_mk, ← map_sub]
  apply atlasColumnConstant_class_mem
  intro i k
  change w.val (i, rowLabel.symm (rowLabel k - t.toAdd.val i)) - w.val (i,k) =
    w.val (i, rowLabel.symm (rowLabel 0 - t.toAdd.val i)) - w.val (i,0)
  exact blockTranslation_constant _ (fun k => w.val (i,k)) (congrFun hw i) k

/-- The entire actual translation subgroup acts trivially on the middle quotient. -/
lemma atlasTranslation_middle_fixed (t : Multiplicative hexacode) (v : AtlasMiddle) :
    atlasMiddleRepresentation (sextetTranslation t) v = v := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change atlasMiddleRepresentation (sextetTranslation t) (atlasLineInPair.mkQ v) =
      atlasLineInPair.mkQ v
    rw [atlasMiddleRepresentation_mk]
    apply (Submodule.Quotient.eq atlasLineInPair).mpr
    exact atlasTranslation_displacement t v.property

end
end MathieuCode.SextetLayers
