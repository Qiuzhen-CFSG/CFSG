module
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.Checks
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.Obstruction
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.SylowCoverage.Native
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Candidate
/-!
# Quadratic elementary actors on the actual M24 cocode

The literal coordinate equivalence identifies double displacement with matrix
multiplication. A quadratic elementary subgroup in the native Sylow group gives
a clique in the checked graph, hence has order at most four. Sylow conjugacy
transports this conclusion to every elementary subgroup of the native M24.
Source: Aschbacher--Smith K.4.2--3, printed pp.458--459.
-/
public section
open Sporadic.Mathieu Representation.BinaryOffender
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
open Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.CocodeOctad.Involutions
open scoped IsMulCommutative
namespace MathieuCode.QuadraticActors
set_option maxRecDepth 4096
lemma unitCoordinate_spec : ∀ x : Fin 24,
    unitCoordinate x = reduce (Pi.single x 1) := by decide +kernel
lemma displacementMatrix_point (g : M24) : displacementMatrix g = pointMatrix g.val := by
  have hs (x : Fin 24) : fullRepresentation g (Pi.single x 1) = Pi.single (g.val x) 1 := by
    ext k
    simp [fullRepresentation, Pi.single_apply, Equiv.symm_apply_eq]
  ext i j
  simp only [displacementMatrix, coordinateWord, map_add, hs, pointMatrix,
    unitCoordinate_spec, Pi.add_apply]
lemma displacementMatrix_native (v : Fin 192) :
    displacementMatrix (native v).val = matrix v := by
  rw [displacementMatrix_point, ← matrix_check v]
  congr 1
  funext x
  exact native_apply v x

lemma matrix_product_apply (a b : M24) (v : Coordinates) :
    (displacementMatrix a * displacementMatrix b).mulVecLin v =
      coordinates (cocodeRepresentation a (cocodeRepresentation b (sectionMap v) - sectionMap v) -
        (cocodeRepresentation b (sectionMap v) - sectionMap v)) := by
  have hs (x : Cocode) : sectionMap (coordinates x) = x :=
    LinearMap.congr_fun sectionMap_coordinates x
  simp only [Matrix.mulVecLin_mul, displacementMatrix_eq, LinearMap.comp_apply, hs,
    LinearMap.sub_apply, LinearMap.id_apply]

lemma matrix_product_entry (a b : M24) (i j : Fin 11) :
    (displacementMatrix a * displacementMatrix b) i j =
      coordinates (cocodeRepresentation a
        (cocodeRepresentation b (sectionMap (Pi.single j 1)) - sectionMap (Pi.single j 1)) -
        (cocodeRepresentation b (sectionMap (Pi.single j 1)) - sectionMap (Pi.single j 1))) i := by
  have h := congrFun (matrix_product_apply a b (Pi.single j 1)) i
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col, Matrix.transpose_apply] using h

lemma native_quadratic_adjacent {A : Subgroup M24} [IsElementaryAbelian 2 A]
    (hq : IsQuadratic cocodeRepresentation A) (v w : Fin 192)
    (hv : (native v).val ∈ A) (hw : (native w).val ∈ A) : adjacent v w = true := by
  have hc : compatible v w = true := native_compatible v w (Subtype.ext
    (congrArg (fun a : A => a.val) (mul_comm (⟨(native v).val,hv⟩ : A) ⟨(native w).val,hw⟩)))
  rcases rejection_check v w with hr | hr | hr
  · exact Bool.noConfusion (hc.symm.trans hr)
  · exact hr
  · exfalso
    apply hr
    rw [← displacementMatrix_native v, ← displacementMatrix_native w, matrix_product_entry]
    rw [hq _ hv _ hw, sub_self, map_zero]
    rfl

lemma native_cocode_card_le_four (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hA : A ≤ SylowNormalizer.candidate) (hq : IsQuadratic cocodeRepresentation A) :
    Nat.card A ≤ 4 := by
  classical
  let s : Finset (Fin 192) := Finset.univ.filter (fun v => (native v).val ∈ A)
  have hs : s.card ≤ 4 := clique_card_le_four 0 adjacent neighbors_check s (by
    intro v hv w hw
    exact native_quadratic_adjacent hq v w (Finset.mem_filter.mp hv).2
      (Finset.mem_filter.mp hw).2)
  let f : s → A := fun v => ⟨(native v.val).val, (Finset.mem_filter.mp v.property).2⟩
  have hf : Function.Surjective f := by
    intro a
    let b : SylowNormalizer.candidate := ⟨a.val, hA a.property⟩
    have hb : b ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
    obtain ⟨v, hv⟩ := vertex_of_square b hb
    have ha : (native v).val = a.val := congrArg Subtype.val hv
    refine ⟨⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.symm ▸ a.property⟩⟩, ?_⟩
    exact Subtype.ext ha
  have hc := Nat.card_le_card_of_surjective f hf
  have he : Nat.card s = s.card := by simp
  exact (hc.trans_eq he).trans hs

lemma m24_cocode_card_le_four (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hq : IsQuadratic cocodeRepresentation A) : Nat.card A ≤ 4 := by
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 S SextetCore.nativeSylow
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom =
      SylowNormalizer.candidate := congrArg Sylow.toSubgroup hg
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hB : B ≤ SylowNormalizer.candidate := hg' ▸ Subgroup.map_mono hAS
  have hc := native_cocode_card_le_four B hB (quadratic_conj _ hq g)
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hc
end MathieuCode.QuadraticActors
