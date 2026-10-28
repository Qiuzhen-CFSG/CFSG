module
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.Native
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Marking
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules
/-!
# Quadratic actors on the actual ten-dimensional M22 cocode

The compatible Sylow group is the literal intersection of a conjugate M24 Sylow
with the pair stabilizer. Its 72 square-one elements are drawn from the native
vertex list. Quadraticity on the quotient by the pair line makes each double
displacement lie in that same line, so the checked quotient graph bounds the
actor's order by four. Conjugacy of Sylow groups removes the Sylow placement.
Source: Aschbacher--Smith H.13.1 and K.4.4, printed pp.395,459.
-/
@[expose] public section
open Sporadic.Mathieu Representation.BinaryOffender
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
open Sporadic.Mathieu.M24LocalGeometry
open MathieuCode MathieuCode.CocodeOctad.Involutions
open scoped IsMulCommutative
namespace MathieuCode.QuadraticActors
set_option maxRecDepth 4096
noncomputable section

def transportNative (v : Fin 192) : M24 := MulAut.conj M22ChapterH.CompatibleSylow.transport (native v).val
def conjugatedPoint (v : Fin 192) (x : Fin 24) : Fin 24 :=
  transportPoint (vertexPoint v (transportInvPoint x))
lemma transportNative_apply (v : Fin 192) (x : Fin 24) :
    (transportNative v).val x = conjugatedPoint v x := by
  change M22ChapterH.CompatibleSylow.transportPerm ((native v).val.val (M22ChapterH.CompatibleSylow.transportPerm.symm x)) = _
  rw [native_apply]
  rfl

def outerNative (v : Fin 72) : M24 := transportNative (outerVertex v)
lemma outerNative_apply (v : Fin 72) (x : Fin 24) :
    (outerNative v).val x = outerPoint v x := transportNative_apply _ _
lemma displacementMatrix_outerNative (v : Fin 72) :
    displacementMatrix (outerNative v) = outerMatrix v := by
  rw [displacementMatrix_point, ← outer_matrix_check v]
  congr 1
  funext x
  exact outerNative_apply v x

lemma pair_vertex_coverage : ∀ v : Fin 192,
    (conjugatedPoint v 0 = 0 ∨ conjugatedPoint v 0 = 9) →
    (conjugatedPoint v 9 = 0 ∨ conjugatedPoint v 9 = 9) →
    outerVertex (outerCode v) = v := by decide +kernel

lemma outer_vertex_of_square (a : m22PairStabilizer) (ha : a ∈ M22ChapterH.CompatibleSylow.outerGroup)
    (ha2 : a ^ 2 = 1) : ∃ v : Fin 72, outerNative v = a.val := by
  have hm : a.val ∈ M22ChapterH.CompatibleSylow.ambient.toSubgroup := ha
  rw [M22ChapterH.CompatibleSylow.ambient_coe] at hm
  obtain ⟨g, hg, hga⟩ := hm
  change MulAut.conj M22ChapterH.CompatibleSylow.transport g = a.val at hga
  let b : SylowNormalizer.candidate := ⟨g, hg⟩
  have hb : b ^ 2 = 1 := by
    apply Subtype.ext
    apply (MulAut.conj M22ChapterH.CompatibleSylow.transport).injective
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one, b, hga] using
      congrArg Subtype.val ha2
  obtain ⟨v, hv⟩ := vertex_of_square b hb
  have hva : transportNative v = a.val :=
    (congrArg (MulAut.conj M22ChapterH.CompatibleSylow.transport) (congrArg Subtype.val hv)).trans hga
  have hpair (x : Fin 24) (hx : x ∈ m22Pair) :
      conjugatedPoint v x = 0 ∨ conjugatedPoint v x = 9 := by
    have h := MulAction.mem_stabilizer_finset'.mp a.property hx
    change a.val.val x ∈ m22Pair at h
    rw [← hva, transportNative_apply] at h
    simpa only [m22Pair, Finset.mem_insert, Finset.mem_singleton] using h
  have hv' := pair_vertex_coverage v (hpair 0 (by simp [m22Pair]))
    (hpair 9 (by simp [m22Pair]))
  refine ⟨outerCode v, ?_⟩
  simpa only [outerNative, hv'] using hva

lemma pair_coordinates : coordinates m22PairClass = pairCoordinate := by
  ext i
  change reduce m22PairWord i = pairCoordinate i
  revert i
  decide +kernel

lemma pair_line_coordinate (x : Cocode) (hx : x ∈ m22PairLine) (i : Fin 11) :
    coordinates x i - coordinates x 0 * pairCoordinate i = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  rw [← hc, map_smul, pair_coordinates]
  change c * pairCoordinate i - (c * pairCoordinate 0) * pairCoordinate i = 0
  rw [show pairCoordinate 0 = 1 from by decide +kernel, mul_one, sub_self]

lemma outer_quadratic_adjacent {A : Subgroup m22PairStabilizer}
    [IsElementaryAbelian 2 A] (hq : IsQuadratic m22OuterCocodeRepresentation A)
    (a b : A) (v w : Fin 72) (hv : outerNative v = a.val.val)
    (hw : outerNative w = b.val.val) : outerAdjacent v w = true := by
  have hab : outerNative v * outerNative w = outerNative w * outerNative v := by
    rw [hv, hw]
    exact congrArg (fun a : A => a.val.val) (mul_comm a b)
  have hn : native (outerVertex v) * native (outerVertex w) =
      native (outerVertex w) * native (outerVertex v) := by
    apply Subtype.ext
    apply (MulAut.conj M22ChapterH.CompatibleSylow.transport).injective
    simpa only [Subgroup.coe_mul, map_mul, outerNative, transportNative] using hab
  have hc := native_compatible _ _ hn
  rcases outer_rejection_check v w with hr | hr | hr
  · exact Bool.noConfusion (hc.symm.trans hr)
  · exact hr
  · exfalso
    apply hr
    rw [← displacementMatrix_outerNative v, ← displacementMatrix_outerNative w, hv, hw,
      matrix_product_entry, matrix_product_entry]
    apply pair_line_coordinate
    apply (Submodule.Quotient.mk_eq_zero m22PairLine).mp
    change m22PairLine.mkQ _ = (0 : M22Cocode)
    have hh := hq a.val a.property b.val b.property
      (m22PairLine.mkQ (sectionMap (Pi.single (outerRejectCol v w) 1)))
    simpa only [map_sub, m22OuterCocodeRepresentation_mk] using sub_eq_zero.mpr hh

lemma outer_sylow_cocode_card_le_four (A : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A] (hA : A ≤ M22ChapterH.CompatibleSylow.outerGroup)
    (hq : IsQuadratic m22OuterCocodeRepresentation A) : Nat.card A ≤ 4 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hex (a : A) : ∃ v : Fin 72, outerNative v = a.val.val :=
    outer_vertex_of_square a.val (hA a.property)
      (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
  choose f hf using hex
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact (hf a).symm.trans ((congrArg outerNative hab).trans (hf b))
  let s : Finset (Fin 72) := Finset.univ.image f
  have hc : Nat.card A = s.card := by
    simp only [s, Finset.card_image_of_injective _ hi, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [hc]
  apply clique_card_le_four 0 outerAdjacent outer_neighbors_check
  intro v hv w hw
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hw
  exact outer_quadratic_adjacent hq a b (f a) (f b) (hf a) (hf b)

lemma m22Outer_cocode_card_le_four (A : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A] (hq : IsQuadratic m22OuterCocodeRepresentation A) :
    Nat.card A ≤ 4 := by
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq m22PairStabilizer S M22ChapterH.CompatibleSylow.outer
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom = M22ChapterH.CompatibleSylow.outerGroup :=
    congrArg Sylow.toSubgroup hg
  let B := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hB : B ≤ M22ChapterH.CompatibleSylow.outerGroup := hg' ▸ Subgroup.map_mono hAS
  have hc := outer_sylow_cocode_card_le_four B hB (quadratic_conj _ hq g)
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hc
end
end MathieuCode.QuadraticActors
