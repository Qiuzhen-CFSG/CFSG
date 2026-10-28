module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.PointData
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedLocalData

/-!
# Constructed local geometry on the literal native J4 model

Apply the marked cocode constructor to the certified kernel at the literal
matrix generator a. The actual centralizer conjugator aligns that kernel
with the common Sylow Thompson subgroup. All PointData, LineData and
LocalData fields are constructed, with the supplied cubic quotient and
Sylow retained and both Todd markings transported by that same element.

The proved native generation identity transports with the point subgroup.
The native full cubic-centralizer and normalizer results supply AS91 (4.9)
on the same LocalData. No native simplicity, local-data, splitting,
generation or comparison premise is assumed. The original Mathieu adapter
uses this geometry in the already proved local point/plane comparison;
edge alignment and final recognition remain separate obligations.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.4)--(4.9) and (8.3), pp.597--599,606,
DOI 10.1007/BF01232280. The imported native cocode and generation
certificates retain their ATLAS attribution.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCocode
open Janko4 Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open LocalGeometry LocalGeometry.LocalSubgroups
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

/-- Complete native local data, with the actual cocode and M24 markings transported together. -/
theorem first_localData
    (cubic : CubicAutomorphismQuotient (centralizer Janko4.a ⧸ core Janko4.a))
    (X : Sylow 3 (CubicLift.subgroup cubic)) :
    ∃ (data : SourceIncidence.LocalData model_isTypeJ4) (g : centralizer Janko4.a),
      data.e = cubic ∧ HEq data.X X ∧ data.P.E = firstKernel.map (MulAut.conj (g : Model)).toMonoidHom ∧
      data.P.M = (normalizer (firstKernel : Set Model)).map (MulAut.conj (g : Model)).toMonoidHom ∧
      (∀ w : firstKernel, data.P.vectorEmbedding
        (Multiplicative.ofAdd (firstModule (Additive.ofMul w))) = MulAut.conj (g : Model) w.val) ∧
      ∃ m : normalizer (firstKernel : Set Model) ≃* data.P.M,
        (∀ n, (m n).val = MulAut.conj (g : Model) n.val) ∧
        ∀ n, data.P.projection (m n) = firstProjection n :=
  marked_cocode_localData firstKernel firstProjection firstProjection_surjective firstProjection_ker
    firstModule firstModule_equivariant firstMarker standardSextet firstMarker_coordinates
    model_isTypeJ4 cubic X

/-- Generation and AS91 (4.9) hold on the same constructed native local geometry. -/
theorem first_local_geometry
    (cubic : CubicAutomorphismQuotient (centralizer Janko4.a ⧸ core Janko4.a))
    (X : Sylow 3 (CubicLift.subgroup cubic)) :
    ∃ (data : SourceIncidence.LocalData model_isTypeJ4) (g : centralizer Janko4.a),
      data.e = cubic ∧ HEq data.X X ∧ data.P.E = firstKernel.map (MulAut.conj (g : Model)).toMonoidHom ∧
      data.P.M = (normalizer (firstKernel : Set Model)).map (MulAut.conj (g : Model)).toMonoidHom ∧
      (∀ w : firstKernel, data.P.vectorEmbedding
        (Multiplicative.ofAdd (firstModule (Additive.ofMul w))) = MulAut.conj (g : Model) w.val) ∧
      (∃ m : normalizer (firstKernel : Set Model) ≃* data.P.M,
        (∀ n, (m n).val = MulAut.conj (g : Model) n.val) ∧
        ∀ n, data.P.projection (m n) = firstProjection n) ∧
      centralizer Janko4.a ⊔ data.P.M = ⊤ ∧
      Nonempty (SourceComparison.CubicNormalizerData data) := by
  obtain ⟨data,g,hc,hX,hE,hM,hv,hm⟩ := first_localData cubic X
  refine ⟨data,g,hc,hX,hE,hM,hv,hm,?_,first_cubicNormalizerData data⟩
  let c := MulAut.conj (g : Model)
  have hh := congrArg (Subgroup.map c.toMonoidHom) first_generate
  have hfix : c Janko4.a = Janko4.a :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property)
  have he : (centralizer Janko4.a).map c.toMonoidHom = centralizer Janko4.a := by
    rw [Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton,hfix]
  rw [Subgroup.map_sup,he,map_top_of_surjective _ c.surjective] at hh
  rw [hM]
  exact hh

/-- Existence of compatible native local algebra with generation and the full cubic normalizer. -/
theorem exists_first_local_geometry :
    ∃ data : SourceIncidence.LocalData model_isTypeJ4,
      centralizer Janko4.a ⊔ data.P.M = ⊤ ∧
      Nonempty (SourceComparison.CubicNormalizerData data) := by
  obtain ⟨cubic⟩ := model_isTypeJ4.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (CubicLift.subgroup cubic)))
  obtain ⟨data,_,_,_,_,_,_,_,hgen,hc⟩ := first_local_geometry cubic X
  exact ⟨data,hgen,hc⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCocode
