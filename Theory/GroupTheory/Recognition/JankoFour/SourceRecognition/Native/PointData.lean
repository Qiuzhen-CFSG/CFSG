module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.Normalizer
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedPointData
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.Defs

/-!
# Native point data at the literal first J4 generator

Conjugate the certified max1 cocode kernel by an actual ambient element
carrying its sextet marker to a. Transport the quotient projection and
cocode coordinates by that same conjugator. The marked point construction
then supplies the split Todd group and its exact hexad overlap for every
cubic quotient at a, preserving both quotient and vector markings.

The known native generation theorem transports with these subgroups.
The same cocode marking also proves perfectness of the original full
cubic centralizer and an involutory splitting of its normalizer, before
any native LocalData is assumed. These supply the native AS91 (4.9)
premises of the plane comparison. Compatible line data and the remaining
section 8 overlap alignment are separate construction obligations.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.8)--(4.9) and (8.3), pp.598--599,606,
DOI 10.1007/BF01232280. The native model and its fusion and generation
certificates retain the ATLAS attribution in the imported modules.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCocode
open Janko4 Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open LocalGeometry LocalGeometry.LocalSubgroups
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

private def move : MulAut Model := MulAut.conj (Classical.choose (isConj_iff.mp marker_isConj.symm))
private theorem move_marker : move (marker : Model) = Janko4.a :=
  Classical.choose_spec (isConj_iff.mp marker_isConj.symm)

/-- The original embedded max1 kernel conjugated to contain the literal generator a. -/
def firstKernel : Subgroup Model := W.map move.toMonoidHom
instance firstKernel_elementary : IsElementaryAbelian 2 firstKernel := IsElementaryAbelian.map _

private def firstEmbedding : W ≃* firstKernel := move.subgroupMap W
private theorem firstEmbedding_val (w : W) : (firstEmbedding w).val = move w.val := rfl

private def moveNormalizer : normalizer (W : Set Model) ≃* normalizer (firstKernel : Set Model) :=
  (move.subgroupMap (normalizer (W : Set Model))).trans
    (MulEquiv.subgroupCongr (W.map_equiv_normalizer_eq move))
private theorem moveNormalizer_val (n : normalizer (W : Set Model)) :
    (moveNormalizer n).val = move n.val := rfl

/-- The transported original M24 marking on the full native normalizer. -/
def firstProjection : normalizer (firstKernel : Set Model) →* M24 :=
  normalizerProjection.comp moveNormalizer.symm.toMonoidHom

/-- The transported cocode coordinates on the same actual kernel. -/
def firstModule : Additive firstKernel ≃ₗ[ZMod 2] Cocode :=
  (firstEmbedding.symm.toAdditive.toLinearEquiv (ZMod.map_smul _)).trans moduleEquiv

theorem firstProjection_surjective : Function.Surjective firstProjection :=
  normalizerProjection_surjective.comp moveNormalizer.symm.surjective

theorem firstProjection_ker :
    firstProjection.ker = firstKernel.subgroupOf (normalizer (firstKernel : Set Model)) := by
  ext n
  obtain ⟨n,rfl⟩ := moveNormalizer.surjective n
  change normalizerProjection (moveNormalizer.symm (moveNormalizer n)) = 1 ↔ move n.val ∈ firstKernel
  rw [moveNormalizer.symm_apply_apply,←MonoidHom.mem_ker,normalizerProjection_ker]
  constructor
  · intro hn
    exact mem_map_of_mem _ hn
  · rintro ⟨w,hw,he⟩
    change n.val ∈ W
    exact move.injective he ▸ hw

theorem firstModule_equivariant (n : normalizer (firstKernel : Set Model)) (v : firstKernel) :
    firstModule (Additive.ofMul (firstKernel.normalizerMonoidHom n v)) =
      cocodeRepresentation (firstProjection n) (firstModule (Additive.ofMul v)) := by
  obtain ⟨n,rfl⟩ := moveNormalizer.surjective n
  obtain ⟨v,rfl⟩ := firstEmbedding.surjective v
  have he : firstKernel.normalizerMonoidHom (moveNormalizer n) (firstEmbedding v) =
      firstEmbedding (W.normalizerMonoidHom n v) := by
    apply Subtype.ext
    change move n.val * move v.val * (move n.val)⁻¹ = move (n.val * v.val * n.val⁻¹)
    simp only [map_mul,map_inv]
  rw [he]
  change moduleEquiv (Additive.ofMul (firstEmbedding.symm (firstEmbedding _))) =
    cocodeRepresentation (normalizerProjection (moveNormalizer.symm (moveNormalizer n)))
      (moduleEquiv (Additive.ofMul (firstEmbedding.symm (firstEmbedding v))))
  rw [firstEmbedding.symm_apply_apply,firstEmbedding.symm_apply_apply,moveNormalizer.symm_apply_apply]
  exact moduleEquiv_equivariant n v

theorem first_mem : Janko4.a ∈ firstKernel := move_marker ▸ mem_map_of_mem _ marker.property

/-- The marker is literally a, rather than an unspecified fused involution. -/
@[expose] def firstMarker : firstKernel := ⟨Janko4.a,first_mem⟩

@[simp] theorem firstMarker_val : (firstMarker : Model) = Janko4.a := rfl

theorem firstMarker_coordinates : firstModule (Additive.ofMul firstMarker) = sextetVector standardSextet := by
  have he : firstMarker = firstEmbedding marker := Subtype.ext move_marker.symm
  rw [he]
  change moduleEquiv (Additive.ofMul (firstEmbedding.symm (firstEmbedding marker))) = _
  rw [firstEmbedding.symm_apply_apply,marker_coordinates]

/-- Native generation is transported by the same ambient conjugator as both markings. -/
theorem first_generate : centralizer Janko4.a ⊔ normalizer (firstKernel : Set Model) = ⊤ := by
  have hh := congrArg (Subgroup.map move.toMonoidHom) marker_generate
  rw [Subgroup.map_sup,map_top_of_surjective _ move.surjective,W.map_equiv_normalizer_eq move] at hh
  have hc : (centralizer (marker : Model)).map move.toMonoidHom = centralizer Janko4.a := by
    rw [Theory.GroupTheory.map_centralizer_equiv]
    rw [Set.image_singleton,move_marker]
  rwa [hc] at hh

/-- Native AS91 (4.8), for EVERY cubic quotient marking at the literal a. -/
theorem first_pointData
    (cubic : CubicAutomorphismQuotient (centralizer Janko4.a ⧸ core Janko4.a)) :
    ∃ data : PointData Janko4.a,
      data.cubic=cubic ∧ data.E=firstKernel ∧
      ∃ hm : data.M=normalizer (firstKernel : Set Model),
        (∀ x, firstProjection (MulEquiv.subgroupCongr hm (data.toddEquiv x))=x.right) ∧
        (∀ w : firstKernel, (data.toddEquiv (SemidirectProduct.inl
          (Multiplicative.ofAdd (firstModule (Additive.ofMul w))))).val=w.val) :=
  marked_pointData firstKernel firstProjection firstProjection_surjective firstProjection_ker
    firstModule firstModule_equivariant firstMarker standardSextet firstMarker_coordinates model_isTypeJ4 cubic

/-- The constructed native point group generates with C(a), before any local-data assumption. -/
theorem first_pointData_generation
    (cubic : CubicAutomorphismQuotient (centralizer Janko4.a ⧸ core Janko4.a)) :
    ∃ data : PointData Janko4.a,
      data.cubic=cubic ∧ data.E=firstKernel ∧
      data.M=normalizer (firstKernel : Set Model) ∧ centralizer Janko4.a ⊔ data.M = ⊤ := by
  obtain ⟨data,hc,hE,hm,_⟩ := first_pointData cubic
  exact ⟨data,hc,hE,hm,by rw [hm]; exact first_generate⟩

/-- The original full-H perfectness clause at the literal native a. -/
theorem first_fullCubic_perfect
    (cubic : CubicAutomorphismQuotient (centralizer Janko4.a ⧸ core Janko4.a))
    (X : Sylow 3 (CubicLift.subgroup cubic)) : Group.IsPerfect (fullCubicCentralizer cubic X) :=
  marked_fullCubicCentralizer_perfect firstKernel firstProjection firstProjection_surjective firstProjection_ker
    firstModule firstModule_equivariant firstMarker standardSextet firstMarker_coordinates model_isTypeJ4 cubic X

/-- The involutory splitting of the same native full cubic normalizer. -/
theorem first_fullCubic_split
    (cubic : CubicAutomorphismQuotient (centralizer Janko4.a ⧸ core Janko4.a))
    (X : Sylow 3 (CubicLift.subgroup cubic)) :
    ∃ v : fullCubicNormalizer cubic X, orderOf v=2 ∧
      v.val ∉ fullCubicCentralizer cubic X ∧
      (∀ x ∈ cubicSylowImage cubic X, v.val*x*v.val⁻¹=x⁻¹) ∧
      IsComplement' ((fullCubicCentralizer cubic X).subgroupOf (fullCubicNormalizer cubic X))
        (zpowers v) :=
  marked_fullCubicNormalizer_split firstKernel firstProjection firstProjection_surjective firstProjection_ker
    firstModule firstModule_equivariant firstMarker standardSextet firstMarker_coordinates model_isTypeJ4 cubic X

/-- Both original-H clauses for every compatible local-data package at the native a. -/
theorem first_cubicNormalizerData (data : SourceIncidence.LocalData model_isTypeJ4) :
    Nonempty (SourceComparison.CubicNormalizerData data) := by
  obtain ⟨v,hv,hout,_⟩ := first_fullCubic_split data.e data.X
  exact ⟨{
    perfect := first_fullCubic_perfect data.e data.X
    s := v.val
    s_mem := v.property
    s_sq := by
      have hh : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
      exact congrArg Subtype.val (by simpa only [pow_two] using hh)
    s_not_mem := hout }⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCocode
