module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.Cocode
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Generation
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.Recognition.JankoFour.ModelHypotheses
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Naturality
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Orbits

/-!
# The native cocode normalizer and its type-J4 marker

The full ambient normalizer of the literal max1 kernel is the certified
max1 subgroup. Transport of the actual kernel action therefore gives a
surjective M24 marking on this normalizer, with exactly the embedded kernel
and with the cocode action proved by Native.Cocode.

The standard sextet class selects an actual element of that kernel. The
certified two kernel orbits and the pair-class coordinate of the seed
exclude the second involution class. The remaining orbit supplies an
ambient conjugator to the literal generator a. Its type-J4 hypotheses
therefore follow from model_isTypeJ4 by this concrete conjugation.
No native simplicity or assumed local-data package is used.

Source: Aschbacher--Segev, The uniqueness of groups of type J4, Invent.
Math. 105 (1991), (4.8), pp.598--599, DOI 10.1007/BF01232280.
Native max1 words and fusion certificates retain their ATLAS attribution
in the imported model modules. SourceFusion.Orbits is used only for its
unconditional identity on the native sextet vectors.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCocode
open Janko4 Janko4.Cardinality Janko4.LocalStructure
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

abbrev M := max1Subgroup matrixA_mul_self matrixB_pow_four
abbrev K := localKernel matrixA_mul_self matrixB_pow_four
local instance : IsElementaryAbelian 2 K := localKernel_elementary _ _

def W : Subgroup Model := K.map M.subtype
instance W_elementary : IsElementaryAbelian 2 W := IsElementaryAbelian.map M.subtype

theorem W_normalizer : normalizer (W : Set Model) = M := by
  apply le_antisymm normalizer_embedded_localKernel_le_max1
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    K.le_normalizer_map M.subtype

noncomputable def kernelEmbedding : K ≃* W := K.equivMapOfInjective M.subtype M.subtype_injective

theorem kernelEmbedding_val (x : K) : (kernelEmbedding x).val = x.val.val := rfl

noncomputable def moduleEquiv : Additive W ≃ₗ[ZMod 2] Cocode :=
  ((kernelEmbedding.symm.toAdditive).toLinearEquiv (ZMod.map_smul _)).trans
    (cocodeEquiv matrixA_mul_self matrixB_pow_four).symm

noncomputable def normalizerProjection : normalizer (W : Set Model) →* M24 :=
  (projection matrixA_mul_self matrixB_pow_four).comp (MulEquiv.subgroupCongr W_normalizer).toMonoidHom

theorem normalizerProjection_surjective : Function.Surjective normalizerProjection :=
  (projection_surjective _ _).comp (MulEquiv.subgroupCongr W_normalizer).surjective

theorem normalizerProjection_ker :
    normalizerProjection.ker = W.subgroupOf (normalizer (W : Set Model)) := by
  ext n
  change projection matrixA_mul_self matrixB_pow_four
    (MulEquiv.subgroupCongr W_normalizer n) = 1 ↔ n.val ∈ W
  rw [←MonoidHom.mem_ker,projection_ker]
  constructor
  · intro hn
    exact ⟨_,hn,rfl⟩
  · rintro ⟨x,hx,he⟩
    have he' : x = MulEquiv.subgroupCongr W_normalizer n := Subtype.ext he
    rwa [←he']

theorem moduleEquiv_equivariant (n : normalizer (W : Set Model)) (v : W) :
    moduleEquiv (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (normalizerProjection n) (moduleEquiv (Additive.ofMul v)) := by
  let nM := MulEquiv.subgroupCongr W_normalizer n
  let w := kernelEmbedding.symm v
  have he : kernelEmbedding.symm (W.normalizerMonoidHom n v) = MulAut.conjNormal nM w := by
    apply kernelEmbedding.injective
    apply Subtype.ext
    change _ = (n.val * w.val.val * n.val⁻¹)
    rw [show w.val.val = v.val from congrArg Subtype.val (kernelEmbedding.apply_symm_apply v)]
    exact congrArg Subtype.val (kernelEmbedding.apply_symm_apply _)
  have hh := cocodeEquiv_equivariant matrixA_mul_self matrixB_pow_four nM
    ((cocodeEquiv matrixA_mul_self matrixB_pow_four).symm (Additive.ofMul w))
  rw [LinearEquiv.apply_symm_apply] at hh
  apply (cocodeEquiv matrixA_mul_self matrixB_pow_four).injective
  change cocodeEquiv matrixA_mul_self matrixB_pow_four
    ((cocodeEquiv matrixA_mul_self matrixB_pow_four).symm
      (Additive.ofMul (kernelEmbedding.symm (W.normalizerMonoidHom n v)))) = _
  rw [LinearEquiv.apply_symm_apply,he]
  exact hh.symm

noncomputable def marker : W :=
  kernelEmbedding ((cocodeEquiv matrixA_mul_self matrixB_pow_four (sextetVector standardSextet)).toMul)

theorem marker_coordinates : moduleEquiv (Additive.ofMul marker) = sextetVector standardSextet := by
  change (cocodeEquiv matrixA_mul_self matrixB_pow_four).symm
    (Additive.ofMul (kernelEmbedding.symm (kernelEmbedding _))) = _
  rw [kernelEmbedding.symm_apply_apply]
  exact LinearEquiv.symm_apply_apply _ _

private theorem marker_ne_one : marker ≠ 1 := by
  intro he
  have hh := marker_coordinates
  rw [he,show Additive.ofMul (1 : W) = 0 from rfl,map_zero] at hh
  exact sextetVector_ne_zero standardSextet hh.symm

/-- The native sextet element lies in the local orbit of the certified pair marker. -/
theorem marker_local_conjugator : ∃ g : M,
    (Simplicity.Max1Fusion.kernelPair matrixA_mul_self matrixB_pow_four : Model) =
      g.val * marker.val * g.val⁻¹ := by
  let w := kernelEmbedding.symm marker
  have hw : w.val ≠ 1 := by
    intro he
    apply marker_ne_one
    have hw1 : w = 1 := Subtype.ext he
    have hh := congrArg kernelEmbedding hw1
    change kernelEmbedding (kernelEmbedding.symm marker) = kernelEmbedding 1 at hh
    simpa only [map_one,kernelEmbedding.apply_symm_apply] using hh
  obtain ⟨g,hg | hg⟩ := Simplicity.Max1Fusion.kernel_nonidentity_orbits
    matrixA_mul_self matrixB_pow_four w.val w.property hw
  · have he : MulAut.conjNormal g w =
        (⟨localKernelSeed matrixA_mul_self matrixB_pow_four, localKernelSeed_mem _ _⟩ : K) :=
      Subtype.ext hg.symm
    have hh := cocodeEquiv_equivariant matrixA_mul_self matrixB_pow_four g
      (sextetVector standardSextet)
    have hcoords : (cocodeEquiv matrixA_mul_self matrixB_pow_four (sextetVector standardSextet)).toMul = w :=
      (kernelEmbedding.symm_apply_apply _).symm
    have hs : cocodeEquiv matrixA_mul_self matrixB_pow_four (pairVector ⟨{1,14},by decide⟩) =
        Additive.ofMul (⟨localKernelSeed matrixA_mul_self matrixB_pow_four, localKernelSeed_mem _ _⟩ : K) :=
      congrArg Additive.ofMul (Subtype.ext (cocodeEquiv_seed _ _))
    rw [hcoords,he,←hs] at hh
    have hv := (cocodeEquiv matrixA_mul_self matrixB_pow_four).injective hh
    rw [SourceFusion.sextet_vector_action] at hv
    exact (pairVector_ne_sextetVector _ _ hv.symm).elim
  · have hg' : (Simplicity.Max1Fusion.kernelPair matrixA_mul_self matrixB_pow_four : Model) =
        (g : Model) * (marker : Model) * (g : Model)⁻¹ := by
      have hh := congrArg M.subtype hg
      have hwv : w.val.val = marker.val := by
        have he := congrArg (fun x : W => x.val) (kernelEmbedding.apply_symm_apply marker)
        rw [kernelEmbedding_val] at he
        exact he
      change (Simplicity.Max1Fusion.kernelPair matrixA_mul_self matrixB_pow_four : Model) =
        g.val * w.val.val * g.val⁻¹ at hh
      rwa [hwv] at hh
    exact ⟨g,hg'⟩

/-- The concrete cocode marker is conjugate to the literal first matrix generator. -/
theorem marker_isConj : IsConj Janko4.a (marker : Model) := by
  obtain ⟨g,hg⟩ := marker_local_conjugator
  obtain ⟨k,hk⟩ := Simplicity.Max1Fusion.pair_fuses_first matrixA_mul_self matrixB_pow_four
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨k*g.val,?_⟩
  calc
    (k*g.val) * marker.val * (k*g.val)⁻¹ = k * (g.val * marker.val * g.val⁻¹) * k⁻¹ := by group
    _ = Janko4.a := by rw [←hg]; exact hk.symm

/-- The actual native point group and marker centralizer generate the full matrix model. -/
theorem marker_generate : centralizer (marker : Model) ⊔ normalizer (W : Set Model) = ⊤ := by
  rw [W_normalizer]
  obtain ⟨g,hg⟩ := marker_local_conjugator
  let c := MulAut.conj g.val
  have hM : M.map c.toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer g.property)
  have hC : (centralizer (marker : Model)).map c.toMonoidHom = Janko4.Max1AmalgamRigidity.C := by
    rw [Theory.GroupTheory.map_centralizer_equiv]
    rw [Set.image_singleton]
    change Subgroup.centralizer ({g.val * marker.val * g.val⁻¹} : Set Model) = _
    rw [←hg]
  apply (map_injective (f := c.toMonoidHom) c.injective)
  rw [Subgroup.map_sup,hC,hM,map_top_of_surjective _ c.surjective]
  exact Janko4.AdequateLocal.centralizer_sup_max1_eq_top

/-- Native type-J4 hypotheses at the actual marked cocode element. -/
theorem marker_isTypeJ4 : IsTypeJ4 (marker : Model) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp marker_isConj
  simpa only [MulAut.conj_apply,hg] using type_map model_isTypeJ4 (MulAut.conj g)

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeCocode
