module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorFusionSource
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Normalizer
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLine
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerSingularity

/-!
The determinant distinguishes singular and nonsingular vectors in the original
field-four tensor coordinates. The full binary normalizer preserves this
distinction, so the proved full-module fusion theorem preserves it as well.
An involution with binary displacement rank at most two cannot have a nonzero
singular vector in its displacement space. Applied to the original singular
tensor line, this excludes the commutator configuration used in source 9.4.5.

Source: Aschbacher--Smith, 9.4.5, printed p.737.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

theorem maximalAction_det_zero_iff (h : D.maximalLocal) (a : D.fullModule) :
    (m.maximalAction h (m.sectionData.coordinates a).toAdd).det = 0 ↔
      ((m.sectionData.coordinates a).toAdd).det = 0 :=
  Binary.normalizer_det_zero_iff _ (m.maximalAction_mem_normalizer h) _

theorem singular_fusion (a b : D.fullModule) (hab : IsConj (a : G) (b : G)) :
    ((m.sectionData.coordinates a).toAdd).det = 0 ↔
      ((m.sectionData.coordinates b).toAdd).det = 0 := by
  obtain ⟨g,hg,hga⟩ := m.tensor_element_fusion a.property b.property hab
  let h : D.maximalLocal := ⟨g,hg⟩
  have he : D.fullModule.normalizerMonoidHom
      ⟨h,D.maximalLocal_normalizes_fullModule h.property⟩ a = b :=
    Subtype.ext hga
  have hc := m.maximalAction_coordinates h a
  rw [he] at hc
  rw [← hc]
  exact (m.maximalAction_det_zero_iff h a).symm

theorem tensorLine_not_mem_displacement (h : D.maximalLocal)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range ((m.maximalAction h).toLinearMap - LinearMap.id)) ≤ 2)
    (h2 : m.maximalAction h ^ 2 = 1) (s : m.tensorLine) (hs : s ≠ 1) :
    (m.sectionData.coordinates ⟨s,m.tensorLine_le_fullModule s.property⟩).toAdd ∉
      LinearMap.range ((m.maximalAction h).toLinearMap - LinearMap.id) := by
  apply Binary.low_rank_involution_singular_not_mem_displacement _
    (m.maximalAction_mem_normalizer h) hr h2 _ _ (m.tensorLine_singular s)
  intro hz
  apply hs
  apply Subtype.ext
  have hc : m.sectionData.coordinates ⟨s,m.tensorLine_le_fullModule s.property⟩ = 1 :=
    Multiplicative.toAdd.injective hz
  have he := m.coordinates_injective (hc.trans m.sectionData.coordinates.map_one.symm)
  exact congrArg (fun x : D.fullModule => (x : G)) he

theorem tensorLine_ne_commutator (h : D.maximalLocal)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range ((m.maximalAction h).toLinearMap - LinearMap.id)) ≤ 2)
    (h2 : m.maximalAction h ^ 2 = 1) (a : D.fullModule)
    (s : m.tensorLine) (hs : s ≠ 1) :
    ⁅(h : G),(a : G)⁆ ≠ (s : G) := by
  intro he
  apply m.tensorLine_not_mem_displacement h hr h2 s hs
  refine ⟨(m.sectionData.coordinates a).toAdd,?_⟩
  change m.maximalAction h (m.sectionData.coordinates a).toAdd -
    (m.sectionData.coordinates a).toAdd = _
  rw [m.maximalAction_coordinates]
  let b := D.fullModule.normalizerMonoidHom
    ⟨h,D.maximalLocal_normalizes_fullModule h.property⟩ a
  have hb : b * a⁻¹ = ⟨s,m.tensorLine_le_fullModule s.property⟩ := by
    apply Subtype.ext
    exact he
  have hcoord := congrArg (fun x : D.fullModule => (m.sectionData.coordinates x).toAdd) hb
  rw [map_mul,map_inv] at hcoord
  change (m.sectionData.coordinates b).toAdd + -(m.sectionData.coordinates a).toAdd = _ at hcoord
  simpa only [b, sub_eq_add_neg] using hcoord

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
