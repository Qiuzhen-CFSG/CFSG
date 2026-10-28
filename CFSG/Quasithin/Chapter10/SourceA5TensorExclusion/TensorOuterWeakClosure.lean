module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOuterWeakClosure.ActorImage
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOuterWeakClosure.GeometryTransport
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorSingularLineFixed
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointPairs

/-!
# The outer-actor branch of tensor weak closure

An original corank-at-most-one actor in the Sylow subgroup has rank at
least three in the full tensor normalizer whenever the full module does
not normalize its conjugate. The proved singular-line argument makes the
actor fix an invariant coefficient line pointwise. The outer matrix
geometry then supplies a subspace with pointwise-kernel index at most four
and two nonsingular displacement vectors on distinct coefficient lines.

Global rank greater than three puts this subspace in the conjugate-module
normalizer, and its moved span lies in that module. The original
nonsingular-pair uniqueness theorem forces equality with the full module,
contradicting the assumed nonnormalization. This closes the outer branch
of Aschbacher–Smith 9.4.5, printed pp.736–737. Original point normality is
the independent earlier-source premise, retained for discharge using the
same generation-one hypothesis in the final assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.NaturalTensor
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The actual outer actor cannot occur in a nonnormalized conjugate module. -/
theorem tensor_outer_actor_false
    (hpoint : ∀ v : D.fullModule, ((m.sectionData.coordinates v).toAdd).det ≠ 0 →
      centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G))
    (hr : 3 < globalR D.fullModule) (g : G) {A : Subgroup G}
    (hAW : A ≤ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hcor : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hAT : A ≤ (T : Subgroup G))
    (hnot : ¬ D.fullModule ≤ normalizer
      (D.fullModule.map (MulAut.conj g).toMonoidHom : Set G))
    (houter : ¬ (A.subgroupOf D.maximalLocal).map m.maximalAction ≤ Binary.linearAction.range) :
    False := by
  let W := D.fullModule.map (MulAut.conj g).toMonoidHom
  let := m.fullModule_elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := offender_elementary_of_le hAW
  have hAM : A ≤ D.maximalLocal := hAT.trans (le_normalizer_componentOrbit L T)
  let f := m.maximalNormalizerAction.comp (inclusion hAM)
  let B := f.range
  have hrank : 3 ≤ rank B := by
    rw [m.normalizerActor_rank hAM]
    exact m.tensor_actor_rank_ge_three hr g hAW hcor hAT hnot
  have hB : IsElementaryTwo B := by
    refine ⟨?_,IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective⟩
    intro hb
    rw [hb,Representation.BinaryOffender.rank_bot] at hrank
    omega
  have hBo : ¬ B.map (linearNormalizer Binary.action).subtype ≤ actionImage Binary.action :=
    m.normalizerActor_outer hAM houter
  let d := Binary.normalizerSingularLineData f (T.isPGroup'.to_le hAT)
  have hfixed : ∀ h : B, ∀ c : Binary.F, h.val.val.val (c • d.vector) = c • d.vector := by
    intro h c
    rcases h with ⟨h,⟨a,rfl⟩⟩
    exact m.tensor_singular_line_fixed hr g hAW hcor hAM d a _ ⟨c,rfl⟩
  obtain ⟨U,K,hK,hKU,x,hx,y,hy,hxn,hyn,hxy⟩ :=
    Binary.outer_fixed_line_geometry B hB hrank hBo d.vector d.vector_ne_zero
      d.vector_singular hfixed
  have hUN := m.tensor_index_four_fixed_normalizes hr g hAW hcor hAM U K hK hKU
  have hSW := m.tensor_normalizerMovedSpace_le hAM hAW U hUN
  let S := m.tensorCoordinateSubgroup (Binary.normalizerMovedSpace B U)
  obtain ⟨p,hp⟩ := m.sectionData.onto (Multiplicative.ofAdd x)
  obtain ⟨q,hq⟩ := m.sectionData.onto (Multiplicative.ofAdd y)
  have hpx : (m.sectionData.coordinates p).toAdd = x := congrArg Multiplicative.toAdd hp
  have hqy : (m.sectionData.coordinates q).toAdd = y := congrArg Multiplicative.toAdd hq
  have hpS : (p : G) ∈ S := by
    apply (m.mem_tensorCoordinateSubgroup _ p).mpr
    rwa [hpx]
  have hqS : (q : G) ∈ S := by
    apply (m.mem_tensorCoordinateSubgroup _ q).mpr
    rwa [hqy]
  have hpdet : ((m.sectionData.coordinates p).toAdd).det ≠ 0 := by rwa [hpx]
  have hqdet : ((m.sectionData.coordinates q).toAdd).det ≠ 0 := by rwa [hqy]
  have hpq : (m.sectionData.coordinates q).toAdd ∉
      Submodule.span Binary.F ({(m.sectionData.coordinates p).toAdd} : Set Binary.V) := by
    rwa [hpx,hqy]
  have he := m.tensor_unique_conjugate_of_nonsingular_pair hpoint p q hpdet hqdet hpq
    (m.tensorCoordinateSubgroup_le _) hpS hqS g hSW
  apply hnot
  rw [he]
  exact D.fullModule.le_normalizer

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
