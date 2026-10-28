module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorSingularLineFixed.Normalization
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterWeakClosureGeometry
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Outer matrix geometry in the original tensor module

Pulling an index-at-most-four subgroup back through the actual actor image
gives corank at most three in a conjugate module. The global weak-closure
bound then makes the corresponding tensor-coordinate subgroup normalize
that conjugate module.

When the actor lies in this conjugate module, every commutator with the
coordinate subgroup lies there too. Equivariance identifies these actual
commutators with the generators of the binary matrix displacement span;
bijective coordinates recover a representative for every vector in that span.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 9.4.5, printed pp.736–737, the passage from the small action quotient
on `UN` to `UN ≤ Mᵍ` and `[A,UN] ≤ Vᵍ`.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

public noncomputable section

/-- The index-four fixed subgroup makes the literal coordinate subgroup
normalize the conjugate module by the global-rank criterion. -/
theorem tensor_index_four_fixed_normalizes (hr : 3 < globalR D.fullModule)
    (g : G) {A : Subgroup G}
    (hAW : A ≤ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hcor : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hAM : A ≤ D.maximalLocal) (U : Submodule (ZMod 2) Binary.V)
    (K : Subgroup (m.maximalNormalizerAction.comp (inclusion hAM)).range)
    (hK : K.index ≤ 4)
    (hfix : ∀ h ∈ K, ∀ v ∈ U, h.val.val.val v = v) :
    m.tensorCoordinateSubgroup U ≤ normalizer
      (D.fullModule.map (MulAut.conj g).toMonoidHom : Set G) := by
  let f := m.maximalNormalizerAction.comp (inclusion hAM)
  let Q := K.comap f.rangeRestrict
  let P := Q.map A.subtype
  let W := D.fullModule.map (MulAut.conj g).toMonoidHom
  let := m.fullModule_elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hPA : P ≤ A := map_subtype_le _
  have hi : P.relIndex A ≤ 4 := by
    change (P.subgroupOf A).index ≤ 4
    rw [show P.subgroupOf A = Q from
      comap_map_eq_self_of_injective A.subtype_injective Q]
    change (K.comap f.rangeRestrict).index ≤ 4
    rw [K.index_comap_of_surjective f.rangeRestrict_surjective]
    exact hK
  have hcA : subgroupCorank A P ≤ 2 := by
    change Nat.log 2 (P.relIndex A) ≤ 2
    exact (Nat.log_mono_right hi).trans (by decide)
  have hcW : subgroupCorank W P ≤ 3 := by
    rw [offender_corank_add hPA hAW]
    omega
  have hrW : 3 < globalR W := by
    rw [globalR_map_equiv]
    exact hr
  have hCN : centralizer (P : Set G) ≤ normalizer (W : Set G) :=
    centralizer_le_normalizer_of_corank_lt_globalR (hPA.trans hAW)
      ((show (subgroupCorank W P : ℕ∞) ≤ 3 by exact_mod_cast hcW).trans_lt hrW)
  apply le_trans (le_centralizer_iff.mp ?_) hCN
  rintro a ⟨b,hb,rfl⟩
  apply m.tensorCoordinateSubgroup_fixed U ⟨b,hAM b.property⟩
  intro v hv
  have hh := hfix (f.rangeRestrict b) hb v hv
  change normalizerRepresentation Binary.action
    (m.maximalNormalizerAction ⟨b,hAM b.property⟩) v = v at hh
  rwa [m.maximalNormalizerAction_apply] at hh

/-- The actual displacement span lifts into the subgroup containing the actor. -/
theorem tensor_normalizerMovedSpace_le {A W : Subgroup G}
    (hAM : A ≤ D.maximalLocal) (hAW : A ≤ W)
    (U : Submodule (ZMod 2) Binary.V)
    (hUN : m.tensorCoordinateSubgroup U ≤ normalizer (W : Set G)) :
    m.tensorCoordinateSubgroup
      (Binary.normalizerMovedSpace (m.maximalNormalizerAction.comp (inclusion hAM)).range U) ≤ W := by
  let f := m.maximalNormalizerAction.comp (inclusion hAM)
  have hmove : Binary.normalizerMovedSpace f.range U ≤ m.sectionData.imageSpace W := by
    apply Submodule.span_le.mpr
    rintro z ⟨h,v,hv,rfl⟩
    rcases h with ⟨h,⟨a,rfl⟩⟩
    obtain ⟨u,hu⟩ := m.sectionData.onto (Multiplicative.ofAdd v)
    have huv : (m.sectionData.coordinates u).toAdd = v := congrArg Multiplicative.toAdd hu
    have huU : (u : G) ∈ m.tensorCoordinateSubgroup U :=
      (m.mem_tensorCoordinateSubgroup U u).mpr (huv ▸ hv)
    let aM : D.maximalLocal := ⟨a,hAM a.property⟩
    let u' := D.fullModule.normalizerMonoidHom
      ⟨aM,D.maximalLocal_normalizes_fullModule aM.property⟩ u
    have hwW : ((u' * u⁻¹ : D.fullModule) : G) ∈ W := by
      change ⁅(a : G),(u : G)⁆ ∈ W
      exact (le_normalizer_iff_commutator_le_left.mp hUN)
        (commutator_mem_commutator (hAW a.property) huU)
    apply (m.sectionData.mem_imageSpace_iff W _).mpr
    refine ⟨u' * u⁻¹,hwW,?_⟩
    rw [map_mul,map_inv]
    change (m.sectionData.coordinates u').toAdd + -(m.sectionData.coordinates u).toAdd = _
    have hcoord := m.maximalNormalizerAction_coordinates aM u
    change normalizerRepresentation Binary.action (m.maximalNormalizerAction aM)
      (m.sectionData.coordinates u).toAdd = (m.sectionData.coordinates u').toAdd at hcoord
    rw [←hcoord,huv]
    simp only [sub_eq_add_neg]
    rfl
  intro z hz
  let zV : D.fullModule := ⟨z,m.tensorCoordinateSubgroup_le _ hz⟩
  have hzm := (m.mem_tensorCoordinateSubgroup
    (Binary.normalizerMovedSpace f.range U) zV).mp hz
  obtain ⟨w,hw,hcoord⟩ :=
    (m.sectionData.mem_imageSpace_iff W _).mp (hmove hzm)
  have hwz : w = zV := m.coordinates_injective (Multiplicative.toAdd.injective hcoord)
  change (zV : G) ∈ W
  rw [←hwz]
  exact hw

end
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
