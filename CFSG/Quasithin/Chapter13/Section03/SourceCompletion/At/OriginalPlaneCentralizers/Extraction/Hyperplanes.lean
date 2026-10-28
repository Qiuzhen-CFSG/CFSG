module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.Hyperplanes
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Source


/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.Extraction.Hyperplanes`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open UnitaryGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

omit [Finite G] in
private lemma marked_dimension (d : MarkedPlane V) : finrank K (Additive V) = 6 := by
  rw [d.coordinates.finrank_eq]
  simp [W]

private lemma marked_corank (d : MarkedPlane V) (U : Subgroup G) :
    finrank K (pointCoordinateSubspace d.coordinates U) + subgroupCorank V U =
      finrank K W := by
  have hd := (d.coordinates.submoduleMap (ambientSpace (V := V) U)).finrank_eq
  have hspace : (ambientSpace (V := V) U).map d.coordinates.toLinearMap =
      pointCoordinateSubspace d.coordinates U := by
    ext w
    obtain ⟨v,rfl⟩ := d.coordinates.surjective w
    rw [mem_pointCoordinateSubspace]
    constructor
    · rintro ⟨z,hz,hzv⟩
      have he : z = v := d.coordinates.injective hzv
      subst z
      exact hz
    · intro hv
      exact ⟨v,hv,rfl⟩
  rw [hspace] at hd
  rw [← hd, ← d.coordinates.finrank_eq]
  exact ambientSpace_finrank_add_corank U

private lemma hyperplane_nontrivial (d : MarkedPlane V) (U : Subgroup G)
    (hu : subgroupCorank V U = 1) : U ≠ ⊥ := by
  intro hb
  rw [hb, Section06.corank_bot, marked_dimension d] at hu
  omega

lemma Context.hyperplane_local_centralizer (s : Context T L V) (d : MarkedPlane V)
    (U : Subgroup G) (hUV : U ≤ V) (hu : subgroupCorank V U = 1) :
    normalizer (L : Set G) ⊓ centralizer (U : Set G) = centralizer (V : Set G) := by
  have he := s.earlier_geometry.1
  have hn := he.localCentralizer_le_normalizer (hyperplane_nontrivial d U hu) hUV
  apply le_antisymm
  · intro x hx
    let n : normalizer (V : Set G) := ⟨x,hn hx⟩
    let a := V.normalizerMonoidHom.rangeRestrict n
    have hg : d.chart a = 1 := by
      apply pointwise_hyperplane_trivial (pointCoordinateSubspace d.coordinates U)
        (hu ▸ marked_corank d U)
      intro w hw
      obtain ⟨v,rfl⟩ := d.coordinates.surjective w
      rw [← d.equivariant]
      apply congrArg d.coordinates
      apply Additive.toMul.injective
      apply Subtype.ext
      have hv := (mem_pointCoordinateSubspace d.coordinates U v).mp hw
      change x * v.toMul.val * x⁻¹ = v.toMul.val
      rw [← mem_centralizer_iff.mp hx.2 _ hv, mul_inv_cancel_right]
    intro v hv
    let w : Additive V := Additive.ofMul ⟨v,hv⟩
    have ha : automizerRepresentation V a w = w := by
      apply d.coordinates.injective
      rw [d.equivariant, hg, map_one, Module.End.one_apply]
    have hc : x * v * x⁻¹ = v := congrArg (fun z : Additive V => z.toMul.val) ha
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  · exact le_inf he.centralizer_le (Subgroup.centralizer_le hUV)

lemma Context.hyperplane_transitive (s : Context T L V) (d : MarkedPlane V)
    (U U' : Subgroup G) (hUV : U ≤ V) (hU'V : U' ≤ V)
    (hu : subgroupCorank V U = 1) (hu' : subgroupCorank V U' = 1) :
    ∃ n : normalizer (V : Set G), n.val ∈ L ∧
      U.map (MulAut.conj n.val).toMonoidHom = U' := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect s.maximal.1
  obtain ⟨g,hg⟩ := derived_hyperplane_transitive
    (pointCoordinateSubspace d.coordinates U) (pointCoordinateSubspace d.coordinates U')
    (hu ▸ marked_corank d U) (hu' ▸ marked_corank d U')
  have hi : g.val ∈ (inducedAutomizer V L).map d.chart :=
    (component_actor_image s.chosen.normalizes s.actor d.chart d.coordinates d.equivariant).symm ▸
      g.property
  obtain ⟨a,⟨n,hnL,rfl⟩,hn⟩ := hi
  refine ⟨n,hnL,?_⟩
  have hle : U' ≤ U.map (MulAut.conj n.val).toMonoidHom := by
    have hh := pointCoordinateSubspace_map_actor U d.chart d.coordinates d.equivariant n
    rw [hn,hg] at hh
    intro x hx
    exact (mem_pointCoordinateSubspace d.coordinates _ (Additive.ofMul ⟨x,hU'V hx⟩)).mp
      (hh ((mem_pointCoordinateSubspace d.coordinates U' _).mpr hx))
  apply (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective (MulAut.conj n.val).injective,
    ← card_pointCoordinateSubspace d.coordinates U hUV,
    ← card_pointCoordinateSubspace d.coordinates U' hU'V]
  have hdu := marked_corank d U
  have hdu' := marked_corank d U'
  have hh : finrank K (pointCoordinateSubspace d.coordinates U) =
    finrank K (pointCoordinateSubspace d.coordinates U') := by omega
  rw [Module.natCard_eq_pow_finrank (K := K) (V := pointCoordinateSubspace d.coordinates U),
    Module.natCard_eq_pow_finrank (K := K) (V := pointCoordinateSubspace d.coordinates U'), hh]

lemma Context.hyperplane_centralizer (s : Context T L V) (d : MarkedPlane V)
    (U : Subgroup G) (hUV : U ≤ V) (hu : subgroupCorank V U = 1) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have he := s.earlier_geometry.1
  let τ := (automizerRepresentation V).comp
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion he.sylow_le_normalizer))
  let : Nontrivial (Additive V) := Module.nontrivial_of_finrank_pos
    (R := K) (M := Additive V) (by rw [marked_dimension d]; decide)
  obtain ⟨P,hP,hinv⟩ := Representation.exists_invariant_binary_hyperplane τ T.isPGroup'
  let U0 : Subgroup G := ambientGroup P
  have h0V : U0 ≤ V := map_subtype_le _
  have h0 : subgroupCorank V U0 = 1 := by
    have hh := ambientSpace_finrank_add_corank (V := V) U0
    rw [show ambientSpace (V := V) U0 = P from ambientSpace_ambientGroup P] at hh
    omega
  have hnormal : (U0.subgroupOf (T : Subgroup G)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (h0V.trans he.le_sylow)).mpr
    apply le_normalizer_iff.mpr
    intro t ht x hx
    obtain ⟨v,hv,rfl⟩ := hx
    refine ⟨(V.normalizerMonoidHom ⟨t,he.sylow_le_normalizer ht⟩) v, ?_, rfl⟩
    exact hinv ⟨t,ht⟩ (Additive.ofMul v) hv
  have hodd : Section06.oddCentralizerCondition (normalizer (L : Set G)) V U0 := by
    rw [Section06.oddCentralizerCondition, s.hyperplane_local_centralizer d U0 h0V h0]
    exact (map_subtype_le _).trans (le_inf he.centralizer_le le_rfl)
  have hc := Section06.InvariantSubspaces.centralizer_le_of_normal_in_sylow_knownSimple
    he (hyperplane_nontrivial d U0 h0) h0V hodd hnormal
  obtain ⟨n,hnL,hn⟩ := s.hyperplane_transitive d U0 U h0V hUV h0 hu
  rw [← hn]
  have hh := map_mono (f := (MulAut.conj n.val).toMonoidHom) hc
  rw [Theory.GroupTheory.map_centralizer_equiv] at hh
  have hnM : n.val ∈ normalizer (L : Set G) := L.le_normalizer hnL
  have hMM : (normalizer (L : Set G)).map (MulAut.conj n.val).toMonoidHom =
      normalizer (L : Set G) := mem_normalizer_iff_map_conj_eq.mp ((normalizer (L : Set G)).le_normalizer hnM)
  simpa only [hMM, Subgroup.coe_map, MulEquiv.coe_toMonoidHom] using hh

lemma MarkedPlane.one_lt_localM (d : MarkedPlane V) : 1 < localM V := by
  have hf : Function.Injective d.chart := by
    intro a b hab
    apply automizerRepresentation_injective V
    apply LinearMap.ext
    intro v
    apply d.coordinates.injective
    rw [d.equivariant,d.equivariant,hab]
  apply Nat.lt_of_succ_le
  apply le_csInf ⟨_,Set.mem_insert _ _⟩
  rintro n (rfl | ⟨a,ha,rfl⟩)
  · rw [marked_dimension d]
    decide
  · have hag : orderOf (d.chart a) = 2 := (orderOf_injective d.chart hf a).trans ha
    have hb := Atlas.G2.Natural.InvolutionRank.two_le_operatorFixedCodim_of_involution
      (d.chart a) (by intro h; simp [h] at hag)
      (by have hh := pow_orderOf_eq_one (d.chart a); rwa [hag,pow_two] at hh)
    have hcoord := Representation.BinaryOffender.NaturalTensor.operatorFixedCodim_eq_of_equiv
      (Atlas.G2.Natural.action K (d.chart a)) (rho (d.chart a))
      (Atlas.G2.Restricted.NaturalCoordinates.equiv K)
      (fun v => LinearMap.congr_fun
        ((Atlas.G2.Restricted.NaturalCoordinates.repEquiv K).isIntertwining' (d.chart a)) v)
    have hmark := Representation.BinaryOffender.NaturalTensor.operatorFixedCodim_eq_of_equiv
      (automizerRepresentation V a) (rho (d.chart a)) d.coordinates (d.equivariant a)
    rw [hcoord,← hmark] at hb
    simpa only [Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank,
      Representation.BinaryOffender.NaturalTensor.operatorFixedCodim, Module.End.one_eq_id] using hb

lemma Context.one_lt_globalS (s : Context T L V) (d : MarkedPlane V) :
    (1 : ℕ∞) < globalS V := by
  have he := s.earlier_geometry.1
  have hr := one_lt_globalR_of_hyperplane_centralizers V (by
    intro U hUV hu
    exact (he.centralizer_le_iff (hyperplane_nontrivial d U hu) hUV).mp
      (s.hyperplane_centralizer d U hUV hu))
  exact lt_min hr (by exact_mod_cast d.one_lt_localM)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
