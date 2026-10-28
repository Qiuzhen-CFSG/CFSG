module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorSingularDisplacement
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorCorankPreparation
public import Theory.Representation.OrthogonalFourPlusMatrix.NearOffenderSwap

/-!
# A small singular commutator on a conjugate tensor hyperplane

Restrict an actor to a binary hyperplane. If its displacement there lies in
a subgroup of order at most four, rank-nullity bounds its total displacement
rank by three. The tensor normalizer excludes rank three, leaving rank at
most two. An involution of this rank cannot move a nonzero singular vector.

Conjugate the original hyperplane back to the full module and transport
singularity through the proved full-module fusion theorem. This makes the
literal commutator trivial, without assuming invariance of the hyperplane.
The result supplies the common singular-image step of the inner and outer
actor arguments in source 9.4.4--5.

Source: Aschbacher--Smith 9.4.4--5, printed pp.736--737.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

private theorem small_image_displacement_rank {B S : Subgroup G}
    (hBV : B ≤ D.fullModule) (hBcor : subgroupCorank D.fullModule B ≤ 1)
    (hSV : S ≤ D.fullModule) (hScard : Nat.card S ≤ 4)
    (c : D.maximalLocal) (hcomm : ∀ b ∈ B, ⁅(c : G),b⁆ ∈ S) :
    Module.finrank (ZMod 2)
      (LinearMap.range ((m.maximalAction c).toLinearMap - LinearMap.id)) ≤ 2 := by
  let := m.fullModule_elementary
  let U := m.sectionData.imageSpace B
  let X := m.sectionData.imageSpace S
  let δ := (m.maximalAction c).toLinearMap - LinearMap.id
  have hUdim : 7 ≤ Module.finrank (ZMod 2) U := by
    have hi := D.fullModule.relIndex_eq_two_pow_quotient_finrank B
    rw [←subgroupCorank_eq_quotient_finrank] at hi
    have hd := m.sectionData.imageSpace_codimension_of_index B hBV bot_le _ hi
    rw [Binary.finrank_binary] at hd
    change 7 ≤ Module.finrank (ZMod 2) (m.sectionData.imageSpace B)
    omega
  have hXdim : Module.finrank (ZMod 2) X ≤ 2 := by
    have hc := m.sectionData.imageSpace_card_eq_relIndex S hSV
    rw [Subgroup.relIndex_bot_left] at hc
    have hc' : Nat.card X ≤ 4 := hc.trans_le hScard
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc'
    have hh : 2 ^ Module.finrank (ZMod 2) X ≤ 2 ^ 2 := hc'
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  have hrange : (δ.domRestrict U).range ≤ X := by
    rintro _ ⟨u,rfl⟩
    obtain ⟨b,hb,hbe⟩ := (m.sectionData.mem_imageSpace_iff B u.val).mp u.property
    change δ u.val ∈ X
    rw [←hbe]
    change m.maximalAction c (m.sectionData.coordinates b).toAdd -
      (m.sectionData.coordinates b).toAdd ∈ X
    rw [m.maximalAction_coordinates]
    let b' := D.fullModule.normalizerMonoidHom
      ⟨c,D.maximalLocal_normalizes_fullModule c.property⟩ b
    apply (m.sectionData.mem_imageSpace_iff S _).mpr
    refine ⟨b' * b⁻¹,hcomm b hb,?_⟩
    rw [map_mul,map_inv]
    change (m.sectionData.coordinates b').toAdd + -(m.sectionData.coordinates b).toAdd = _
    simp only [b',sub_eq_add_neg]
  have hrank := Submodule.finrank_mono hrange
  have hkernel : Module.finrank (ZMod 2) (δ.domRestrict U).ker ≤
      Module.finrank (ZMod 2) δ.ker := by
    let f : (δ.domRestrict U).ker →ₗ[ZMod 2] δ.ker :=
      { toFun := fun x => ⟨x.val.val,x.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    apply LinearMap.finrank_le_finrank_of_injective (f := f)
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : δ.ker => (z : Binary.V)) h
  have hδ := δ.finrank_range_add_finrank_ker
  have hδU := (δ.domRestrict U).finrank_range_add_finrank_ker
  rw [Binary.finrank_binary] at hδ
  apply Binary.rank_le_two_of_rank_le_three _ (m.maximalAction_mem_normalizer c)
  change Module.finrank (ZMod 2) δ.range ≤ 3
  omega

/-- A small singular commutator image on a hyperplane of a conjugate tensor
module is trivial. The literal conjugation preserves singularity by fusion. -/
theorem tensor_commutator_eq_bot_of_singular_image (g : G) {A C S : Subgroup G}
    (hAW : A ≤ D.fullModule.map (MulAut.conj g).toMonoidHom)
    (hcor : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hCV : C ≤ D.fullModule)
    (hCN : C ≤ normalizer (D.fullModule.map (MulAut.conj g).toMonoidHom : Set G))
    (hSV : S ≤ D.fullModule) (hScard : Nat.card S ≤ 4)
    (hSsing : ∀ s : S,
      ((m.sectionData.coordinates ⟨s,hSV s.property⟩).toAdd).det = 0)
    (hcomm : ⁅C,A⁆ ≤ S) : ⁅C,A⁆ = ⊥ := by
  let := m.fullModule_elementary
  let E := MulAut.conj g
  let W := D.fullModule.map E.toMonoidHom
  let B := A.map E.symm.toMonoidHom
  let S₀ := (S ⊓ W).map E.symm.toMonoidHom
  have hWback : W.map E.symm.toMonoidHom = D.fullModule := by
    change (D.fullModule.map E.toMonoidHom).map E.symm.toMonoidHom = D.fullModule
    rw [map_map]
    have he : E.symm.toMonoidHom.comp E.toMonoidHom = MonoidHom.id G := by
      ext x
      exact E.symm_apply_apply x
    rw [he,map_id]
  have hBV : B ≤ D.fullModule := (map_mono hAW).trans_eq hWback
  have hScV : S₀ ≤ D.fullModule := (map_mono inf_le_right).trans_eq hWback
  have hScC : Nat.card S₀ ≤ 4 := by
    change Nat.card ((S ⊓ W).map E.symm.toMonoidHom) ≤ 4
    rw [card_map_of_injective E.symm.injective]
    exact (card_le_of_le inf_le_left).trans hScard
  have hBcor : subgroupCorank D.fullModule B ≤ 1 := by
    rw [←hWback]
    change Nat.log 2 ((A.map E.symm.toMonoidHom).relIndex (W.map E.symm.toMonoidHom)) ≤ 1
    rw [relIndex_map_map_of_injective _ _ E.symm.injective]
    exact hcor
  have hcommW : ⁅C,A⁆ ≤ W := (commutator_mono le_rfl hAW).trans
    (le_normalizer_iff_commutator_le_right.mp hCN)
  apply bot_unique
  apply commutator_le.mpr
  intro c hc a ha
  have hcN : E.symm c ∈ normalizer (D.fullModule : Set G) := by
    have hn := mem_map_of_mem E.symm.toMonoidHom (hCN hc)
    rw [map_equiv_normalizer_eq,hWback] at hn
    exact hn
  have hcM : E.symm c ∈ D.maximalLocal := by
    rwa [source_fullModule_normalizer D] at hcN
  let cM : D.maximalLocal := ⟨E.symm c,hcM⟩
  have hsc (b : G) (hb : b ∈ B) : ⁅(cM : G),b⁆ ∈ S₀ := by
    obtain ⟨a,ha,rfl⟩ := hb
    have hs : ⁅c,a⁆ ∈ S ⊓ W := ⟨hcomm (commutator_mem_commutator hc ha),
      hcommW (commutator_mem_commutator hc ha)⟩
    change ⁅E.symm c,E.symm a⁆ ∈ (S ⊓ W).map E.symm.toMonoidHom
    rw [←map_commutatorElement]
    exact mem_map_of_mem E.symm.toMonoidHom hs
  have hrank := m.small_image_displacement_rank hBV hBcor hScV hScC cM hsc
  have hc2 : cM ^ 2 = 1 := by
    apply Subtype.ext
    change (E.symm c) ^ 2 = 1
    rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian c (hCV hc),map_one]
  have hact2 : m.maximalAction cM ^ 2 = 1 := by rw [←map_pow,hc2,map_one]
  have hsS : ⁅c,a⁆ ∈ S := hcomm (commutator_mem_commutator hc ha)
  have hsW : ⁅c,a⁆ ∈ W := hcommW (commutator_mem_commutator hc ha)
  have hsV : E.symm ⁅c,a⁆ ∈ D.fullModule := hScV
    (mem_map_of_mem E.symm.toMonoidHom ⟨hsS,hsW⟩)
  let s : D.fullModule := ⟨⁅c,a⁆,hSV hsS⟩
  let s₀ : D.fullModule := ⟨E.symm ⁅c,a⁆,hsV⟩
  have hsing : ((m.sectionData.coordinates s₀).toAdd).det = 0 := by
    apply (m.singular_fusion s s₀ (isConj_iff.mpr ⟨g⁻¹,by change g⁻¹ * ⁅c,a⁆ * (g⁻¹)⁻¹ = (MulAut.conj g).symm ⁅c,a⁆; rw [inv_inv]; rfl⟩)).mp
    exact hSsing ⟨⁅c,a⁆,hsS⟩
  have hmem : (m.sectionData.coordinates s₀).toAdd ∈ LinearMap.range
      ((m.maximalAction cM).toLinearMap - LinearMap.id) := by
    let b : D.fullModule := ⟨E.symm a,hBV (mem_map_of_mem E.symm.toMonoidHom ha)⟩
    refine ⟨(m.sectionData.coordinates b).toAdd,?_⟩
    change m.maximalAction cM (m.sectionData.coordinates b).toAdd -
      (m.sectionData.coordinates b).toAdd = _
    rw [m.maximalAction_coordinates]
    let b' := D.fullModule.normalizerMonoidHom
      ⟨cM,D.maximalLocal_normalizes_fullModule cM.property⟩ b
    have hb : b' * b⁻¹ = s₀ := by
      apply Subtype.ext
      change ⁅E.symm c,E.symm a⁆ = E.symm ⁅c,a⁆
      exact (map_commutatorElement E.symm.toMonoidHom c a).symm
    have he := congrArg (fun x : D.fullModule => (m.sectionData.coordinates x).toAdd) hb
    rw [map_mul,map_inv] at he
    change (m.sectionData.coordinates b').toAdd + -(m.sectionData.coordinates b).toAdd = _ at he
    simpa only [b',sub_eq_add_neg] using he
  have hz : (m.sectionData.coordinates s₀).toAdd = 0 := by
    by_contra hn
    exact Binary.low_rank_involution_singular_not_mem_displacement _
      (m.maximalAction_mem_normalizer cM) hrank hact2 _ hn hsing hmem
  have hs01 : s₀ = 1 := m.coordinates_injective
    ((Multiplicative.toAdd.injective hz).trans m.sectionData.coordinates.map_one.symm)
  change ⁅c,a⁆ = 1
  apply E.symm.injective
  rw [map_one]
  exact congrArg (fun x : D.fullModule => (x : G)) hs01

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
