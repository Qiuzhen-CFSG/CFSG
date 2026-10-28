module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.DesignProjection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Residuals
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure
public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Native Mathieu partition-overlap quotient

The literal inverse image of the outer three-pair stabilizer under the native
design projection has the cubic scalar kernel and two independent intrinsic
three-point actions. A characteristic complement to the cubic kernel gives
the second action on three cosets; the published partition action gives the
first. Their product is surjective with kernel exactly the intrinsic
two-core, yielding the required `S₃ × S₃` quotient.

The conjugate and residual/Sylow forms below retain the actual lift under the
design projection and the source image hypothesis used by the actor catalogue.

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012, and H.12.1,
printed pp.393--394.
-/

open Subgroup
open scoped Pointwise
open Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open M22ValueBound.Concrete M22ValueBound.OddCoverLifting
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.PartitionOverlap

noncomputable abbrev projection : partitionPreimage →* outerSecond := localProjection outerSecond
noncomputable def innerPartition : Subgroup partitionPreimage := component.subgroupOf partitionPreimage
noncomputable def localCubic : Subgroup partitionPreimage := cubic.subgroupOf partitionPreimage
instance : innerPartition.Normal := inferInstanceAs (component.subgroupOf partitionPreimage).Normal
instance : localCubic.Normal := inferInstanceAs (cubic.subgroupOf partitionPreimage).Normal

theorem localCubic_card : Nat.card localCubic = 3 := by
  change Nat.card (cubic.subgroupOf partitionPreimage) = 3
  have hle : cubic ≤ partitionPreimage := by
    exact cubic_le_preimage outerSecond
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
  exact cubic_card

theorem localCubic_le_inner : localCubic ≤ innerPartition := fun _ hx => cubic_le_component hx

noncomputable def innerInclusion : innerPartition →* component :=
  { toFun := fun x => ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' := by intro x y; rfl }

noncomputable def innerProjectionRaw : innerPartition →* M22 :=
  componentProjection.comp (componentEquiv.toMonoidHom.comp innerInclusion)

noncomputable def innerProjection : innerPartition →* second :=
  innerProjectionRaw.codRestrict second (by
    intro x
    rw [← comap_outerSecond]
    change inclusion (innerProjectionRaw x) ∈ outerSecond
    change inclusion (componentProjection (componentEquiv ⟨x.val.val, x.property⟩)) ∈ outerSecond
    rw [← designProjection_component]
    exact x.val.property)

theorem innerProjection_surjective : Function.Surjective innerProjection := by
  intro y
  obtain ⟨x, hx⟩ := componentProjection_surjective y.val
  have hxP : componentInclusion x ∈ partitionPreimage := by
    change designProjection (componentInclusion x) ∈ outerSecond
    rw [designProjection_component, hx]
    exact y.property
  exact ⟨⟨⟨componentInclusion x, hxP⟩, x.property⟩, Subtype.ext hx⟩

theorem innerProjection_ker : innerProjection.ker = localCubic.subgroupOf innerPartition := by
  ext x
  rw [MonoidHom.mem_ker]
  change innerProjection x = 1 ↔ x.val.val ∈ cubic
  rw [Subtype.ext_iff]
  change innerProjectionRaw x = 1 ↔ x.val.val ∈ cubic
  dsimp [innerProjectionRaw, innerInclusion]
  change componentProjection (componentEquiv ⟨x.val.val, x.property⟩) = 1 ↔ x.val.val ∈ cubic
  rw [← MonoidHom.mem_ker, componentProjection_ker, cubic_eq_map_center]
  constructor
  · intro hx
    exact mem_map.mpr ⟨_, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    have he : y = componentEquiv ⟨x.val.val, x.property⟩ :=
      by
        apply componentEquiv.symm.injective
        apply Subtype.ext
        exact hxy
    exact he ▸ hy

theorem innerProjection_ker_central : innerProjection.ker ≤ center innerPartition := by
  rw [innerProjection_ker]
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Subtype.ext
  exact cubic_le_centralizer_component hx y.val.val y.property

theorem innerProjection_ker_card : Nat.card innerProjection.ker = 3 := by
  rw [innerProjection_ker, Nat.card_congr (subgroupOfEquivOfLe localCubic_le_inner).toEquiv,
    localCubic_card]

theorem innerPartition_card : Nat.card innerPartition = 1152 := by
  have h := innerProjection.ker.card_mul_index
  rw [index_ker, innerProjection.range_eq_top_of_surjective innerProjection_surjective,
    card_top, innerProjection_ker_card, PartitionStructure.second_card] at h
  exact h.symm

theorem partitionPreimage_card : Nat.card partitionPreimage = 2304 := by
  have h := projection.ker.card_mul_index
  have hk : projection.ker = localCubic := by
    change (localProjection outerSecond).ker = cubic.subgroupOf partitionPreimage
    rw [localProjection_ker]
    rfl
  rw [index_ker, projection.range_eq_top_of_surjective (localProjection_surjective _),
    card_top, hk, localCubic_card,
    PartitionStructure.outerSecond_card] at h
  exact h.symm

theorem innerPartition_index : innerPartition.index = 2 := by
  have h := innerPartition.card_mul_index
  rw [innerPartition_card, partitionPreimage_card] at h
  omega

noncomputable def pairMap : partitionPreimage →* Equiv.Perm (Fin 3) :=
  outerSecondQuotientEquiv.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 outerSecond)).comp projection)

theorem pairMap_surjective : Function.Surjective pairMap :=
  outerSecondQuotientEquiv.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (localProjection_surjective _))


theorem pairMap_inner (x : innerPartition) :
    pairMap x.val = secondQuotientEquiv (QuotientGroup.mk' (pCore 2 second)
      (innerProjection x)) := by
  have ho (z : outerSecond) :
      outerSecondQuotientEquiv (QuotientGroup.mk' (pCore 2 outerSecond) z) =
        (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe]
          using M22ValueBound.Concrete.hexadPartition_card)).permCongrHom
            (M22ValueBound.Concrete.PartitionStructure.outerPairAction z) := by
    rfl
  have hi (z : second) :
      secondQuotientEquiv (QuotientGroup.mk' (pCore 2 second) z) =
        (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe]
          using M22ValueBound.Concrete.hexadPartition_card)).permCongrHom
            (M22ValueBound.Concrete.PartitionStructure.innerPairAction z) := by
    rfl
  change outerSecondQuotientEquiv
      (QuotientGroup.mk' (pCore 2 outerSecond) (projection x.val)) =
    secondQuotientEquiv
      (QuotientGroup.mk' (pCore 2 second) (innerProjection x))
  rw [ho, hi]
  congr 1
  have hproj : (projection x.val : outerSecond) =
      ⟨M22ValueBound.Concrete.inclusion (innerProjection x), by
        exact (innerProjection x).property⟩ := by
    apply Subtype.ext
    change designProjection x.val.val =
      M22ValueBound.Concrete.inclusion (innerProjection x)
    rw [show x.val.val = componentInclusion
      (componentEquiv ⟨x.val.val, x.property⟩) from rfl,
      designProjection_component]
    rfl
  rw [hproj]
  rfl

theorem pairMap_cubic (x : partitionPreimage) (hx : x ∈ localCubic) : pairMap x = 1 := by
  have hp : projection x = 1 := by
    have hk : projection.ker = localCubic := by
      change (localProjection outerSecond).ker = cubic.subgroupOf partitionPreimage
      rw [localProjection_ker]
      rfl
    rw [← MonoidHom.mem_ker, hk]
    exact hx
  simp only [pairMap, MonoidHom.comp_apply, hp, map_one]

theorem exists_innerComplement :
    ∃ D : Subgroup innerPartition, D.Characteristic ∧ innerProjection.ker.IsComplement' D :=
  oddCentralSplitting_three innerPartition second innerProjection innerProjection_surjective
    innerProjection_ker_central (by rw [innerProjection_ker_card]; decide) secondQuotientEquiv

noncomputable def innerComplement : Subgroup innerPartition := Classical.choose exists_innerComplement
instance : innerComplement.Characteristic := (Classical.choose_spec exists_innerComplement).1

theorem innerComplement_isComplement : innerProjection.ker.IsComplement' innerComplement :=
  (Classical.choose_spec exists_innerComplement).2

noncomputable def complement : Subgroup partitionPreimage := innerComplement.map innerPartition.subtype
instance : complement.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  exact (show (⊤ : Subgroup partitionPreimage) ≤ normalizer (innerPartition : Set partitionPreimage) by
    rw [normalizer_eq_top]).trans
    (normalizer_le_normalizer_characteristic_image innerPartition innerComplement)

theorem complement_le_inner : complement ≤ innerPartition :=
  (map_le_range innerPartition.subtype innerComplement).trans_eq (range_subtype _)

theorem cubic_sup_complement : localCubic ⊔ complement = innerPartition := by
  have h := congrArg (Subgroup.map innerPartition.subtype) innerComplement_isComplement.sup_eq_top
  simpa only [innerProjection_ker, Subgroup.map_sup, map_subgroupOf_eq_of_le localCubic_le_inner,
    ← MonoidHom.range_eq_map, range_subtype, complement] using h

theorem cubic_disjoint_complement : Disjoint localCubic complement := by
  have h := Subgroup.disjoint_map innerPartition.subtype_injective innerComplement_isComplement.disjoint
  simpa only [innerProjection_ker, map_subgroupOf_eq_of_le localCubic_le_inner, complement] using h

theorem complement_card : Nat.card complement = 384 := by
  have h := innerComplement_isComplement.card_mul_card
  rw [innerProjection_ker_card, innerPartition_card] at h
  rw [complement, card_map_of_injective innerPartition.subtype_injective]
  omega

theorem pairMap_complement_surjective : Function.Surjective (pairMap.comp complement.subtype) := by
  intro y
  obtain ⟨z, hz⟩ := secondQuotientEquiv.surjective y
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (pCore 2 second) z
  obtain ⟨x, hx⟩ := innerProjection_surjective w
  have hp : pairMap x.val = y := by rw [pairMap_inner, hx, hw, hz]
  have hmem : x.val ∈ localCubic ⊔ complement := cubic_sup_complement.symm ▸ x.property
  obtain ⟨c, hc, d, hd, hcd⟩ := mem_sup_of_normal_left.mp hmem
  refine ⟨⟨d, hd⟩, ?_⟩
  change pairMap d = y
  rw [← hcd, map_mul, pairMap_cubic c hc, one_mul] at hp
  exact hp

theorem inner_sup_sylow (T : Sylow 2 partitionPreimage) :
    innerPartition ⊔ (T : Subgroup partitionPreimage) = ⊤ := by
  have hp : IsPGroup 2 (partitionPreimage ⧸ innerPartition) :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one, ← index_eq_card] using innerPartition_index)
  have hr : pResidual 2 partitionPreimage ≤ innerPartition := sInf_le ⟨inferInstance, hp⟩
  exact top_unique ((pResidual_sup_sylow_eq_top T).symm ▸ sup_le_sup_right hr _)

noncomputable def sylowComplement : Subgroup partitionPreimage :=
  complement ⊔ (default : Sylow 2 partitionPreimage)

theorem sylowComplement_isComplement : localCubic.IsComplement' sylowComplement := by
  apply complement_adjoin_sylow localCubic complement
    (by rw [localCubic_card]; decide) cubic_disjoint_complement
  rw [cubic_sup_complement, inner_sup_sylow]

theorem sylowComplement_core : sylowComplement.normalCore = complement := by
  apply le_antisymm
  · have hd : Disjoint sylowComplement.normalCore localCubic :=
      (sylowComplement_isComplement.disjoint.mono_right sylowComplement.normalCore_le).symm
    have hc : sylowComplement.normalCore ≤ centralizer (localCubic : Set partitionPreimage) :=
      commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
    intro x hx
    have he : x ∈ innerPartition := by
      change x.val ∈ component
      rw [← centralizer_scalar_eq_component]
      intro z hz
      have hz' : z = cubicScalar := hz
      subst z
      exact congrArg Subtype.val (hc hx ⟨cubicScalar, cubic_le_preimage outerSecond cubicScalar_mem_cubic⟩
        cubicScalar_mem_cubic)
    have hmem : x ∈ localCubic ⊔ complement := cubic_sup_complement.symm ▸ he
    obtain ⟨c, hcc, d, hdd, hcd⟩ := mem_sup_of_normal_left.mp hmem
    have hdH : d ∈ sylowComplement := (show complement ≤ sylowComplement from le_sup_left) hdd
    have hcdH : c * d ∈ sylowComplement :=
      sylowComplement.normalCore_le (hcd ▸ hx)
    have hcH : c ∈ sylowComplement := (sylowComplement.mul_mem_cancel_right hdH).mp
      hcdH
    have hc1 : c = 1 := sylowComplement_isComplement.disjoint.le_bot ⟨hcc, hcH⟩
    rw [← hcd, hc1, one_mul]
    exact hdd
  · exact normal_le_normalCore.mpr le_sup_left

noncomputable def cosetEquiv : (partitionPreimage ⧸ sylowComplement) ≃ Fin 3 :=
  (Finite.equivFin _).trans (finCongr (sylowComplement_isComplement.index_eq_card.trans localCubic_card))

noncomputable def cubicMap : partitionPreimage →* Equiv.Perm (Fin 3) :=
  cosetEquiv.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom partitionPreimage (partitionPreimage ⧸ sylowComplement))

theorem cubicMap_ker : cubicMap.ker = complement := by
  rw [cubicMap, MonoidHom.ker_comp_of_injective _ _ cosetEquiv.permCongrHom.injective,
    ← normalCore_eq_ker, sylowComplement_core]

theorem cubicMap_surjective : Function.Surjective cubicMap := by
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_card_eq
  have h := cubicMap.ker.card_mul_index
  have hk : Nat.card cubicMap.ker = 384 := by rw [cubicMap_ker, complement_card]
  rw [hk, partitionPreimage_card] at h
  have hr : cubicMap.ker.index = 6 := by omega
  have hrr : Nat.card cubicMap.range = 6 := by rw [← index_ker]; exact hr
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  exact hrr.trans hperm.symm

noncomputable def productMap : partitionPreimage →*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := cubicMap.prod pairMap

theorem productMap_surjective : Function.Surjective productMap := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := cubicMap_surjective a
  obtain ⟨d, hd⟩ := pairMap_complement_surjective (b * (pairMap x)⁻¹)
  have hd1 : cubicMap d.val = 1 := by
    rw [← MonoidHom.mem_ker, cubicMap_ker]
    exact d.property
  refine ⟨d.val * x, Prod.ext ?_ ?_⟩
  · change cubicMap (d.val * x) = a
    rw [map_mul, hd1, one_mul, hx]
  · change pairMap (d.val * x) = b
    rw [map_mul, show pairMap d.val = b * (pairMap x)⁻¹ from hd, inv_mul_cancel_right]


theorem productMap_ker_card : Nat.card productMap.ker = 64 := by
  have h := productMap.ker.card_mul_index
  rw [index_ker, productMap.range_eq_top_of_surjective productMap_surjective,
    card_top, Nat.card_prod, partitionPreimage_card] at h
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hperm] at h
  omega

private theorem pCore_perm_three : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  have h := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Equiv.Perm (Fin 3)))
    Function.surjective_id (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)
  exact h.symm.trans MonoidHom.ker_id

private theorem twoCore_le_ker (f : partitionPreimage →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f) : pCore 2 partitionPreimage ≤ f.ker := by
  have hn : ((pCore 2 partitionPreimage).map f).Normal :=
    (inferInstance : (pCore 2 partitionPreimage).Normal).map f hf
  have hle : (pCore 2 partitionPreimage).map f ≤ pCore 2 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨hn, pCore_isPGroup.map f⟩
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (pCore_perm_three ▸ hle))

theorem productMap_ker : productMap.ker = pCore 2 partitionPreimage := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, IsPGroup.of_card (n := 6) productMap_ker_card⟩
  · rw [productMap, MonoidHom.ker_prod]
    exact le_inf (twoCore_le_ker cubicMap cubicMap_surjective)
      (twoCore_le_ker pairMap pairMap_surjective)

noncomputable def quotientEquiv : coreQuotient partitionPreimage ≃*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  (QuotientGroup.quotientMulEquivOfEq productMap_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective productMap productMap_surjective)

theorem quotientEquiv_mk (x : partitionPreimage) :
    quotientEquiv (QuotientGroup.mk' (pCore 2 partitionPreimage) x) =
      (cubicMap x, pairMap x) := rfl

theorem cubicMap_injective_on_cubic : Function.Injective (cubicMap.comp localCubic.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← MonoidHom.comap_ker, cubicMap_ker]
  apply bot_unique
  intro x hx
  apply Subtype.ext
  exact cubic_disjoint_complement.le_bot ⟨x.property, hx⟩

theorem localCubic_map_pairMap : localCubic.map pairMap = ⊥ := by
  apply (Subgroup.map_eq_bot_iff _).mpr
  exact pairMap_cubic


theorem conjugate_preimage_eq (x : Model) :
    (outerSecond.map (MulAut.conj (designProjection x)).toMonoidHom).comap designProjection =
      partitionPreimage.map (MulAut.conj x).toMonoidHom := by
  have hcomp : designProjection.comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj (designProjection x)).toMonoidHom.comp designProjection := by
    ext y
    simp [MulAut.conj_apply]
  have hmap : (partitionPreimage.map (MulAut.conj x).toMonoidHom).map designProjection =
      outerSecond.map (MulAut.conj (designProjection x)).toMonoidHom := by
    change ((outerSecond.comap designProjection).map (MulAut.conj x).toMonoidHom).map designProjection = _
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_comap_eq_self_of_surjective designProjection_surjective]
  rw [← hmap, Subgroup.comap_map_eq]
  apply sup_eq_left.mpr
  have hc := map_mono (f := (MulAut.conj x).toMonoidHom)
    (cubic_le_preimage outerSecond)
  have hcc : cubic.map (MulAut.conj x).toMonoidHom = cubic := by
    simpa using (Subgroup.Normal.map_conj_eq (H := cubic) x)
  rw [hcc] at hc
  exact (designProjection_ker ▸ hc)


/-- The product quotient transports through an actual lift of a conjugate
partition stabilizer. -/
noncomputable def conjugateQuotientEquiv (x : Model) :
    coreQuotient (partitionPreimage.map (MulAut.conj x).toMonoidHom) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  let e := partitionPreimage.equivMapOfInjective
    (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
  exact (M22ValueBound.OddCoverLifting.pCoreQuotientEquiv e).symm.trans quotientEquiv

/-- The literal overlap quotient, including the residual/Sylow join used by
Lemma 14.4.12. The image hypothesis is retained as the source catalogue's
actual lifted partition position. -/
noncomputable def joinQuotientEquiv (S : Sylow 2 Model) (P₂ : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P₂) (x : Model)
    (hP : P₂.map designProjection =
      outerSecond.map (MulAut.conj (designProjection x)).toMonoidHom) :
    coreQuotient (twoResidual (pCore 3 Model) ⊔ twoResidual P₂ ⊔
      (S : Subgroup Model)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  have hres := residual_sup_sylow S P₂ hSP
  have hjoin : cubic ⊔ twoResidual P₂ ⊔ (S : Subgroup Model) =
      partitionPreimage.map (MulAut.conj x).toMonoidHom := by
    calc
      cubic ⊔ twoResidual P₂ ⊔ (S : Subgroup Model) =
          cubic ⊔ (twoResidual P₂ ⊔ (S : Subgroup Model)) := sup_assoc _ _ _
      _ = cubic ⊔ P₂ := by rw [hres]
      _ = partitionPreimage.map (MulAut.conj x).toMonoidHom := by
        rw [cubic_sup_eq_full_preimage, hP, conjugate_preimage_eq]
  rw [firstActor_eq_cubic, hjoin]
  exact conjugateQuotientEquiv x

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.PartitionOverlap
