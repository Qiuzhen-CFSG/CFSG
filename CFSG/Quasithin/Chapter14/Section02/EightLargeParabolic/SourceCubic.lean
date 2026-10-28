module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRankOne
public import Theory.GroupTheory.PRegularLift
public import Theory.SpecificGroups.PSL2.RootSemilinearFixedBound

/-!
# The actual cubic extension of both original endpoints

The exact two-core kernel gives an order-three pure field lift. An inner
conjugation aligns it with the original Sylow, placing the same cubic subgroup
in M intersect Mc. It supplements both original endpoints and retains the
whole odd Borel factor. All inputs are original Chapter 14 source data.

Source: Aschbacher--Smith 14.2.18, printed p.987.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCubic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

private theorem first_residual : residual H = H := by
  rw [residual, SourcePerfect.first_twoResidual_eq_top hG T hempty hM hu hmany hcard e H hH eR,
    ← MonoidHom.range_eq_map, range_subtype]

private theorem field_witness
    (hn : (SourceRankOne.fieldAction hG T hempty hM hu hmany hcard e H hH eR).range ≠ ⊥) :
    ∃ (σ : Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) (x : Mc),
      orderOf σ = 3 ∧
      SourceRankOne.rankOneAction hG T hempty hM hu hmany hcard e H hH eR x = Theory.PSL2.fieldAut σ ∧
      orderOf (SourceRankOne.rankOneAction hG T hempty hM hu hmany hcard e H hH eR x) = 3 := by
  have hc : Nat.card (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) = 3 :=
    GaloisField.card_ringAut 2 3 (by decide)
  let : IsCyclic (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) :=
    isCyclic_of_prime_card hc
  obtain ⟨σ,hσ⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3)
  rw [hc] at hσ
  have hi : Theory.PSL2.inner (Theory.PSL2.BinaryField 3) ≤
      (SourceRankOne.rankOneAction hG T hempty hM hu hmany hcard e H hH eR).range := by
    rw [←SourceRankOne.first_image hG T hempty hM hu hmany hcard e H hH eR]
    exact Subgroup.map_le_range _ _
  obtain ⟨x,hx⟩ := Theory.PSL2.eight_action_field_lift _ hi hn σ
  exact ⟨σ,x,hσ,hx,by rw [hx,Theory.PSL2.orderOf_fieldAut,hσ]⟩

/-- A pure cubic coefficient automorphism has an actual order-three lift in Mc. -/
theorem cubic_field_lift (hne : Mc ≠ H) :
    ∃ (σ : Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) (x : Mc),
      orderOf σ = 3 ∧ orderOf x = 3 ∧
      SourceRankOne.rankOneAction hG T hempty hM hu hmany hcard e H hH eR x = Theory.PSL2.fieldAut σ := by
  let a := SourceRankOne.rankOneAction hG T hempty hM hu hmany hcard e H hH eR
  have hn : (SourceRankOne.fieldAction hG T hempty hM hu hmany hcard e H hH eR).range ≠ ⊥ := by
    rw [SourceRankOne.field_range_eq_top hG T hempty hM hu hmany hcard e H hH eR hne]
    have hc : Nat.card (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) = 3 :=
      GaloisField.card_ringAut 2 3 (by decide)
    let : Finite (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) :=
      Nat.finite_of_card_ne_zero (by omega)
    have : Nontrivial (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact top_ne_bot
  obtain ⟨σ,x,hσ,hx,ho⟩ :=
    field_witness hG T hempty hM hu hmany hcard e H hH eR hn
  let v : a.range := ⟨a x,⟨x,rfl⟩⟩
  have hv : orderOf v = 3 := (Subgroup.orderOf_coe v).symm.trans ho
  obtain ⟨y,hy,hey⟩ := a.rangeRestrict.exists_pRegular_lift a.rangeRestrict_surjective
    2 Nat.prime_two v (by rw [hv]; decide)
  have hay : a y = Theory.PSL2.fieldAut σ := (congrArg Subtype.val hey).trans hx
  have hker : IsPGroup 2 a.ker := by
    rw [SourceRankOne.action_kernel hG T hempty hM hu hmany hcard e H hH eR]
    exact pCore_isPGroup
  have horder : orderOf y = 3 := by
    rw [←a.orderOf_map_eq_of_coprime_of_isPGroup_ker hker y
      (Nat.prime_two.coprime_iff_not_dvd.mpr hy), hay, Theory.PSL2.orderOf_fieldAut,hσ]
  exact ⟨σ,y,hσ,horder,hay⟩

/-- An inner conjugation places the lift in the original Sylow normalizer. -/
theorem cubic_normalizer_lift (hne : Mc ≠ H) :
    ∃ (σ : Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) (x : Mc)
      (j : Theory.PSL2.BinaryGroup 3),
      orderOf σ = 3 ∧ orderOf x = 3 ∧ (x : G) ∈ normalizer (T : Set G) ∧
      SourceRankOne.rankOneAction hG T hempty hM hu hmany hcard e H hH eR x =
        MulAut.congr (MulAut.conj j) (Theory.PSL2.fieldAut σ) ∧
      SourceRankOne.fieldAction hG T hempty hM hu hmany hcard e H hH eR x = σ := by
  let b := (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)
  let f := b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := b.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ b.injective,QuotientGroup.ker_mk']
  let S := T.subtype hH.1.1.2
  let P := S.mapSurjective hf
  let a := SourceRankOne.rankOneAction hG T hempty hM hu hmany hcard e H hH eR
  let d := SourceRankOne.fieldAction hG T hempty hM hu hmany hcard e H hH eR
  obtain ⟨σ,x,hσ,hx,hax⟩ := cubic_field_lift hG T hempty hM hu hmany hcard e H hH eR hne
  obtain ⟨j,hj,_⟩ := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylow_normalizer_conjugate
    (Theory.PSL2.BinaryField 3) P
  obtain ⟨h,hh⟩ := hf j
  let i := inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH)
  let y := MulAut.conj (i h) x
  have hai : a (i h) = MulAut.conj j := by
    rw [SourceRankOne.rankOneAction_on_first]
    exact congrArg MulAut.conj hh
  have hay : a y = MulAut.congr (MulAut.conj j) (Theory.PSL2.fieldAut σ) := by
    change a (i h * x * (i h)⁻¹) = _
    rw [map_mul,map_mul,map_inv,hai,hax]
    ext v
    rfl
  have hdy : d y = σ := by
    have hdi : d (i h) = 1 := by
      have hmem : i h ∈ H.subgroupOf Mc := h.property
      rw [←SourceRankOne.field_kernel hG T hempty hM hu hmany hcard e H hH eR] at hmem
      exact hmem
    have hdx : d x = σ := by
      change Theory.PSL2.fieldProjection _ (a x) = σ
      rw [hax,Theory.PSL2.fieldProjection_fieldAut]
    change d (i h * x * (i h)⁻¹) = σ
    rw [map_mul,map_mul,map_inv,hdi,hdx,inv_one,one_mul,mul_one]
  have hstable (u : Theory.PSL2.BinaryGroup 3) (hu : u ∈ (P : Subgroup _)) :
      a y u ∈ (P : Subgroup _) := by
    rw [←hj] at hu ⊢
    obtain ⟨v,hv,rfl⟩ := hu
    refine ⟨Theory.PSL2.fieldAut σ v,?_,?_⟩
    · rw [←Theory.PSL2.RootSemilinear.fieldAut_map_kernel σ]
      exact mem_map_of_mem _ hv
    · rw [hay]
      change MulAut.conj j (Theory.PSL2.fieldAut σ v) =
        MulAut.conj j (Theory.PSL2.fieldAut σ ((MulAut.conj j).symm (MulAut.conj j v)))
      rw [MulEquiv.symm_apply_apply]
  have hpre : (P : Subgroup _).comap f = (S : Subgroup H) := by
    change ((S : Subgroup H).map f).comap f = _
    rw [comap_map_eq]
    exact sup_eq_left.mpr (hk ▸ pCore_isPGroup.le_sylow_of_normal S)
  have hyN : (y : G) ∈ normalizer (T : Set G) := by
    apply mem_normalizer_fintype
    intro t ht
    let k : H := ⟨t,hH.1.1.2 ht⟩
    let k' := H.normalizerMonoidHom (inclusion
      (SourceNormal.partner_le_first_normalizer hG T hempty hM hu hmany hcard e H hH eR) y) k
    have hfk : f k' = a y (f k) :=
      (SourceRankOne.rankOneAction_mk hG T hempty hM hu hmany hcard e H hH eR y k).symm
    have hmem : k' ∈ (P : Subgroup _).comap f := by
      change f k' ∈ (P : Subgroup _)
      rw [hfk]
      exact hstable _ (mem_map_of_mem f ht)
    rw [hpre] at hmem
    exact hmem
  exact ⟨σ,y,j,hσ,(orderOf_injective (MulAut.conj (i h)).toMonoidHom (MulAut.conj (i h)).injective x).trans hx,
    hyN,hay,hdy⟩

/-- The same cubic subgroup supplements H and the whole original overlap. -/
theorem cubic_overlap_supplement (hne : Mc ≠ H) :
    ∃ (σ : Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) (x : Mc)
      (j : Theory.PSL2.BinaryGroup 3),
      orderOf σ = 3 ∧ orderOf x = 3 ∧
      SourceRankOne.rankOneAction hG T hempty hM hu hmany hcard e H hH eR x =
        MulAut.congr (MulAut.conj j) (Theory.PSL2.fieldAut σ) ∧
      SourceRankOne.fieldAction hG T hempty hM hu hmany hcard e H hH eR x = σ ∧
      zpowers (x : G) ≤ normalizer (T : Set G) ∧
      zpowers (x : G) ≤ M ⊓ Mc ∧ Nat.card (zpowers (x : G)) = 3 ∧
      Mc = H ⊔ zpowers (x : G) ∧ M ⊓ Mc = (M ⊓ H) ⊔ zpowers (x : G) := by
  obtain ⟨σ,x,j,hσ,hx,hn,hact,hfield⟩ := cubic_normalizer_lift
    hG T hempty hM hu hmany hcard e H hH eR hne
  let A := zpowers (x : G)
  have hA : A ≤ M ⊓ Mc := zpowers_le.mpr
    (source_lemma_14_2_2_7 hG T hempty hM hu hmany hcard e hn)
  let b := SourceRankOne.fieldAction hG T hempty hM hu hmany hcard e H hH eR
  have hmap : (zpowers x).map b = ⊤ := by
    rw [MonoidHom.map_zpowers,hfield]
    apply zpowers_eq_top_of_prime_card (GaloisField.card_ringAut 2 3 (by decide))
    intro he
    rw [he,orderOf_one] at hσ
    contradiction
  have hsup : zpowers x ⊔ H.subgroupOf Mc = ⊤ := by
    rw [←SourceRankOne.field_kernel hG T hempty hM hu hmany hcard e H hH eR,
      ←comap_map_eq,hmap,comap_top]
  have hamb := congrArg (Subgroup.map Mc.subtype) hsup
  rw [Subgroup.map_sup,MonoidHom.map_zpowers,map_subgroupOf_eq_of_le
    (source_first_le_partner hG hempty hM hu hmany hcard e hH),
    ←MonoidHom.range_eq_map,range_subtype,sup_comm] at hamb
  have hover : M ⊓ Mc = (M ⊓ H) ⊔ A := by
    apply le_antisymm
    · intro u huM
      have hp : u ∈ (H : Set G) * (A : Set G) := by
        rw [←coe_mul_of_right_le_normalizer_left H A
          ((hA.trans inf_le_right).trans
            (SourceNormal.partner_le_first_normalizer hG T hempty hM hu hmany hcard e H hH eR))]
        exact hamb.symm ▸ huM.2
      obtain ⟨v,hv,w,hw,he⟩ := hp
      have hvM : v ∈ M := by
        have ht := M.mul_mem huM.1 (M.inv_mem ((hA hw).1))
        rw [←he,mul_inv_cancel_right] at ht
        exact ht
      rw [←he]
      exact mul_mem_sup ⟨hvM,hv⟩ hw
    · exact sup_le (le_inf inf_le_left (inf_le_right.trans
        (source_first_le_partner hG hempty hM hu hmany hcard e hH))) hA
  exact ⟨σ,x,j,hσ,hx,hact,hfield,zpowers_le.mpr hn,hA,by rw [Nat.card_zpowers,Subgroup.orderOf_coe,hx],
    hamb.symm,hover⟩

omit eR in
private theorem second_partner_factorization :
    M = (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔ (M ⊓ Mc) := by
  have hne : M ≠ Mc := by
    intro he
    exact hH.1.2 (he.symm ▸ source_first_le_partner hG hempty hM hu hmany hcard e hH)
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hc := (plane_intersection_core_inputs hG T hempty hM.1 hu hmany hZ hne).2.1
  have hd := decomposition_of_intersectionCore_not_centralizing
    M Mc (localModule T M) T hM.1.2 ⟨e⟩ hc
  apply le_antisymm
  · calc
      M = (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔
          (M ⊓ centralizer (localModule T M : Set G)) := hd
      _ ≤ (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔ (M ⊓ Mc) :=
        sup_le le_sup_left ((le_inf inf_le_left
          (inf_le_right.trans (InitialSource.localModule_centralizer_le_partner T M hu))).trans le_sup_right)
  · exact sup_le (sup_le (sourceResidual_le M Mc) hM.1.2) inf_le_left

/-- Both original endpoints admit the same cubic supplement, retaining full set products. -/
theorem cubic_endpoint_factorizations :
    Mc = H ∨ ∃ A : Subgroup G,
      A ≤ M ⊓ Mc ∧ Nat.card A = 3 ∧
      Mc = H ⊔ A ∧ M ⊓ Mc = (M ⊓ H) ⊔ A ∧
      M = secondParabolic T M Mc H ⊔ A ∧
      A ≤ normalizer (secondParabolic T M Mc H : Set G) ∧
      (Mc : Set G) = (H : Set G) * (A : Set G) ∧
      (M : Set G) = (secondParabolic T M Mc H : Set G) * (A : Set G) := by
  by_cases he : Mc = H
  · exact Or.inl he
  · obtain ⟨σ,x,j,hσ,hx,hact,hfield,hAN,hA,hcardA,hMc,hI⟩ :=
      cubic_overlap_supplement hG T hempty hM hu hmany hcard e H hH eR he
    have hMsecond : M = secondParabolic T M Mc H ⊔ zpowers (x : G) := by
      calc
        M = (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔ (M ⊓ Mc) :=
          second_partner_factorization hG T hempty hM hu hmany hcard e H hH
        _ = secondParabolic T M Mc H ⊔ zpowers (x : G) := by
          simp only [hI,secondParabolic,first_residual hG T hempty hM hu hmany hcard e H hH eR,sup_assoc]
    have hAH : zpowers (x : G) ≤ normalizer (H : Set G) :=
      (hA.trans inf_le_right).trans
        (SourceNormal.partner_le_first_normalizer hG T hempty hM hu hmany hcard e H hH eR)
    have hAM : zpowers (x : G) ≤ M := hA.trans inf_le_left
    have hAY : zpowers (x : G) ≤ normalizer (sourceResidual M Mc : Set G) :=
      hAM.trans ((normal_subgroupOf_iff_le_normalizer (sourceResidual_le M Mc)).mp
        (residualY_normal M Mc))
    have hAn : zpowers (x : G) ≤ normalizer (secondParabolic T M Mc H : Set G) := by
      rw [secondParabolic,first_residual hG T hempty hM hu hmany hcard e H hH eR]
      exact (le_inf ((le_inf hAY hAN).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _))
          ((le_inf (hAM.trans M.le_normalizer) hAH).trans inf_normalizer_le_normalizer_inf)).trans
            (normalizer_inf_normalizer_le_normalizer_sup _ _)
    refine Or.inr ⟨zpowers (x : G),hA,hcardA,hMc,hI,hMsecond,hAn,?_,?_⟩
    · exact (congrArg (fun X : Subgroup G => (X : Set G)) hMc).trans
        (coe_mul_of_right_le_normalizer_left _ _ hAH)
    · exact (congrArg (fun X : Subgroup G => (X : Set G)) hMsecond).trans
        (coe_mul_of_right_le_normalizer_left _ _ hAn)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCubic
