module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.UFixer
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.InnerCoordinates
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair.Coordinates

/-!
# Centralizers of the last deleted coordinate unit

The deleted class of the sixth coordinate unit defines an involution fixing the
canonical quaternion core. Its fixed subgroup in the natural split A₆ block
projects onto the actual letter-stabilizing A₅ with translation kernel; its
order is 960. In the full deleted-module automorphism model, its centralizer
projects onto the letter-stabilizing S₅ with deleted translation kernel and
has order 3840. All projections retain the literal coordinate unit at index 5.

The coordinate unit lies outside the natural even submodule, so the induced
automorphism cannot be inner conjugation by a natural translation.
Source: Aschbacher–Smith 14.3.20, second paragraph, printed pp.997–998.
-/

@[expose] public section
namespace BinaryPermutation.SixNaturalSplit
open Subgroup SemidirectProduct
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

noncomputable def deletedUnit (i : Fin 6) : Deleted (Fin 6) :=
  (constants (Fin 6)).mkQ (Pi.single i 1)

theorem deletedUnit_injective : Function.Injective deletedUnit := by
  intro i j hij
  by_contra hne
  have hh : Pi.single i (1:ZMod 2)-Pi.single j 1 ∈ constants (Fin 6) :=
    (Submodule.Quotient.eq _).mp hij
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hh
  have hk : ∀ i j:Fin 6,∃k,k≠i ∧ k≠j := by decide
  obtain ⟨k,hki,hkj⟩ := hk i j
  have hz : c=0 := by simpa [allOne,Pi.single_apply,hki,hkj] using congrFun hc k
  have hi := congrFun hc i
  simp [hz,allOne,hne] at hi

theorem deletedUnit_action (s : Equiv.Perm (Fin 6)) (i : Fin 6) :
    deletedRepresentation (Fin 6) s (deletedUnit i)=deletedUnit (s i) := by
  rw [deletedUnit,deletedRepresentation_mk,deletedUnit]
  congr 1
  ext j
  simp [representation_apply,Pi.single_apply,Equiv.symm_apply_eq]

theorem deletedUnit_not_natural (i : Fin 6) : deletedUnit i ∉ natural (Fin 6) := by
  rintro ⟨w,hw,he⟩
  have hc : w-Pi.single i (1:ZMod 2) ∈ constants (Fin 6) := (Submodule.Quotient.eq _).mp he
  have hh := ((constants_le_core_iff (Fin 6)).mpr (by decide)) hc
  have hi : Pi.single i (1:ZMod 2) ∈ core (Fin 6) := by
    convert (core (Fin 6)).sub_mem hw hh using 1
    abel
  simp [mem_core] at hi

noncomputable def deletedPoint : Multiplicative (Deleted (Fin 6)) := Multiplicative.ofAdd (deletedUnit 5)
noncomputable def pointAutomorphism : MulAut Model := kernelHom deletedPoint

theorem pointAutomorphism_tail : pointAutomorphism=tailKernel (Multiplicative.ofAdd ![0,1]) := by
  change kernelHom (Multiplicative.ofAdd ((constants (Fin 6)).mkQ (Pi.single 5 1))) =
    kernelHom (Multiplicative.ofAdd ((constants (Fin 6)).mkQ (tailFull ![0,1])))
  congr 3
  ext i
  simp [tailFull]

theorem pointAutomorphism_fixes_core : pointAutomorphism∈canonicalFixer := by
  rw [pointAutomorphism_tail]
  exact tailKernel_fixes _

theorem pointAutomorphism_square : pointAutomorphism^2=1 := by
  rw [pointAutomorphism_tail]
  exact tailKernel_square _

theorem pointAutomorphism_ne_one : pointAutomorphism≠1 := by
  intro h
  have he : deletedPoint=1 := by
    apply kernelEquiv.injective
    exact Subtype.ext (h.trans (congrArg Subtype.val (map_one kernelEquiv)).symm)
  have hz : deletedUnit 5=0 := congrArg Multiplicative.toAdd he
  exact deletedUnit_not_natural 5 (hz.symm ▸ (natural (Fin 6)).zero_mem)

theorem deletedEquiv_value (d : Deleted (Fin 6)) (g : Actor) :
    ((SixNaturalCocycles.deletedEquiv d).val g : Deleted (Fin 6))=
      deletedRepresentation (Fin 6) g.val d-d := by
  obtain ⟨w,rfl⟩ := (constants (Fin 6)).mkQ_surjective d
  rw [SixNaturalCocycles.deletedEquiv_mk,deletedRepresentation_mk]
  rfl

theorem point_cocycle_zero (g : Actor) :
    (SixNaturalCocycles.deletedEquiv (deletedUnit 5)).val g=0 ↔ g.val 5=5 := by
  rw [←Subtype.val_inj,deletedEquiv_value,Submodule.coe_zero,sub_eq_zero,deletedUnit_action]
  exact deletedUnit_injective.eq_iff

theorem pointAutomorphism_fixed_iff (x : Model) :
    x∈pointAutomorphism.fixedSubgroup ↔ x.right.val 5=5 := by
  rw [MulAut.mem_fixedSubgroup]
  change (kernelEquiv deletedPoint).val x=x ↔ _
  rw [kernelEquiv_apply]
  constructor
  · intro hx
    have he := congrArg (fun x:Model=>x.left.toAdd) hx
    change x.left.toAdd+(SixNaturalCocycles.deletedEquiv (deletedUnit 5)).val x.right=x.left.toAdd at he
    exact (point_cocycle_zero _).mp (add_left_cancel (he.trans (add_zero _).symm))
  · intro hx
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change x.left.toAdd+(SixNaturalCocycles.deletedEquiv (deletedUnit 5)).val x.right=x.left.toAdd
      rw [(point_cocycle_zero _).mpr hx,add_zero]
    · rfl

noncomputable def pointActor := MulAction.stabilizer Actor (5:Fin 6)
noncomputable def pointActorEquiv : pointActor ≃* alternatingGroup (Fin 5) :=
  AlternatingSix.SmallIndex.pointEquiv (n:=5) 5

theorem pointActor_card : Nat.card pointActor=60 := by
  rw [Nat.card_congr pointActorEquiv.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
  decide

noncomputable def pointFixedCoordinates : pointAutomorphism.fixedSubgroup ≃ Vector × pointActor where
  toFun x := (x.val.left,⟨x.val.right,(pointAutomorphism_fixed_iff _).mp x.property⟩)
  invFun x := ⟨⟨x.1,x.2.val⟩,(pointAutomorphism_fixed_iff _).mpr x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem pointAutomorphism_fixed_card : Nat.card pointAutomorphism.fixedSubgroup=960 := by
  rw [Nat.card_congr pointFixedCoordinates,Nat.card_prod,pointActor_card]
  change Nat.card (natural (Fin 6))*60=960
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,finrank_natural_even _ (by decide)]
  decide

noncomputable def pointFixedProjection : pointAutomorphism.fixedSubgroup →* pointActor :=
  (rightHom.comp pointAutomorphism.fixedSubgroup.subtype).codRestrict pointActor
    (fun x=>(pointAutomorphism_fixed_iff _).mp x.property)

theorem pointFixedProjection_surjective : Function.Surjective pointFixedProjection := by
  intro g
  exact ⟨⟨inr g.val,(pointAutomorphism_fixed_iff _).mpr g.property⟩,rfl⟩

theorem pointFixedProjection_ker : pointFixedProjection.ker=translations.subgroupOf pointAutomorphism.fixedSubgroup := by
  ext x
  change pointFixedProjection x=1 ↔ x.val∈translations
  rw [←Subtype.val_inj]
  change x.val.right=1 ↔ x.val∈translations
  rw [translations,range_inl_eq_ker_rightHom]
  rfl

noncomputable def pointFixedQuotientEquiv :
    (pointAutomorphism.fixedSubgroup ⧸ translations.subgroupOf pointAutomorphism.fixedSubgroup) ≃*
      alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq pointFixedProjection_ker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective pointFixedProjection pointFixedProjection_surjective).trans pointActorEquiv)


theorem kernelHom_natural_conj (v : natural (Fin 6)) :
    kernelHom (Multiplicative.ofAdd (-v.val))=MulAut.conj (inl (Multiplicative.ofAdd v) : Model) := by
  obtain ⟨w,rfl⟩ := coreToNatural_surjective v
  have hd : SixNaturalCocycles.deletedEquiv (-(coreToNatural (Fin 6) w).val)=
      naturalDisplacement (Fin 6) (-w.val) := by
    change SixNaturalCocycles.deletedEquiv (-((constants (Fin 6)).mkQ w.val))=_
    rw [←map_neg,SixNaturalCocycles.deletedEquiv_mk]
  apply MulEquiv.ext
  intro x
  change (kernelEquiv (Multiplicative.ofAdd (-(coreToNatural (Fin 6) w).val))).val x = _
  rw [kernelEquiv_apply]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.val_injective
    simp only [MulAut.conj_apply,mul_left,inv_left,left_inl,right_inl,
      mul_right,one_mul,inv_one,map_one,MulAut.one_apply]
    change (x.left.toAdd+(SixNaturalCocycles.deletedEquiv (-(coreToNatural (Fin 6) w).val)).val x.right).val=_
    rw [hd]
    change x.left.toAdd.val+((constants (Fin 6)).mkQ (representation (Fin 6) x.right.val (-w.val)-(-w.val))) =
      (constants (Fin 6)).mkQ w.val+x.left.toAdd.val+
        -(deletedRepresentation (Fin 6) x.right.val ((constants (Fin 6)).mkQ w.val))
    rw [map_sub,map_neg,map_neg,deletedRepresentation_mk,map_neg]
    abel
  · simp only [MulAut.conj_apply,mul_right,right_inl,inv_right,inv_one,one_mul,mul_one]

theorem pointAutomorphism_not_inner_translation (v : Vector) :
    pointAutomorphism≠MulAut.conj (inl v : Model) := by
  intro h
  have hh : deletedPoint=Multiplicative.ofAdd (-v.toAdd.val) := by
    apply kernelEquiv.injective
    apply Subtype.ext
    exact h.trans (kernelHom_natural_conj v.toAdd).symm
  have he : deletedUnit 5= -v.toAdd.val := congrArg Multiplicative.toAdd hh
  apply deletedUnit_not_natural 5
  rw [he]
  exact (natural (Fin 6)).neg_mem v.toAdd.property


noncomputable def pointSymmetric := MulAction.stabilizer (Equiv.Perm (Fin 6)) (5:Fin 6)

theorem pointSymmetric_card : Nat.card pointSymmetric=120 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Equiv.Perm (Fin 6)) (5:Fin 6))
  rw [Nat.card_prod,MulAction.orbit_eq_univ] at h
  have ho : Nat.card (Set.univ : Set (Fin 6))=6 := by simp
  rw [ho,Nat.card_eq_fintype_card (α:=Equiv.Perm (Fin 6)),Fintype.card_perm,Fintype.card_fin] at h
  change 6*Nat.card pointSymmetric=720 at h
  omega

noncomputable def pointSymmetricEmbedding : Equiv.Perm (Fin 5) →* pointSymmetric :=
  FivePair.extendPerm.codRestrict _ (fun s=>FivePair.extendPerm_last s)

theorem pointSymmetricEmbedding_bijective : Function.Bijective pointSymmetricEmbedding := by
  have hi : Function.Injective pointSymmetricEmbedding := by
    intro a b h
    exact Equiv.Perm.extendDomainHom_injective FivePair.letterEquiv (congrArg Subtype.val h)
  exact hi.bijective_of_nat_card_le (by
    rw [pointSymmetric_card,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide)

noncomputable def pointSymmetricEquiv : pointSymmetric ≃* Equiv.Perm (Fin 5) :=
  (MulEquiv.ofBijective pointSymmetricEmbedding pointSymmetricEmbedding_bijective).symm

noncomputable def deletedPointElement : AutomorphismModel := inl deletedPoint
noncomputable def deletedPointCentralizer : Subgroup AutomorphismModel :=
  centralizer ({deletedPointElement}:Set AutomorphismModel)

theorem deletedPointCentralizer_iff (x:AutomorphismModel) :
    x∈deletedPointCentralizer ↔ x.right 5=5 := by
  rw [deletedPointCentralizer,mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hl := congrArg SemidirectProduct.left h
    simp only [mul_left,deletedPointElement,left_inl,right_inl,map_one,MulAut.one_apply] at hl
    change x.left*deletedAction x.right deletedPoint=deletedPoint*x.left at hl
    rw [mul_comm deletedPoint x.left] at hl
    have hd := congrArg Multiplicative.toAdd (mul_left_cancel hl)
    change deletedRepresentation (Fin 6) x.right (deletedUnit 5)=deletedUnit 5 at hd
    rw [deletedUnit_action] at hd
    exact deletedUnit_injective hd
  · intro h
    apply SemidirectProduct.ext
    · simp only [mul_left,deletedPointElement,left_inl,right_inl,map_one,MulAut.one_apply]
      change x.left*deletedAction x.right deletedPoint=deletedPoint*x.left
      have hd : deletedAction x.right deletedPoint=deletedPoint := by
        apply Multiplicative.toAdd.injective
        change deletedRepresentation (Fin 6) x.right (deletedUnit 5)=deletedUnit 5
        rw [deletedUnit_action,h]
      rw [hd,mul_comm]
    · simp only [mul_right,deletedPointElement,right_inl,mul_one,one_mul]

noncomputable def deletedPointCentralizerCoordinates :
    deletedPointCentralizer ≃ Multiplicative (Deleted (Fin 6)) × pointSymmetric where
  toFun x := (x.val.left,⟨x.val.right,(deletedPointCentralizer_iff _).mp x.property⟩)
  invFun x := ⟨⟨x.1,x.2.val⟩,(deletedPointCentralizer_iff _).mpr x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem deletedPointCentralizer_card : Nat.card deletedPointCentralizer=3840 := by
  rw [Nat.card_congr deletedPointCentralizerCoordinates,Nat.card_prod,pointSymmetric_card]
  change Nat.card (Deleted (Fin 6))*120=3840
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,finrank_deleted]
  decide

noncomputable def deletedPointCentralizerProjection : deletedPointCentralizer →* pointSymmetric :=
  (rightHom.comp deletedPointCentralizer.subtype).codRestrict pointSymmetric
    (fun x=>(deletedPointCentralizer_iff _).mp x.property)

theorem deletedPointCentralizerProjection_surjective :
    Function.Surjective deletedPointCentralizerProjection := by
  intro g
  exact ⟨⟨inr g.val,(deletedPointCentralizer_iff _).mpr g.property⟩,rfl⟩

theorem deletedPointCentralizerProjection_ker : deletedPointCentralizerProjection.ker=
    (rightHom : AutomorphismModel→*Equiv.Perm (Fin 6)).ker.subgroupOf deletedPointCentralizer := by
  ext x
  change deletedPointCentralizerProjection x=1 ↔ x.val.right=1
  exact Subtype.val_inj.symm

noncomputable def deletedPointCentralizerQuotientEquiv :
    (deletedPointCentralizer ⧸
      (rightHom : AutomorphismModel→*Equiv.Perm (Fin 6)).ker.subgroupOf deletedPointCentralizer) ≃*
        Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq deletedPointCentralizerProjection_ker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective deletedPointCentralizerProjection
      deletedPointCentralizerProjection_surjective).trans pointSymmetricEquiv)

theorem automorphismEquiv_pointAutomorphism
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    automorphismEquiv hN pointAutomorphism=deletedPointElement := by
  apply (automorphismEquiv hN).symm.injective
  rw [MulEquiv.symm_apply_apply]
  change pointAutomorphism=kernelHom deletedPoint*diagonal 1
  rw [map_one,mul_one]
  rfl

noncomputable def pointAutCentralizerEquiv
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    centralizer ({pointAutomorphism}:Set (MulAut Model)) ≃* deletedPointCentralizer :=
  ((MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj pointAutomorphism).symm).trans
    (MulAut.fixedSubgroupCongr (automorphismEquiv hN) (MulAut.conj pointAutomorphism))).trans
      (MulEquiv.subgroupCongr (by
        rw [MulAut.congr_conj,automorphismEquiv_pointAutomorphism,MulAut.fixedSubgroup_conj]
        rfl))

end BinaryPermutation.SixNaturalSplit
