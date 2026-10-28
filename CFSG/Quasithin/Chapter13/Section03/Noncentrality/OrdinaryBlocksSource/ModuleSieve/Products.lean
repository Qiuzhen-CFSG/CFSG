module
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedRestriction
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.BinaryComponentRows
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.Representation.BinaryOffender.IrreducibleCentralLift
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# A₅ component moved spaces in the product rows

An actual component lies in one factor of the B.5.6 internal product.
Its A₅ identification excludes the linear-three rows. In the remaining
SL₂ or S₅ rows the natural module restricts irreducibly to that component.
The quotient-image kernel is central, so perfectness lifts Irr⁺ to the
literal moved space. The hyperplane row uses the same argument on its
second factor's reduced action; no ambient splitting is needed.

These are the last module-row deductions used by ModuleSieve/Complete
in the ordinary 13.3.14 source application. Source: Aschbacher--Smith
B.5.6(3),(5), p.105, and 13.3.14, pp.892--893.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterB.SourceInduction ChapterB.QuasisimpleSource

private theorem irrPlus_top_of_irreducible
    {D X : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) D X) (C : Subgroup D) [Nontrivial C]
    (hi : IsIrreducible (σ.comp C.subtype)) (hf : Function.Injective (σ.comp C.subtype)) :
    IsIrrPlus σ C ⊤ := by
  let := hi
  have hn : ¬ (⊤ : Submodule (ZMod 2) X) ≤ fixedSpace σ C := by
    intro hz
    obtain ⟨c,hc⟩ := exists_ne (1 : C)
    apply hc
    apply hf
    ext x
    simpa using hz (Submodule.mem_top : x ∈ (⊤ : Submodule (ZMod 2) X)) c
  have hmin (J : Submodule (ZMod 2) X) (hJ : C ≤ subspaceStabilizer σ J) :
      J = ⊤ ∨ J ≤ fixedSpace σ C := by
    rcases eq_bot_or_eq_top (invariantSubspace σ C J hJ) with hz | ht
    · exact Or.inr ((congrArg Subrepresentation.toSubmodule hz).le.trans bot_le)
    · exact Or.inl (congrArg Subrepresentation.toSubmodule ht)
  apply isIrrPlus_of_minimal σ (le_subspaceStabilizer σ ⊤ (by simp)) ?_ hn
    (fun J hJ _ => hmin J hJ)
  rcases hmin (moved σ C) (subspaceCommutator_invariant σ ⊤ C) with ht | hz
  · exact ht
  · have hzero : moved σ C = ⊥ := by
      -- An irreducible action has no proper nonzero invariant space.
      rcases eq_bot_or_eq_top (invariantSubspace σ C (moved σ C)
        (subspaceCommutator_invariant σ ⊤ C)) with h | h
      · exact congrArg Subrepresentation.toSubmodule h
      · have he : moved σ C = ⊤ := congrArg Subrepresentation.toSubmodule h
        rw [he] at hz
        exact (hn hz).elim
    exact (hn ((subspaceCommutator_eq_bot_iff σ ⊤ C).mp hzero)).elim

private theorem moved_irrPlus_of_central_image
    {D V X : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [Group.IsPerfect C] [Nontrivial C]
    (U : Subrepresentation ρ) (hU : moved ρ C ≤ U.toSubmodule)
    (σ : Representation (ZMod 2) D X) (f : U.toSubmodule →ₗ[ZMod 2] X)
    (hs : Function.Surjective f) (he : ∀ c : C, ∀ v, f (U.toRepresentation c v) = σ c (f v))
    (hk : f.ker ≤ fixedSpace U.toRepresentation C)
    (hi : IsIrreducible (σ.comp C.subtype)) (hf : Function.Injective (σ.comp C.subtype)) :
    IsIrrPlus ρ C (moved ρ C) := by
  have hl := IsIrrPlus.of_central_surjection U.toRepresentation σ C f hs he hk
    (irrPlus_top_of_irreducible σ C hi hf)
  have hm := IsIrrPlus.map_embedding ρ U.toRepresentation (MonoidHom.id D)
    U.toSubmodule.subtype U.toSubmodule.subtype_injective (fun _ _ => rfl)
    C (moved U.toRepresentation C) (by simpa using hl)
  have heq := subspaceCommutator_map_embedding ρ U.toRepresentation (MonoidHom.id D)
    U.toSubmodule.subtype (fun _ _ => rfl) C (⊤ : Submodule (ZMod 2) U.toSubmodule)
  simp only [Submodule.map_top, Submodule.range_subtype, Subgroup.map_id] at heq
  rw [←heq,subspaceCommutator_eq_moved_of_contains_moved ρ C U.toSubmodule hU] at hm
  exact hm

private theorem component_top_of_linearTwo
    {D : Type*} [Group D] (C : Subgroup D) (hC : IsComponent D C)
    (F : BinaryField) (e : D ≃* SL(2,F.Carrier)) : C = ⊤ := by
  by_cases hd : F.degree = 1
  · let e3 := e.trans ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
      ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
        BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype,←alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective (f := e3.toMonoidHom) e3.injective
    let := hC.2
    let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  · have hl : 3 < Nat.card F.Carrier := by
      rw [F.card_eq]
      have hd' : 2 ≤ F.degree := by have := F.degree_pos; omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd'
      norm_num at hp
      omega
    let : IsSimpleGroup PSL(2,F.Carrier) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let hs : IsSimpleGroup D := (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL).isSimpleGroup
    exact (hC.1.eq_bot_or_top_of_isSimpleGroup hs).resolve_left hC.isCComponent.ne_bot

private theorem natural_two_component_irreducible
    {D X : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) D X) (C : Subgroup D) (hC : IsComponent D C)
    (F : BinaryField) (hn : IsLinearNatural σ F 2) :
    IsIrreducible (σ.comp C.subtype) := by
  obtain ⟨e⟩ := hn
  have ht := component_top_of_linearTwo C hC F e.groupEquiv
  have hs : Function.Surjective C.subtype := by
    intro x
    exact ⟨⟨x,ht ▸ mem_top x⟩,rfl⟩
  exact (irreducible_comp_surjective_iff C.subtype hs σ).mpr
    (ExtensionConsequences.irreducible_of_equiv e
      (ExtensionConsequences.linearNatural_irreducible F (by decide)))


private theorem natural_five_component_irreducible
    {D X : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) D X) (C : Subgroup D) (hC : IsComponent D C)
    (hn : IsSymmetricNatural σ 5) : IsIrreducible (σ.comp C.subtype) := by
  obtain ⟨e⟩ := hn
  let N := alternatingGroup (Fin 5)
  let : IsSimpleGroup N := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple N :=
    { toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      simple := ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hN : IsComponent (Equiv.Perm (Fin 5)) N :=
    ⟨(inferInstance : N.Normal).isSubnormal,inferInstance⟩
  have hc := hC.map_equiv e.groupEquiv
  let := hc.2
  have heq : C.map e.groupEquiv.toMonoidHom = N := by
    apply hc.eq_of_le hN
    rw [← commutator_eq_self (H := C.map e.groupEquiv.toMonoidHom)]
    exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
  let a : ActionEquiv (σ.comp C.subtype)
      ((BinaryPermutation.naturalRepresentation (Fin 5)).comp N.subtype) :=
    { groupEquiv := (C.equivMapOfInjective e.groupEquiv.toMonoidHom e.groupEquiv.injective).trans
        (MulEquiv.subgroupCongr heq)
      linearEquiv := e.linearEquiv
      intertwines := fun c v => e.intertwines c v }
  exact ExtensionConsequences.irreducible_of_equiv a
    (BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide))

private theorem moved_irrPlus_of_quotientImage
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [Group.IsPerfect C] [Nontrivial C]
    (U : Subrepresentation ρ) (hU : moved ρ C ≤ U.toSubmodule)
    (hi : IsIrreducible (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype))
    (hf : Function.Injective (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype)) :
    IsIrrPlus ρ C (moved ρ C) := by
  let I := (fixed ρ).quotientImage U
  let f : U.toSubmodule →ₗ[ZMod 2] I.toSubmodule :=
    LinearMap.codRestrict I.toSubmodule ((fixed ρ).toSubmodule.mkQ.comp U.toSubmodule.subtype)
      (fun v => ⟨v,v.property,rfl⟩)
  apply moved_irrPlus_of_central_image ρ C U hU I.toRepresentation f ?_ ?_ ?_ hi hf
  · rintro ⟨_,v,hv,rfl⟩
    exact ⟨⟨v,hv⟩,rfl⟩
  · intro c v
    rfl
  · intro v hv c
    have he : (fixed ρ).toSubmodule.mkQ v = 0 := congrArg Subtype.val hv
    have hz := (Submodule.Quotient.mk_eq_zero _).mp he
    exact Subtype.ext (hz c)

private noncomputable def fiveEquivLinearTwo :
    alternatingGroup (Fin 5) ≃* SL(2,BinaryField.four.Carrier) :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := BinaryField.four.Carrier) (by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      decide)).some.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
        QuotientGroup.quotientBot)

private theorem factor_irrPlus_of_component_five
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C A : Subgroup D) [A.Normal]
    (hC : IsComponent D C) (hCA : C ≤ A) (eC : C ≃* alternatingGroup (Fin 5))
    (U : Subrepresentation ρ) (h : SourceFactorCase ρ A U) : IsIrrPlus ρ C (moved ρ C) := by
  let := hC.2
  let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
  obtain ⟨hm,hn⟩ := h.rankOne_of_binary_component hC hCA (eC.trans fiveEquivLinearTwo)
  let σ := ((fixed ρ).quotientImage U).toRepresentation
  have hi : IsIrreducible ((σ.comp A.subtype).comp (C.subgroupOf A).subtype) := by
    rcases hn with ⟨F,hn⟩ | hn
    · exact natural_two_component_irreducible _ _ (hC.subgroupOf hCA) F hn
    · exact natural_five_component_irreducible _ _ (hC.subgroupOf hCA) hn
  have hi' : IsIrreducible (σ.comp C.subtype) :=
    (irreducible_comp_surjective_iff (subgroupOfEquivOfLe hCA).toMonoidHom
      (subgroupOfEquivOfLe hCA).surjective (σ.comp C.subtype)).mp hi
  have hf : Function.Injective (σ.comp C.subtype) := by
    intro a b hab
    have he : (⟨a,hCA a.property⟩ : A) = ⟨b,hCA b.property⟩ := h.faithful hab
    exact Subtype.ext (congrArg (fun x : A => (x : D)) he)
  apply moved_irrPlus_of_quotientImage ρ C U ?_ hi' hf
  rw [hm]
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,hv,rfl⟩
  exact Submodule.subset_span ⟨g,hCA hg,v,hv,rfl⟩

private theorem component_le_product_factor
    {D : Type*} [Group D] {A B C : Subgroup D}
    (h : InternalProduct A B) (hC : IsComponent D C) : C ≤ A ∨ C ≤ B := by
  let := h.swap.second_normal
  let := h.second_normal
  rcases hC.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hC.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have hc : C ≤ centralizer ((A ⊔ B : Subgroup D) : Set D) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  rw [h.sup_eq_top] at hc
  have hcc : ⁅C,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (centralizer_le (show (C : Set D) ⊆ (⊤ : Subgroup D) from Set.subset_univ _)))
  let := hC.2
  rw [commutator_eq_self] at hcc
  exact (hC.isCComponent.ne_bot hcc).elim

/-- The two-factor source row gives Irr⁺ on the original A₅ component's moved space. -/
theorem twoFactor_moved_irrPlus_of_component_five
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) (hC : IsComponent D C)
    (eC : C ≃* alternatingGroup (Fin 5)) (c : SourceTwoFactorCase ρ) :
    IsIrrPlus ρ C (moved ρ C) := by
  rcases component_le_product_factor c.product hC with ha | hb
  · let := c.product.swap.second_normal
    exact factor_irrPlus_of_component_five ρ C c.first hC ha eC c.firstSpace c.firstCase
  · let := c.product.second_normal
    exact factor_irrPlus_of_component_five ρ C c.second hC hb eC c.secondSpace c.secondCase


private theorem no_linearThree_factor_of_component_five
    {D : Type*} [Group D] {C A : Subgroup D} [A.Normal]
    (hC : IsComponent D C) (hCA : C ≤ A) (eC : C ≃* alternatingGroup (Fin 5))
    (F : BinaryField) (eA : A ≃* SL(3,F.Carrier)) : False := by
  let : IsQuasisimple SL(3,F.Carrier) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  have hA : IsComponent D A :=
    ⟨(inferInstance : A.Normal).isSubnormal,IsQuasisimple.of_mulEquiv eA.symm⟩
  have he := hC.eq_of_le hA hCA
  let e := ((MulEquiv.subgroupCongr he).symm.trans eC).symm.trans eA
  have hd := card_subgroup_dvd_card (Matrix.PSL3.LinearThree.unipotentSL F.Carrier)
  rw [Matrix.PSL3.LinearThree.card_unipotentSL,←Nat.card_congr e.toEquiv,
    nat_card_alternatingGroup,F.card_eq] at hd
  have htwo : 2 ∣ 2 ^ F.degree := dvd_pow_self _ (Nat.ne_of_gt F.degree_pos)
  have hdiv := (pow_dvd_pow_of_dvd htwo 3).trans hd
  norm_num [Nat.factorial] at hdiv

private theorem linearNatural_faithful
    {D X : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) D X} (F : BinaryField) (n : ℕ)
    (hn : IsLinearNatural σ F n) : Function.Injective σ := by
  obtain ⟨e⟩ := hn
  intro a b hab
  apply e.groupEquiv.injective
  apply specialLinearNatural_injective n
  apply LinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.linearEquiv.surjective v
  exact (e.intertwines a x).symm.trans
    ((congrArg e.linearEquiv (LinearMap.congr_fun hab x)).trans (e.intertwines b x))

private theorem moved_irrPlus_of_reduced_natural
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) [Group.IsPerfect C] [Nontrivial C]
    (U : Subrepresentation ρ) (hU : moved ρ C ≤ U.toSubmodule)
    (F : BinaryField) (hn : IsLinearNatural (reducedAction (U.toRepresentation.comp C.subtype)) F 2) :
    IsIrrPlus ρ C (moved ρ C) := by
  let Uc : Subrepresentation (ρ.comp C.subtype) :=
    ⟨U.toSubmodule,fun c _ hv => U.apply_mem_toSubmodule c hv⟩
  let σ := reducedAction Uc.toRepresentation
  have hmc : moved (ρ.comp C.subtype) ⊤ = moved ρ C := by
    rw [moved_comp_map,←MonoidHom.range_eq_map,range_subtype]
  have hi : IsIrreducible σ := ExtensionConsequences.irreducible_of_equiv hn.some
    (ExtensionConsequences.linearNatural_irreducible F (by decide))
  have hf : Function.Injective σ := linearNatural_faithful F 2 hn
  have hi' : IsIrreducible (σ.comp (⊤ : Subgroup C).subtype) :=
    (irreducible_comp_surjective_iff _ Subgroup.topEquiv.surjective σ).mpr hi
  have hl := moved_irrPlus_of_central_image (ρ.comp C.subtype) ⊤ Uc
    (hmc ▸ hU) σ (fixed Uc.toRepresentation).toSubmodule.mkQ
    (fixed Uc.toRepresentation).toSubmodule.mkQ_surjective
    (fun _ _ => rfl) (by
      intro v hv c
      exact ((Submodule.Quotient.mk_eq_zero _).mp hv) c) hi'
    (hf.comp (⊤ : Subgroup C).subtype_injective)
  rw [hmc] at hl
  apply (IsIrrPlus.subgroupOf_iff ρ C C le_rfl _).mp
  simpa only [subgroupOf_self] using hl

/-- The hyperplane source row also gives Irr⁺ on its original A₅ component. -/
theorem hyperplane_moved_irrPlus_of_component_five
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (C : Subgroup D) (hC : IsComponent D C)
    (eC : C ≃* alternatingGroup (Fin 5)) (c : HyperplaneCase ρ) :
    IsIrrPlus ρ C (moved ρ C) := by
  let := c.product.swap.second_normal
  let := c.product.second_normal
  rcases component_le_product_factor c.product hC with ha | hb
  · exact (no_linearThree_factor_of_component_five hC ha eC BinaryField.two c.firstEquiv).elim
  · cases c.secondCase with
    | linearThree r _ hn =>
      exact (no_linearThree_factor_of_component_five hC hb eC BinaryField.two hn.some.groupEquiv).elim
    | linearTwo F hn =>
      have ht := component_top_of_linearTwo (C.subgroupOf c.second) (hC.subgroupOf hb) F
        hn.some.groupEquiv
      have he : C = c.second := le_antisymm hb (subgroupOf_eq_top.mp ht)
      let := hC.2
      let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.isCComponent.ne_bot
      apply moved_irrPlus_of_reduced_natural ρ C c.secondSpace ?_ F (he ▸ hn)
      rw [c.secondSpace_eq,he]


end CFSG.Quasithin.Chapter13.Section03.Noncentrality
