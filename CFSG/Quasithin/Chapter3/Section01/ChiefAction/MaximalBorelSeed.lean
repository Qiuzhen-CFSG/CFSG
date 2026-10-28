module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.MaximalBorelLift
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SeedClassification

/-!
# Small natural alternatives from the actual maximal subgroup and seed

Use the maximal subgroup containing the original Sylow, whose two-residual
centralizes the actual seed subgroup. The whole kernel of the faithful action
image is retained. A nonzero seed excludes single and paired higher-field
natural coordinates. The FF premise is supplied for this literal action; no
inheritance of FF from a containing section is asserted.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter3.MaximalBorel
open ChapterB ChapterB.QuasisimpleSource HigherFieldBorelFixedSpaces
variable {G D W : Type*} [Group G] [Finite G] [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {H V : Subgroup G}

private theorem quasisimple_natural_seed_excluded
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsCoatom N)
    (hSN : (S : Subgroup H) ≤ N) (hP : IsMinimalParabolicOver S ⊤)
    (hres : (pResidual 2 N).map N.subtype ≤ (centralizer (V : Set G)).subgroupOf H)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ) (hi : IsIrreducible ρ)
    (v : W) (hvne : v ≠ 0)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (hqs : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ)))
    (F : BinaryField) (hF : 4 ≤ Nat.card F.Carrier)
    (e : ActionEquiv (s.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      (linearNatural F 2)) : False := by
  let Y := offenderSubgroup ρ
  let A := generalizedFitting Y
  let : Y.Normal := offenderSubgroup_normal ρ
  let : IsQuasisimple A := hqs
  let L := A.map Y.subtype
  let eA := A.equivMapOfInjective Y.subtype Y.subtype_injective
  let eL := eA.symm.trans e.groupEquiv
  let : IsSimpleGroup PSL(2,F.Carrier) := ProjectiveSpecialLinearGroup.rank_two_simple hF
  let : IsSimpleGroup L := (eL.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL).isSimpleGroup
  let : IsSimpleGroup A := eA.isSimpleGroup
  have hL : IsComponent D L :=
    ⟨(inferInstance : A.Normal).isSubnormal.trans' (inferInstance : Y.Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv eA⟩
  have heven : 2 ∣ Nat.card L := by
    rw [Nat.card_congr eL.toEquiv]
    have hfcard : 2 ∣ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact dvd_pow_self 2 F.degree_pos.ne'
    have hdiv := (upperUnipotent F.Carrier).card_subgroup_dvd_card
    rw [card_upperUnipotent] at hdiv
    exact hfcard.trans hdiv
  obtain ⟨f,hfi,hfe⟩ := whole_natural_coordinate_of_moved_section ρ hfaith hi Y A
    (A.nontrivial_iff_ne_bot.mp inferInstance) s F e
  have hfeL (g : L) (w : W) : f (ρ (g : D) w) = binaryNatural 2 (eL g) (f w) := by
    have he : (((eA.symm g : A) : Y) : D) = (g : D) :=
      congrArg Subtype.val (eA.apply_symm_apply g)
    rw [←he]
    exact hfe (eA.symm g) w
  have hz := natural_component_fixed_seed_coordinate_zero S N hN hSN hP hres q hq hc hn ρ v hv
    hL heven hF eL f hfeL
  exact hvne (hfi (hz.trans f.map_zero.symm))
/-- The quasisimple source branch cannot be linear natural over any binary field. -/
private theorem quasisimple_natural_seed_impossible
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsCoatom N)
    (hSN : (S : Subgroup H) ≤ N) (hP : IsMinimalParabolicOver S ⊤)
    (hres : (pResidual 2 N).map N.subtype ≤ (centralizer (V : Set G)).subgroupOf H)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ) (hi : IsIrreducible ρ)
    (v : W) (hvne : v ≠ 0)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (hqs : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ)))
    (F : BinaryField)
    (e : ActionEquiv (s.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      (linearNatural F 2)) : False := by
  let : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)) := hqs
  exact quasisimple_natural_seed_excluded S N hN hSN hP hres q hq hc hn ρ hfaith hi v hvne hv hqs s F
    (quasisimple_linear_two_card_ge_four F e.groupEquiv) e

end CFSG.Quasithin.Chapter3.MaximalBorel

open Subgroup Representation Representation.BinaryOffender
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter3.MaximalBorel
open ChapterB QuasisimpleSource SourceInduction Theory.GroupTheory HigherFieldBorelFixedSpaces

private def firstEquiv {Y K : Type*} [Group Y] [Group K]
    (e : Y ≃* K × K) (A : Subgroup Y)
    (hA : ((⊤ : Subgroup K).prod ⊥).map e.symm.toMonoidHom = A) : A ≃* K :=
  (MulEquiv.subgroupCongr hA.symm).trans
    ((e.symm.subgroupMap ((⊤ : Subgroup K).prod ⊥)).symm.trans
      (((⊤ : Subgroup K).prodEquiv ⊥).trans (MulEquiv.prodUnique.trans Subgroup.topEquiv)))

private theorem firstEquiv_apply {Y K : Type*} [Group Y] [Group K]
    (e : Y ≃* K × K) (A : Subgroup Y)
    (hA : ((⊤ : Subgroup K).prod ⊥).map e.symm.toMonoidHom = A) (a : A) :
    firstEquiv e A hA a = (e a).1 := by rfl

private def secondEquiv {Y K : Type*} [Group Y] [Group K]
    (e : Y ≃* K × K) (A : Subgroup Y)
    (hA : ((⊥ : Subgroup K).prod ⊤).map e.symm.toMonoidHom = A) : A ≃* K :=
  (MulEquiv.subgroupCongr hA.symm).trans
    ((e.symm.subgroupMap ((⊥ : Subgroup K).prod ⊤)).symm.trans
      (((⊥ : Subgroup K).prodEquiv ⊤).trans
        (MulEquiv.prodComm.trans (MulEquiv.prodUnique.trans Subgroup.topEquiv))))

private theorem secondEquiv_apply {Y K : Type*} [Group Y] [Group K]
    (e : Y ≃* K × K) (A : Subgroup Y)
    (hA : ((⊥ : Subgroup K).prod ⊤).map e.symm.toMonoidHom = A) (a : A) :
    secondEquiv e A hA a = (e a).2 := by rfl

private theorem naturalFactor_structure {D : Type*} [Group D] [Finite D]
    (Y : Subgroup D) [Y.Normal] (A : Subgroup Y) [A.Normal]
    (F : BinaryField) (hF : 4 ≤ Nat.card F.Carrier) (e : A ≃* SL(2,F.Carrier)) :
    IsSimpleGroup (A.map Y.subtype) ∧ IsComponent D (A.map Y.subtype) ∧
      2 ∣ Nat.card (A.map Y.subtype) := by
  let : IsSimpleGroup PSL(2,F.Carrier) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  let : IsSimpleGroup SL(2,F.Carrier) := Atlas.RankOneFieldAutomorphisms.slEquivPSL.isSimpleGroup
  let : Group.IsPerfect SL(2,F.Carrier) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier (by omega)
  let : IsQuasisimple SL(2,F.Carrier) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F.Carrier))).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  let em := A.equivMapOfInjective Y.subtype Y.subtype_injective
  let ec := em.symm.trans e
  let : IsSimpleGroup (A.map Y.subtype) := ec.isSimpleGroup
  let : IsQuasisimple (A.map Y.subtype) := IsQuasisimple.of_mulEquiv ec.symm
  refine ⟨inferInstance, ⟨(inferInstance : A.Normal).isSubnormal.trans'
    (inferInstance : Y.Normal).isSubnormal, inferInstance⟩, ?_⟩
  rw [Nat.card_congr ec.toEquiv]
  apply dvd_trans (b := Nat.card (upperUnipotent F.Carrier))
  · rw [card_upperUnipotent, F.card_eq]
    exact dvd_pow_self 2 F.degree_pos.ne'
  · exact (upperUnipotent F.Carrier).card_subgroup_dvd_card

variable {G D W : Type*} [Group G] [Finite G] [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {H V : Subgroup G}

/-- Both literal source factors force the original seed to vanish over a larger field. -/
private theorem paired_natural_fixed_seed_zero
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsCoatom N)
    (hSN : (S : Subgroup H) ≤ N) (hP : IsMinimalParabolicOver S ⊤)
    (hres : (pResidual 2 N).map N.subtype ≤ (centralizer (V : Set G)).subgroupOf H)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) (v : W)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (hF : 4 ≤ Nat.card F.Carrier)
    (c : d.MarkedProduct (linearNatural F 2)) : v = 0 := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  let := d.product.first_normal
  let := d.product.second_normal
  let e₁ := firstEquiv c.action.groupEquiv d.first c.first_eq
  let e₂ := secondEquiv c.action.groupEquiv d.second c.second_eq
  let m₁ := d.first.equivMapOfInjective Y.subtype Y.subtype_injective
  let m₂ := d.second.equivMapOfInjective Y.subtype Y.subtype_injective
  let f := c.action.linearEquiv.toLinearMap.comp (fixed (ρ.comp Y.subtype)).toSubmodule.mkQ
  let f₁ := (LinearMap.fst (ZMod 2) (Fin 2 → F.Carrier) (Fin 2 → F.Carrier)).comp f
  let f₂ := (LinearMap.snd (ZMod 2) (Fin 2 → F.Carrier) (Fin 2 → F.Carrier)).comp f
  have hf : ∀ g : Y, ∀ w, f (ρ (g : D) w) =
      (linearNatural F 2 ((c.action.groupEquiv g).1) ((f w).1),
       linearNatural F 2 ((c.action.groupEquiv g).2) ((f w).2)) := by
    intro g w
    exact (congrArg c.action.linearEquiv
      ((fixed (ρ.comp Y.subtype)).quotientRepresentation_mk g w).symm).trans
        (c.action.intertwines g _)
  have hf₁ : ∀ (g : d.first.map Y.subtype) w,
      f₁ (ρ (g : D) w) = binaryNatural 2 ((m₁.symm.trans e₁) g) (f₁ w) := by
    intro g w
    obtain ⟨a,rfl⟩ := m₁.surjective g
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change (f (ρ (a : Y) w)).1 = linearNatural F 2 (e₁ a) ((f w).1)
    rw [hf]
    rw [show e₁ a = (c.action.groupEquiv a).1 from firstEquiv_apply _ _ _ _]
  have hf₂ : ∀ (g : d.second.map Y.subtype) w,
      f₂ (ρ (g : D) w) = binaryNatural 2 ((m₂.symm.trans e₂) g) (f₂ w) := by
    intro g w
    obtain ⟨a,rfl⟩ := m₂.surjective g
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change (f (ρ (a : Y) w)).2 = linearNatural F 2 (e₂ a) ((f w).2)
    rw [hf]
    rw [show e₂ a = (c.action.groupEquiv a).2 from secondEquiv_apply _ _ _ _]
  obtain ⟨hs₁,hL₁,he₁⟩ := naturalFactor_structure Y d.first F hF e₁
  obtain ⟨hs₂,hL₂,he₂⟩ := naturalFactor_structure Y d.second F hF e₂
  let := hs₁
  let := hs₂
  have h₁ := natural_component_fixed_seed_coordinate_zero S N hN hSN hP hres q hq hc hn ρ v hv
    hL₁ he₁ hF (m₁.symm.trans e₁) f₁ hf₁
  have h₂ := natural_component_fixed_seed_coordinate_zero S N hN hSN hP hres q hq hc hn ρ v hv
    hL₂ he₂ hF (m₂.symm.trans e₂) f₂ hf₂
  have hz : f v = 0 := Prod.ext h₁ h₂
  have hY : Y ≠ ⊥ := by
    let : IsSimpleGroup d.first := m₁.isSimpleGroup
    let : Nontrivial Y := Function.Injective.nontrivial d.first.subtype_injective
    exact (Subgroup.nontrivial_iff_ne_bot Y).mp inferInstance
  have hfix : (fixed (ρ.comp Y.subtype)).toSubmodule = ⊥ :=
    fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hfaith hirr Y hY
  have hquot : (fixed (ρ.comp Y.subtype)).toSubmodule.mkQ v = 0 :=
    c.action.linearEquiv.injective (hz.trans c.action.linearEquiv.map_zero.symm)
  have hm : v ∈ (fixed (ρ.comp Y.subtype)).toSubmodule :=
    (Submodule.Quotient.mk_eq_zero _).mp hquot
  simpa only [hfix, Submodule.mem_bot] using hm

/-- A nonzero source seed restricts the marked paired natural action to the binary field. -/
private theorem paired_natural_field_degree_eq_one
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsCoatom N)
    (hSN : (S : Subgroup H) ≤ N) (hP : IsMinimalParabolicOver S ⊤)
    (hres : (pResidual 2 N).map N.subtype ≤ (centralizer (V : Set G)).subgroupOf H)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) (v : W) (hv0 : v ≠ 0)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2)) : F.degree = 1 := by
  by_contra hdeg
  have hd : 2 ≤ F.degree := by have := F.degree_pos; omega
  have hF : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hd
  exact hv0 (paired_natural_fixed_seed_zero S N hN hSN hP hres q hq hc hn ρ hfaith hirr v hv d F hF c)

end CFSG.Quasithin.Chapter3.MaximalBorel

namespace CFSG.Quasithin.Chapter3.MaximalBorel
open ChapterD ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction Theory.GroupTheory
universe u
variable {G D W : Type u} [Group G] [Finite G] [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {H V : Subgroup G}

theorem small_natural_alternatives_of_fixed_seed
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsCoatom N)
    (hSN : (S : Subgroup H) ≤ N) (hP : IsMinimalParabolicOver S ⊤)
    (hD : IsSQTK KnownSimple.IsKnownSimple H)
    (hres : (pResidual 2 N).map N.subtype ≤ (centralizer (V : Set G)).subgroupOf H)
    (q : H →* D) (hq : Function.Surjective q) (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (hff : IsFFModule ρ) (v : W) (hvne : v ≠ 0)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v) :
    ChiefSmallNaturalAlternatives ρ := by
  have hp := (minimalParabolic_reduced_image S hP q hq hc hn).2
  let := hi
  by_cases hs : Group.IsSolvable D
  · obtain ⟨d,ht,hstable,hr,hgen⟩ := source_solvable_minimalParabolic_factors
      (S.mapSurjective hq) hp hs hc hf hff
    have hcount := d.toSolvableFFFactors.count_eq_one_or_two_of_surjective_threeRank
      q hq (hD.stronglyQuasithin 3 (by decide) (by decide))
    exact Or.inl ((d.toSolvableFFFactors.small_natural_moved_action hf hc hr hcount
      (fun i j => let ⟨t,ht⟩ := ht i j; ⟨t,ht⟩)).wreath)
  · let c : SQTKQuotient KnownSimple.IsKnownSimple D := {
      Cover := H
      kernel := q.ker
      sqtk := hD
      equiv := QuotientGroup.quotientKerEquivOfSurjective q hq }
    rcases nonsolvable_offender_natural_source ρ
      (S.mapSurjective hq) hp hs hf hff hc ⟨c⟩
      with hqs | ⟨d,hd₁,hd₂⟩
    · obtain ⟨hqs,c,hlin | hsym⟩ := hqs
      · obtain ⟨F,⟨e⟩⟩ := hlin
        exact (quasisimple_natural_seed_impossible S N hN hSN hP hres
          q hq hc hn
          ρ hf inferInstance v hvne
          hv hqs c.sectionData F e).elim
      · exact Or.inr (Or.inl ⟨hqs,c,hsym⟩)
    · obtain ⟨t,ht₁,ht₂,hmodel⟩ := source_offender_two_factor_shared_natural ρ
        (S.mapSurjective hq) hp hff hc d
      rcases hmodel with ⟨F,⟨e⟩⟩ | hsym
      · have hdeg := paired_natural_field_degree_eq_one S N hN hSN hP hres
          q hq hc hn
          ρ hf inferInstance v hvne
          hv d F e
        exact (hs (source_pair_degree_one_solvable ρ
          (S.mapSurjective hq) hp hff hc d F hdeg e)).elim
      · exact Or.inr (Or.inr ⟨d,hsym⟩)

end CFSG.Quasithin.Chapter3.MaximalBorel

namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterB Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {H V : Subgroup G}
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]

/-- The actual essential action and original seed satisfy the small natural
alternatives using the supplied maximal Sylow overgroup. -/
theorem EssentialSeedAction.small_natural_alternatives_of_maximal
    {S : Sylow 2 H} {hVH : V ≤ H} (a : EssentialSeedAction H V S hVH)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (N : Subgroup H) (hN : IsCoatom N) (hSN : (S : Subgroup H) ≤ N)
    (hres : (pResidual 2 N).map N.subtype ≤ (centralizer (V : Set G)).subgroupOf H)
    (hff : IsFFModule a.imageRepresentation) :
    ChiefSmallNaturalAlternatives a.imageRepresentation := by
  let := a.irreducible
  exact MaximalBorel.small_natural_alternatives_of_fixed_seed S N hN hSN
    a.original_minimal hH hres a.projection a.projection_surjective
    a.twoCore_eq_bot a.projection_kernel_ne_top a.imageRepresentation
    (imageRepresentation_injective a.representation)
    (imageRepresentation_irreducible a.representation a.irreducible) hff
    a.vector a.vector_ne_zero a.vector_centralizer_fixed

end CFSG.Quasithin.Chapter3
