module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointRemainingRefinement
public import Theory.SpecificGroups.AlternatingSeven.CentralCoverParabolic

/-!
# Excluding the central A₇ point component

The original point-residual image has order 168 and trivial two-core in
this row. Its small diagonal block is identity, so the actual
M₁*/O₂(M₁*) = SL₂(2) × SL₃(2) marking proves inner action on that image.
The A₇-cover automorphism fixer then makes M₁* fix the cubic center of K₁*.
The literal order-504 parabolic contains this center, contradicting the
centerless quotient of M₁* by its two-core. Relative normality and the
original projection G₁ → G₁/O₂(G₁) are used throughout.

The full catalogue consumer now constructs LocalComponents or a signed
ternary-seven point component with the literal SL₂(7) residual image.
The remaining ternary Sylow-action exclusions, general normalizers and
quasisimple strict-enlargement escape stay with qt-d-1251-local; final
exterior assembly remains with qt-d-1251-source.
Source: Aschbacher--Smith 12.5.3, printed pp.817--818.
-/

public noncomputable section
open Subgroup Theory.GroupTheory AlternatingSeven.CentralCoverParabolic
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

omit [Finite G] in
theorem pointCoreImage_point_residual_normal :
    ((s.pointCoreImage (s.marking.Li 1)).subgroupOf (s.pointCoreImage (s.marking.Mi 1))).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (s.pointCoreImage_mono (s.Li_le_Mi 1))).mpr
  let H := s.marking.Gi 1
  let q := QuotientGroup.mk' (pCore 2 H)
  have hn : (s.marking.Mi 1).subgroupOf H ≤ normalizer ((s.marking.Li 1).subgroupOf H : Set H) := by
    intro m hm x
    exact s.Mi_normalizes_Li 1 hm (x : G)
  exact (map_mono hn).trans (((s.marking.Li 1).subgroupOf H).le_normalizer_map q)

theorem pointCoreImage_point_residual_small_block (b : s.pointCoreImage (s.marking.Li 1)) :
    (s.pointCoreImage_M₁CoreEquiv (QuotientGroup.mk' _
      (inclusion (s.pointCoreImage_mono (s.Li_le_Mi 1)) b))).1 = 1 := by
  obtain ⟨l,rfl⟩ := s.pointCoreImageHom_surjective (s.marking.Li 1) (s.marking.Li_le_Gi 1) b
  have he : inclusion (s.pointCoreImage_mono (s.Li_le_Mi 1))
      (s.pointCoreImageHom _ (s.marking.Li_le_Gi 1) l) =
      s.pointCoreImageHom (s.marking.Mi 1) (show s.marking.Mi 1 ≤ s.marking.Gi 1 from inf_le_right) (inclusion (s.Li_le_Mi 1) l) := by
    apply Subtype.ext
    change (s.pointCoreImageHom _ (s.marking.Li_le_Gi 1) l :
      s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) = _
    rw [s.pointCoreImageHom_apply,s.pointCoreImageHom_apply]
    rfl
  rw [he]
  exact (congrArg Prod.fst (s.pointCoreImage_M₁CoreEquiv_mk
    (inclusion (s.Li_le_Mi 1) l))).trans (s.point_residual_small_block l)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource

namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

theorem point_component_not_seven_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : IsAlternatingCover (K ⧸ pCore 2 K) 7) : False := by
  let Q := s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)
  let C := s.pointCoreImage K
  let B := s.pointCoreImage (s.marking.Li 1)
  let A := s.pointCoreImage (s.marking.Mi 1)
  have hBC : B ≤ C := s.pointCoreImage_mono hLK
  have hBA : B ≤ A := s.pointCoreImage_mono (s.Li_le_Mi 1)
  let ek := s.pointComponentCoreEquivImage hK.1 hN
  let : IsQuasisimple (K ⧸ pCore 2 K) := hm.1
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv ek
  have hzmap : (center (K ⧸ pCore 2 K)).map ek.toMonoidHom = center C := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr ek ⟨y,hy⟩).property
    · intro hx
      exact ⟨ek.symm x,(centerCongr ek.symm ⟨x,hx⟩).property,ek.apply_symm_apply x⟩
  obtain ⟨ez⟩ := hm.2.1
  obtain ⟨ea⟩ := hm.2.2
  let ec : (C ⧸ center C) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.congr _ _ ek hzmap).symm.trans ea
  have hz : Nat.card (center C) = 3 := by
    rw [←Nat.card_congr (centerCongr ek).toEquiv,Nat.card_congr ez.toEquiv]
    simp
  have hc : Nat.card C = 7560 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center C),Nat.card_congr ec.toEquiv,
      hz,nat_card_alternatingGroup,Nat.card_fin]
    norm_num [Nat.factorial]
  obtain ⟨hbcore,hbcard⟩ := twoCore_eq_bot_of_binary_three_section
    (hc ▸ card_dvd_of_le hBC) s.point_residual_image_core_card
  let fb := s.pointCoreImageHom (s.marking.Li 1) (s.marking.Li_le_Gi 1)
  let ebq := (fb.pCoreQuotientEquiv (s.pointCoreImageHom_surjective _ _)
    (s.pointCoreImageHom_ker_isPGroup _ _)).symm.trans (s.marking.LiCoreEquiv 1 (.inl rfl))
  let eb : B ≃* SL(3,ZMod 2) := ((QuotientGroup.quotientBot.symm).trans
    (QuotientGroup.quotientMulEquivOfEq hbcore.symm)).trans ebq
  have hbz : center B = ⊥ := by
    apply eq_bot_iff.mpr
    intro b hb
    have hh : eb b ∈ center SL(3,ZMod 2) := (centerCongr eb ⟨b,hb⟩).property
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 3),mem_bot] at hh
    exact eb.map_eq_one_iff.mp hh
  let f : PerfectCentralCovering.Cover C (alternatingGroup (Fin 7)) :=
    { toMonoidHom := ec.toMonoidHom.comp (QuotientGroup.mk' (center C))
      surjective := ec.surjective.comp (QuotientGroup.mk'_surjective _)
      isPerfect := inferInstance
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ ec.injective,QuotientGroup.ker_mk'] }
  let BC := B.subgroupOf C
  let E := BC.map f.toMonoidHom
  let bc : BC ≃* B := subgroupOfEquivOfLe hBC
  have hj : Function.Injective (f.toMonoidHom.subgroupMap BC) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hxz : (x : C) ∈ center C := f.ker_le_center (congrArg Subtype.val hx)
    have hxb : bc x ∈ center B := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      change (y : Q) * ((x : C) : Q) = ((x : C) : Q) * y
      exact congrArg (fun c : C => (c : Q)) (mem_center_iff.mp hxz ⟨y,hBC y.property⟩)
    rw [hbz,mem_bot] at hxb
    exact bc.map_eq_one_iff.mp hxb
  let be : B ≃* E := bc.symm.trans (MulEquiv.ofBijective (f.toMonoidHom.subgroupMap BC)
    ⟨hj,f.toMonoidHom.subgroupMap_surjective BC⟩)
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup B := eb.isSimpleGroup
  let : IsSimpleGroup E := be.symm.isSimpleGroup
  let : Group.IsPerfect (s.marking.Li 1) := s.marking.Li_perfect 1
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := fb) (s.pointCoreImageHom_surjective _ _)
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective (f := be.toMonoidHom) be.surjective
  have h7 : 7 ∣ Nat.card E := by rw [←Nat.card_congr be.toEquiv,hbcard]; decide
  let : (B.subgroupOf A).Normal := s.pointCoreImage_point_residual_normal
  have hcoreBA : pCore 2 (B.subgroupOf A) = ⊥ := by
    apply (map_injective (f := (subgroupOfEquivOfLe hBA).toMonoidHom) (subgroupOfEquivOfLe hBA).injective)
    rw [pCore_map_iso,hbcore,Subgroup.map_bot]
  have hi : ∀ a : A, ∃ b : B, ∀ y : B,
      (a : Q) * y * (a : Q)⁻¹ = (b : Q) * y * (b : Q)⁻¹ := by
    intro a
    obtain ⟨b,hb⟩ := exists_inner_action_of_twoCore_product (B.subgroupOf A) hcoreBA
      (by rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv,hbcard,
        Atlas.Comparisons.Exceptional.sl3Two_card]) s.pointCoreImage_M₁CoreEquiv
      (fun b => s.pointCoreImage_point_residual_small_block ((subgroupOfEquivOfLe hBA) b)) a
    refine ⟨(subgroupOfEquivOfLe hBA) b,fun y => ?_⟩
    exact congrArg Subtype.val (hb ((subgroupOfEquivOfLe hBA).symm y))
  have hn : A ≤ normalizer (C : Set Q) := by
    let : (K.subgroupOf (s.marking.Gi 1)).Normal := hN
    let : C.Normal := Normal.map inferInstance (QuotientGroup.mk' (pCore 2 (s.marking.Gi 1)))
      (QuotientGroup.mk'_surjective _)
    rw [C.normalizer_eq_top]
    exact le_top
  have hfixed := center_fixed_of_inner_on_subgroup A B C hBC f (Group.IsPerfect.not_isSolvable E) h7 hn hi
  have hJ := (s.pointComponentParabolic_card_index_of_seven_cover h hK hLK hN hm).1
  have hZA : (center C).map C.subtype ≤ A := by
    rintro _ ⟨z,hz',rfl⟩
    exact center_le_of_card_504 ec hz (s.pointComponentParabolic K) hJ hz'
  let zA : center C →* A := (C.subtype.comp (center C).subtype).codRestrict A
    (fun z => hZA (mem_map_of_mem C.subtype z.property))
  have hzAi : Function.Injective zA := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun a : A => (a : Q)) he))
  have hzAr : zA.range ≤ center A := by
    rintro _ ⟨z,rfl⟩
    exact mem_center_iff.mpr fun a => Subtype.ext
      (hfixed (mem_map_of_mem C.subtype z.property) a a.property)
  have hzquot : center (A ⧸ pCore 2 A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : s.pointCoreImage_M₁CoreEquiv x ∈ center (SL(2,ZMod 2) × SL(3,ZMod 2)) :=
      (centerCongr s.pointCoreImage_M₁CoreEquiv ⟨x,hx⟩).property
    rw [Subgroup.center_prod,
      BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 2),
      BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 3)] at hh
    have he : s.pointCoreImage_M₁CoreEquiv x = 1 := Prod.ext hh.1 hh.2
    exact s.pointCoreImage_M₁CoreEquiv.map_eq_one_iff.mp he
  exact no_central_three_of_centerless_twoCore_quotient zA hzAi hz hzAr hzquot

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The full source catalogue now leaves only the two signed ternary-seven rows. -/
theorem point_component_alternative_or_ternary_seven
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1)) (hLK : s.marking.Li 1 ≤ K)
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    LocalComponentAlternative s 1 K ∨ ∃ unitary : Bool,
      (IsPSLSign (K ⧸ pCore 2 K) unitary 3 7 ∨ IsSLSign (K ⧸ pCore 2 K) unitary 3 7) ∧
        Nonempty ((((s.marking.Li 1).subgroupOf K).map
          (QuotientGroup.mk' (pCore 2 K))) ≃* SL(2,ZMod 7)) := by
  rcases s.point_component_alternative_or_refined_remaining h hK hLK hN with ha | hm
  · exact .inl ha
  rcases hm with hm | ⟨hm,_⟩
  · exact .inr hm
  · exact (s.point_component_not_seven_cover h hK hLK hN hm).elim

/-- The original ambient hypotheses construct all four components unless the
same normal point component has one of the two remaining ternary-seven models. -/
theorem local_components_or_ternary_seven
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    Nonempty (LocalComponents s) ∨ ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (s.marking.Gi 1) ∧ s.marking.Li 1 ≤ K ∧
      (K.subgroupOf (s.marking.Gi 1)).Normal ∧ ∃ unitary : Bool,
      (IsPSLSign (K ⧸ pCore 2 K) unitary 3 7 ∨ IsSLSign (K ⧸ pCore 2 K) unitary 3 7) ∧
        Nonempty ((((s.marking.Li 1).subgroupOf K).map
          (QuotientGroup.mk' (pCore 2 K))) ≃* SL(2,ZMod 7)) := by
  obtain ⟨K,⟨hK,hLK,hN⟩,_⟩ := s.exists_unique_normal_local_component h 1 (.inl rfl)
  rcases s.point_component_alternative_or_ternary_seven h hK hLK hN with ha | hm
  · exact .inl ⟨s.localComponentsOfPointAlternative h K hK hLK hN ha⟩
  · exact .inr ⟨K,hK,hLK,hN,hm⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
