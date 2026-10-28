module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SourceAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.OriginalActionModels
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource
/-!
# C.1.24 selection from the original A₇ plus quotient

The B.5 source classification gives the full natural S₇ module or the
exceptional A₇ four-space. The original component--Sylow join has
characteristic two, and its intrinsic component quotient is quasisimple.
The two C.1.24 seed arguments reconstruct a block unless a nonzero
characteristic subgroup of the original Baumann subgroup is normal.
The original 13.6.16 normalizer obstruction excludes that alternative.

The literal U_K=[W_K,K] then identifies the block module, proving the
ordinary or exceptional A₇ type and transporting it back to K. No action
model, shortness or source-selection callback is assumed.
Source: Aschbacher--Smith C.1.24 and 13.6.22, pp.130--131 and 932.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open ComponentSelection SourceContainment SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ChapterC ChapterC.RankOne.SevenSource
variable {G : Type*} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]

theorem join_block_of_seven_action
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) (hzT : z ∈ Tv T v)
    (hquasi : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : generalizedFitting (K ⊔ Tv T v : Subgroup G) = pCore 2 (K ⊔ Tv T v : Subgroup G))
    (hfB : generalizedFitting (K.subgroupOf (K ⊔ Tv T v)) = pCore 2 (K.subgroupOf (K ⊔ Tv T v)))
    (hred : IsPReduced 2 ((WK K L T z v).subgroupOf (K ⊔ Tv T v)))
    (hmove : ⁅(WK K L T z v).subgroupOf (K ⊔ Tv T v),K.subgroupOf (K ⊔ Tv T v)⁆ ≠ ⊥)
    (P : Sylow 2 (K ⊔ Tv T v : Subgroup G))
    (hprod : ∀ g : (K ⊔ Tv T v : Subgroup G),
      ∃ k ∈ K.subgroupOf (K ⊔ Tv T v),∃ t ∈ (P : Subgroup _),k*t=g)
    (hchar : ∀ C : Subgroup (ChapterB.baumann (P : Subgroup (K ⊔ Tv T v : Subgroup G))),
      C.Characteristic → C≠⊥ → ¬ (C.map (ChapterB.baumann (P : Subgroup (K ⊔ Tv T v : Subgroup G))).subtype).Normal)
    (eC : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 7))
    (m : AlternatingModels.ActionData (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) : IsBlock (K.subgroupOf (K ⊔ Tv T v)) := by
  let H := K ⊔ Tv T v
  let B := K.subgroupOf H
  let W := (WK K L T z v).subgroupOf H
  let U := (UK K L T z v).subgroupOf H
  let D := Gplus K L T z v hL hz
  let C := plusImage K L T z v hL hz K
  let q := joinPlusMap K L T z v hL hz
  have hW := WK_le_join K L T z v hn hLK hzT
  have hq := joinPlusMap_surjective K L T z v hL hz hn hLK
  have hk := joinPlusMap_ker K L T z v hL hz hW
  let : W.Normal := hred.normal
  let : IsElementaryAbelian 2 W := hred.elementary
  let : IsQuasisimple (B ⧸ pCore 2 B) := join_core_quasisimple K T v hquasi
  obtain ⟨hUN,hUE,hcomm,hfix,hUker,hcard⟩ := join_moved_inputs K L T z v hL hz hK hn hLK hzT m
  let : U.Normal := hUN
  let : IsElementaryAbelian 2 U := hUE
  have hfalse : (∃ C : Subgroup (ChapterB.baumann (P : Subgroup H)),
      C.Characteristic ∧ C≠⊥ ∧ (C.map (ChapterB.baumann (P : Subgroup H)).subtype).Normal) → False := by
    rintro ⟨C,hC,hne,hN⟩
    exact hchar C hC hne hN
  rcases m.models with ⟨e,heC⟩ | ⟨hC,hd⟩
  · let q' := e.groupEquiv.toMonoidHom.comp q
    have hq' : Function.Surjective q' := e.groupEquiv.surjective.comp hq
    have hk' : q'.ker = centralizer (W : Set H) :=
      (MonoidHom.ker_comp_of_injective q e.groupEquiv.toMonoidHom e.groupEquiv.injective).trans hk
    have hBq : B.map q' = alternatingGroup (Fin 7) := by
      rw [show B.map q'=(B.map q).map e.groupEquiv.toMonoidHom from (map_map _ _ _).symm]
      rw [joinPlusMap_image K L T z v hL hz K le_sup_left]
      exact heC
    obtain ⟨hc,f,hfi,hfe⟩ := join_natural_inputs K L T z v hL hz hW m e hq' hk'
    exact (Natural.normal_characteristic_or_block_of_natural_seven_linear B W hK.1.2.1
      hf hfB P hprod q' hq' hk' hBq hc f hfi hfe hmove).resolve_left hfalse
  · let E : D ≃* C := (MulEquiv.ofBijective C.subtype
      ⟨C.subtype_injective,by intro d; exact ⟨⟨d,by change d ∈ plusImage K L T z v hL hz K; rw [hC]; trivial⟩,rfl⟩⟩).symm
    let e := E.trans eC
    let q' := e.toMonoidHom.comp q
    have hq' : Function.Surjective q' := e.surjective.comp hq
    have hk' : q'.ker = centralizer (U : Set H) :=
      (MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective).trans hUker
    have hBq : B.map q' = ⊤ := by
      rw [show B.map q'=(B.map q).map e.toMonoidHom from (map_map _ _ _).symm]
      rw [joinPlusMap_image K L T z v hL hz K le_sup_left,hC]
      exact map_top_of_surjective _ e.surjective
    let s : ChapterB.QuasisimpleSource.MovedSection (wkRepresentation K L T z v hL hz) C :=
      ⟨m.sectionData.space,m.sectionData.space_eq,m.sectionData.central,m.sectionData.central_eq⟩
    have hUc : Nat.card U = 2 ^ 4 := by
      rw [joinUK_card K L T z v hL hz hW s,
        Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    have hdim : Module.finrank (ZMod 2) (Additive U) = 4 := by
      apply Nat.pow_right_injective (by decide : 1 < 2)
      have hc : Nat.card (Additive U) = 2 ^ Module.finrank (ZMod 2) (Additive U) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      exact hc.symm.trans ((Nat.card_congr Additive.toMul).trans hUc)
    have hmoveU : ⁅U,B⁆ ≠ ⊥ := by
      rw [hcomm]
      intro hb
      change U = ⊥ at hb
      rw [hb,card_bot] at hUc
      norm_num at hUc
    exact (normal_characteristic_or_block_of_exceptional_seven B U hK.1.2.1 hf hfB P hprod
      q' hq' hk' hBq hdim hmoveU).resolve_left hfalse


theorem join_block_types_of_seven_action
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) (hzT : z ∈ Tv T v)
    (eC : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 7))
    (m : AlternatingModels.ActionData (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (hblock : IsBlock (K.subgroupOf (K ⊔ Tv T v))) :
    IsAlternatingBlock (K.subgroupOf (K ⊔ Tv T v)) 7 ∨
      IsExceptionalA7Block (K.subgroupOf (K ⊔ Tv T v)) := by
  let H := K ⊔ Tv T v
  let B := K.subgroupOf H
  let U := (UK K L T z v).subgroupOf H
  let q := joinPlusMap K L T z v hL hz
  let E : B.map q ≃* alternatingGroup (Fin 7) :=
    (MulEquiv.subgroupCongr (joinPlusMap_image K L T z v hL hz K le_sup_left)).trans eC
  obtain ⟨hN,hE,hm,hfix,hker,hcard⟩ := join_moved_inputs K L T z v hL hz hK hn hLK hzT m
  let : U.Normal := hN
  let : IsElementaryAbelian 2 U := hE
  rcases hcard with hcard | hcard
  · exact Or.inl (ordinary_block_of_full_six B U hblock hm hfix hcard q hker E)
  · exact Or.inr (exceptional_block_of_full_four B U hblock hm hfix hcard q hker E)

private theorem blockModule_card_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : Nat.card (BlockModule A) = Nat.card (BlockModule B) := by
  let E : blockU A ≃* blockU B := (e.subgroupMap (blockU A)).trans
    (MulEquiv.subgroupCongr (RankOne.Solvable.blockU_map_equiv e))
  have hF : (blockFixed A).map E.toMonoidHom = blockFixed B := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro x hx
      exact ⟨E.symm x,(centerCongr e).symm ⟨x,hx⟩ |>.property,E.apply_symm_apply x⟩
  exact Nat.card_congr (QuotientGroup.congr _ _ E hF).toEquiv

private theorem exceptionalBlock_of_equiv {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (e : A ≃* B) (h : IsExceptionalA7Block A) :
    IsExceptionalA7Block B := by
  obtain ⟨hs,⟨a⟩,hc⟩ := h
  refine ⟨RankOne.Solvable.isShort_of_equiv e hs,
    ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans a⟩,?_⟩
  exact (blockModule_card_equiv e).symm.trans hc

omit [IsElementaryAbelian 2 (WK K L T z v)] in
theorem seven_blocks_of_internal
    (h : IsAlternatingBlock (K.subgroupOf (K ⊔ Tv T v)) 7 ∨
      IsExceptionalA7Block (K.subgroupOf (K ⊔ Tv T v))) :
    IsAlternatingBlock K 7 ∨ IsExceptionalA7Block K := by
  let e := subgroupOfEquivOfLe (show K ≤ K ⊔ Tv T v from le_sup_left)
  exact h.imp (RankOne.Solvable.isAlternatingBlock_of_equiv e) (exceptionalBlock_of_equiv e)


open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- C.1.24 selects one of the two A₇ block types from the actual original
plus marking. The original strict normalizer theorem eliminates its only
characteristic-subgroup alternative. -/
theorem alternating_blocks_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (eC : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock K 7 ∨ IsExceptionalA7Block K := by
  obtain ⟨hW,hmoved⟩ := alternating_actionData_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK hL hz eC
  let := hW
  obtain ⟨m⟩ := hmoved
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz (.a7 ⟨eC⟩)).1
  have hzT := (mem_omegaOneCenterAmbient_iff _ _).mp (markedZ_mem_Tv_omega d) |>.1
  have hquasi := (alternating_intrinsic_original_source d V₃ earlier standing hfusion hK hL hz eC).1
  obtain ⟨P,hP,_,hf,hfB,hred,hmove,hprod⟩ := c124_join_preparation_original_source
    d V₃ earlier standing hm hfusion h1332 h63 hK hL hz (.a7 ⟨eC⟩)
  have hc := baumann_characteristic_exclusion_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK P hP
  have hb := join_block_of_seven_action K L (T : Subgroup G) _ _ hL hz hK hn hLK hzT
    hquasi hf hfB hred hmove P hprod hc eC m
  exact seven_blocks_of_internal K (T : Subgroup G) (markedV d.flag.module)
    (join_block_types_of_seven_action K L (T : Subgroup G) _ _ hL hz hK hn hLK hzT eC m hb)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
