module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.ModuleSieve.Containing

/-!
# The actual chosen module of a Thompson-generated component

For H=BT, use the literal action on R₂(H) and its quotient by the
centralizer. Thompson generation places B in the offender group. Since
the quotient modulo B is a two-group, the full B.5 classification gives
the quasisimple row. A nonzero fixed point in the actual moved subgroup
selects its nonsplit Irr⁺ case. Sylow invariance then constructs a chosen
module on that same ambient subgroup.

The original local application supplies every group-theoretic premise
and the fixed point from the original flag. No chosen-module hypothesis,
module marking, or point-core movement is assumed here.
Source: Aschbacher--Smith B.5.1(2), B.5.6 and 13.3.14(g), printed
pp.99,105,892--893.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
open Chapter12.Section02 ChapterA.Section04 ChapterB.QuasisimpleSource ChapterB.SourceInduction
open Chapter13.Section03.Noncentrality
open Representation.BinaryOffender.Homogeneous

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The reduced commutator of a normalized Thompson-generated component
with a Sylow supplement and a nonzero fixed part is an actual chosen
module on the original ambient subgroup. -/
theorem chosen_moved_of_thompson_component
    (H B : Subgroup G)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hTH : (T : Subgroup G) ≤ H) (hBH : B ≤ H)
    (hHN : H ≤ normalizer (B : Set G))
    (hB : (B.subgroupOf H).IsCComponent)
    (hqB : IsQuasisimple (B ⧸ pCore 2 B))
    (hfaith : intrinsicSignalizerModule B ≠ ⊥)
    (hgen : H = B ⊔ (T : Subgroup G))
    (hTh : ⁅B,elementaryAbelianMaxJ (T : Subgroup G)⁆ = B)
    (hfixed : ⁅(reducedTwoSubgroup H).map H.subtype,B⁆ ⊓
      centralizer (B : Set G) ≠ ⊥) :
    Nonempty (ChosenModule T B ⁅(reducedTwoSubgroup H).map H.subtype,B⁆) := by
  let W := reducedTwoSubgroup H
  let := (isPReduced_reducedPSubgroup (p := 2) (G := H)).elementary
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let BH := B.subgroupOf H
  let Bq := BH.map q
  let B₀ := Bq.subgroupOf N
  let σ := reducedRepresentation H
  let I := moved σ BH
  let WK := ⁅W.map H.subtype,B⁆
  let S : Sylow 2 H := T.subtype hTH
  let : BH.Normal := normal_subgroupOf_of_le_normalizer hHN
  let : Bq.Normal := (inferInstance : BH.Normal).map q (QuotientGroup.mk'_surjective C)
  let : B₀.Normal := inferInstance
  let eB : BH ≃* B := subgroupOfEquivOfLe hBH
  have hq₀ : IsQuasisimple (BH ⧸ pCore 2 BH) :=
    IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).symm
  have hfaith₀ : intrinsicSignalizerModule BH ≠ ⊥ := by
    intro hz
    apply hfaith
    have hm := intrinsicSignalizerModule_map_of_injective H.subtype H.subtype_injective BH
    rw [map_subgroupOf_eq_of_le hBH,hz,Subgroup.map_bot] at hm
    exact hm
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hTH
  have hgen₀ : ⁅BH,elementaryAbelianMaxJ (S : Subgroup H)⁆ = BH := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hBH,hjmap,hTh]
  obtain ⟨hBq,hcomp,hrows⟩ :=
    component_reduced_offender_entry hH S BH hB hq₀ hfaith₀ hgen₀
  have htop : BH ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hgen.symm
  have hquot : IsPGroup 2 ((H ⧸ C) ⧸ Bq) :=
    isPGroup_quotient_of_sup_eq_top Bq (((T : Subgroup G).subgroupOf H).map q)
      (T.isPGroup'.comap_subtype.map q) (by
        rw [←Subgroup.map_sup,htop,map_top_of_surjective q (QuotientGroup.mk'_surjective C)])
  have hqN : IsPGroup 2 (N ⧸ B₀) := isPGroup_quotient_subgroupOf Bq N hquot
  have hcore : pCore 2 N = ⊥ := offenderSubgroup_twoCore ρ
    (isPReduced_reducedPSubgroup (p := 2) (G := H)).quotient_pCore_eq_bot
  obtain ⟨c⟩ := quasisimple_row_of_component_two_quotient
    (ρ.comp N.subtype) B₀ hcomp hqN hcore hrows
  have hact : σ = ρ.comp q := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) g w).symm
  have hI : I = moved ρ Bq := by
    change moved σ BH = moved ρ (BH.map q)
    rw [hact,moved_comp_map]
  have himage : subspaceImage H I = WK := by
    rw [hI]
    change subspaceImage H (subspaceCommutator ρ ⊤ (BH.map q)) = _
    rw [←NormalElementaryQuotient.commutatorSpace_eq W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) BH]
    change ((⁅W,BH⁆.subgroupOf W).map W.subtype).map H.subtype = _
    rw [map_subgroupOf_eq_of_le (commutator_le_left W BH),map_commutator,
      map_subgroupOf_eq_of_le hBH]
  have hfixedI : I ⊓ fixedSpace σ BH ≠ ⊥ := by
    intro he
    have hh := congrArg (ReducedNormal.subspaceImage H) he
    have heq : σ = ReducedNormal.representation H := by rfl
    rw [heq,ReducedNormal.subspaceImage_inf_fixedSpace H I B hBH,
      ReducedNormal.subspaceImage_bot] at hh
    change subspaceImage H I ⊓ centralizer (B : Set G) = ⊥ at hh
    rw [himage] at hh
    exact hfixed hh
  have hspace : c.sectionData.space.toSubmodule = moved ρ Bq := by
    rw [c.sectionData.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hBq]
  have hn : ¬ IsCompl c.sectionData.space.toSubmodule
      (fixedSpace (ρ.comp N.subtype) (Bq.subgroupOf N)) := by
    rw [hspace,fixedSpace_subgroupOf ρ Bq N hBq]
    intro hh
    apply hfixedI
    rw [hI,hact,fixedSpace_comp_map]
    exact hh.disjoint.eq_bot
  have hirr : IsIrrPlus ρ Bq (moved ρ Bq) := by
    rw [←hspace]
    exact (IsIrrPlus.subgroupOf_iff ρ Bq N hBq _).mp (c.clause_two hn).1
  have hirr' : IsIrrPlus σ BH I := by
    have hh := IsIrrPlus.map_embedding σ ρ q (LinearMap.id : Additive W →ₗ[ZMod 2] Additive W)
      Function.injective_id (fun g w => by rw [hact]; rfl) BH (moved ρ Bq) hirr
    simpa only [Submodule.map_id,←hI] using hh
  have hnormal : (T : Subgroup G).subgroupOf H ≤ normalizer (BH : Set H) :=
    le_normalizer_of_normal
  have hstable : (T : Subgroup G).subgroupOf H ≤ subspaceStabilizer σ I :=
    subspaceCommutator_invariant_normalizer σ
      (by intro t ht v; simp) hnormal
  have hchoice : IsIrrPlusWith σ BH ((T : Subgroup G).subgroupOf H) I := by
    refine ⟨hnormal,hirr'.choose,hirr',?_⟩
    apply le_antisymm
    · rw [orbitSpan_eq_self σ hstable]
      exact iSup_le fun S => iSup_le fun hS => hS.1
    · exact quotientImage_le_homogeneousPart σ hirr'.choose
  have aux : ∀ (H' : Subgroup G) (I' : Submodule (ZMod 2) (Additive (ReducedModule H'))),
      H' = B ⊔ (T : Subgroup G) →
      IsIrrPlusWith (reducedRepresentation H') (B.subgroupOf H')
        ((T : Subgroup G).subgroupOf H') I' →
      subspaceImage H' I' = WK → Nonempty (ChosenModule T B WK) := by
    intro H' I' he hi him
    subst H'
    exact ⟨⟨I',hi,him⟩⟩
  exact aux H I hgen hchoice himage

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LinearThreeSource
