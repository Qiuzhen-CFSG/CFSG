module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.NaturalMovement
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.EssentialCartan
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearPairGeneration
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairResidual
import all CFSG.Quasithin.Chapter3.Section01.ChiefAction.PairedBorel
import all CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.PairComponentAlignment

/-!
# Matching natural chief coordinates to the original component

An actual SL₂ component determines the cardinality of its field by its Sylow
two-subgroup order. In the single B.6.9 row, this identifies the field in the
original moved section and bounds the whole module by four dimensions.
In the paired row, component calculus locates the original component on one
axis of the original product marking, again over field four.

The prescribed Sylow exchanges the two source factors. A nontrivial part of
a Sylow-invariant fixed actor therefore projects nontrivially to both axes.
The original component element moves at most two dimensions of its fixed
space, including when the other coordinate is passive. The full covering
maps and the actual source section are retained.

Source: Aschbacher--Smith, proof of 3.1.9(6), printed p.578,
refs/quasithin.pdf. NaturalChiefSelection applies these calculations to the
literal original chief factors.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterB QuasisimpleSource SourceInduction

/-- The Sylow order identifies the field in an actual rank-one marking. -/
theorem binary_field_card_eq_of_sl_two_equiv (F E : BinaryField)
    (e : SL(2,F.Carrier) ≃* SL(2,E.Carrier)) :
    Nat.card F.Carrier = Nat.card E.Carrier := by
  let P := upperUnipotentSylow F.Carrier 2
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  calc
    Nat.card F.Carrier = Nat.card P := (card_upperUnipotent F.Carrier).symm
    _ = Nat.card Q := Nat.card_congr (e.subgroupMap (P : Subgroup _)).toEquiv
    _ = Nat.card (upperUnipotentSylow E.Carrier 2) :=
      Nat.card_congr (Q.equiv (upperUnipotentSylow E.Carrier 2)).toEquiv
    _ = Nat.card E.Carrier := card_upperUnipotent E.Carrier

variable {D W : Type*} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- A field-four component bounds a single original natural chief action by four. -/
theorem single_natural_finrank_le_four_of_component
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (S : Sylow 2 D) (hp : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule ρ) (hc : pCore 2 D = ⊥)
    (hqs : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ)))
    (F : BinaryField)
    (e : ActionEquiv (s.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      (linearNatural F 2))
    {C : Subgroup D} (hC : IsComponent D C)
    (E : BinaryField) (hE : Nat.card E.Carrier = 4) (eC : C ≃* SL(2,E.Carrier)) :
    Module.finrank (ZMod 2) W ≤ 4 := by
  let Y := offenderSubgroup ρ
  let A := generalizedFitting Y
  let := offenderSubgroup_normal ρ
  let := hqs
  have hr := source_quasisimple_fitting_eq_residual S hp Y
    (offender_generation S hp ρ hff hc).2 hqs
  let : (A.map Y.subtype).Normal := hr.1 ▸ (inferInstance : (pResidual 2 D).Normal)
  let := hC.2
  let : Group.IsNilpotent (D ⧸ pResidual 2 D) := (isPGroup_quotient_pResidual 2).isNilpotent
  have hCR : C ≤ pResidual 2 D := le_of_isPerfect_of_solvable_quotient C _
  have hR : IsComponent D (pResidual 2 D) :=
    ⟨(inferInstance : (pResidual 2 D).Normal).isSubnormal,hr.2⟩
  have hCA : C = A.map Y.subtype := (hC.eq_of_le hR hCR).trans hr.1.symm
  let em := A.equivMapOfInjective Y.subtype Y.subtype_injective
  let emC : A ≃* C := em.trans (MulEquiv.subgroupCongr hCA.symm)
  have hF : Nat.card F.Carrier = 4 :=
    (binary_field_card_eq_of_sl_two_equiv F E
      (e.groupEquiv.symm.trans (emC.trans eC))).trans hE
  have hA : A ≠ ⊥ := by
    let : IsSimpleGroup (A ⧸ center A) := hqs.simple
    let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
    exact A.nontrivial_iff_ne_bot.mp inferInstance
  obtain ⟨f,hfi,_⟩ := whole_natural_coordinate_of_moved_section ρ hf hi Y A hA s F e
  have hd := LinearMap.finrank_le_finrank_of_injective hfi
  have ht : Module.finrank (ZMod 2) (Fin 2 → F.Carrier) = 4 := by
    rw [Module.finrank_pi_fintype]
    simp [MathieuCode.NormalizedShadowRows.NaturalMovement.field_four_finrank hF]
  exact ht ▸ hd

/-- A field-four component is one of the two original marked factors. -/
theorem pair_natural_field_four_component
    (ρ : Representation (ZMod 2) D W)
    (S : Sylow 2 D) (hp : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule ρ) (hc : pCore 2 D = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    {C : Subgroup D} (hC : IsComponent D C)
    (E : BinaryField) (hE : Nat.card E.Carrier = 4) (eC : C ≃* SL(2,E.Carrier)) :
    Nat.card F.Carrier = 4 ∧
      (C = d.first.map (offenderSubgroup ρ).subtype ∨
        C = d.second.map (offenderSubgroup ρ).subtype) := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  let := hC.2
  let : Group.IsNilpotent (D ⧸ pResidual 2 D) := (isPGroup_quotient_pResidual 2).isNilpotent
  have hCY : C ≤ Y := (le_of_isPerfect_of_solvable_quotient C (pResidual 2 D)).trans
    (offender_generation S hp ρ hff hc).1
  have hC' := hC.subgroupOf hCY
  have hF := c.linear_field_large F hC'
  let := d.product.first_normal
  let := d.product.second_normal
  let e₁ := Chapter3.firstEquiv c.action.groupEquiv d.first c.first_eq
  let e₂ := Chapter3.secondEquiv c.action.groupEquiv d.second c.second_eq
  have h₁ := (Chapter3.naturalFactor_structure Y d.first F hF e₁).2.1
  have h₂ := (Chapter3.naturalFactor_structure Y d.second F hF e₂).2.1
  rcases SourceInduction.component_le_source_factor d.product hC' with h | h
  · have h' : C ≤ d.first.map Y.subtype := by
      have hm := Subgroup.map_mono (f := Y.subtype) h
      rwa [map_subgroupOf_eq_of_le hCY] at hm
    have he := hC.eq_of_le h₁ h'
    let ef : C ≃* SL(2,F.Carrier) := (MulEquiv.subgroupCongr he).trans
      ((d.first.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e₁)
    exact ⟨(binary_field_card_eq_of_sl_two_equiv F E (ef.symm.trans eC)).trans hE,Or.inl he⟩
  · have h' : C ≤ d.second.map Y.subtype := by
      have hm := Subgroup.map_mono (f := Y.subtype) h
      rwa [map_subgroupOf_eq_of_le hCY] at hm
    have he := hC.eq_of_le h₂ h'
    let ef : C ≃* SL(2,F.Carrier) := (MulEquiv.subgroupCongr he).trans
      ((d.second.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e₂)
    exact ⟨(binary_field_card_eq_of_sl_two_equiv F E (ef.symm.trans eC)).trans hE,Or.inr he⟩

/-- Sylow invariance makes both projections of a nonzero fixed actor nonzero. -/
theorem pair_actor_projections_ne_bot
    (ρ : Representation (ZMod 2) D W)
    (S : Sylow 2 D) (hp : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule ρ) (hc : pCore 2 D = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (J : Subgroup D) (hJ : (S : Subgroup D) ≤ normalizer (J : Set D))
    (hne : J.subgroupOf (offenderSubgroup ρ) ≠ ⊥) :
    (((J.subgroupOf (offenderSubgroup ρ)).map c.action.groupEquiv.toMonoidHom).map
      (MonoidHom.fst SL(2,F.Carrier) SL(2,F.Carrier)) ≠ ⊥) ∧
    (((J.subgroupOf (offenderSubgroup ρ)).map c.action.groupEquiv.toMonoidHom).map
      (MonoidHom.snd SL(2,F.Carrier) SL(2,F.Carrier)) ≠ ⊥) := by
  let Y := offenderSubgroup ρ
  let B := J.subgroupOf Y
  let := offenderSubgroup_normal ρ
  obtain ⟨t,ht₁,ht₂⟩ := source_offender_two_factor_exists_sylow_exchange ρ S hp hff hc d
  have hJ' : J.map (MulAut.conj (t : D)).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (hJ t.property)
  have hY' : Y.map (MulAut.conj (t : D)).toMonoidHom = Y :=
    normal_iff_map_conj_eq.mp (inferInstance : Y.Normal) (t : D)
  have hBY : (J ⊓ Y).map (MulAut.conj (t : D)).toMonoidHom = J ⊓ Y := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (t : D)).injective, hJ', hY']
  have hB : B.map (MulAut.conjNormal (t : D)).toMonoidHom = B := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_map]
    have he : Y.subtype.comp (MulAut.conjNormal (t : D)).toMonoidHom =
        (MulAut.conj (t : D)).toMonoidHom.comp Y.subtype := by ext; rfl
    rw [he, ← Subgroup.map_map]
    simpa only [B, subgroupOf_map_subtype] using hBY
  have hnot₁ : ¬ B ≤ d.first := by
    intro hh
    have hh' := Subgroup.map_mono (f := (MulAut.conjNormal (t : D)).toMonoidHom) hh
    rw [hB,ht₁] at hh'
    exact hne (bot_unique ((le_inf hh hh').trans d.product.disjoint.eq_bot.le))
  have hnot₂ : ¬ B ≤ d.second := by
    intro hh
    have hh' := Subgroup.map_mono (f := (MulAut.conjNormal (t : D)).toMonoidHom) hh
    rw [hB,ht₂] at hh'
    exact hne (bot_unique ((le_inf hh' hh).trans d.product.disjoint.eq_bot.le))
  constructor
  · intro hz
    apply hnot₂
    intro g hg
    rw [← c.second_eq]
    refine ⟨c.action.groupEquiv g,?_,c.action.groupEquiv.symm_apply_apply g⟩
    refine ⟨?_,mem_top _⟩
    exact hz.le (mem_map_of_mem _ (mem_map_of_mem _ hg))
  · intro hz
    apply hnot₁
    intro g hg
    rw [← c.first_eq]
    refine ⟨c.action.groupEquiv g,?_,c.action.groupEquiv.symm_apply_apply g⟩
    refine ⟨mem_top _,?_⟩
    exact hz.le (mem_map_of_mem _ (mem_map_of_mem _ hg))

/-- The original component moves at most two dimensions on the same fixed space. -/
theorem pair_natural_fixed_movement_le_two
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (S : Sylow 2 D) (hp : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule ρ) (hc : pCore 2 D = ⊥)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    {C : Subgroup D} (hC : IsComponent D C)
    (E : BinaryField) (hE : Nat.card E.Carrier = 4) (eC : C ≃* SL(2,E.Carrier))
    (J : Subgroup D) (hJ : (S : Subgroup D) ≤ normalizer (J : Set D))
    (hne : J.subgroupOf (offenderSubgroup ρ) ≠ ⊥)
    (b : D) (hb : b ∈ C) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((ρ b - LinearMap.id).domRestrict (fixedSpace ρ J))) ≤ 2 := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  obtain ⟨hF,hfactor⟩ := pair_natural_field_four_component ρ S hp hff hc d F c hC E hE eC
  have hCY : C ≤ Y := hfactor.elim (fun h => h ▸ map_subtype_le d.first)
    (fun h => h ▸ map_subtype_le d.second)
  let bY : Y := ⟨b,hCY hb⟩
  have hbaxis : (c.action.groupEquiv bY).1 = 1 ∨ (c.action.groupEquiv bY).2 = 1 := by
    rcases hfactor with h | h
    · right
      have hh : bY ∈ d.first := by
        obtain ⟨g,hg,he⟩ := h ▸ hb
        exact (Subtype.ext he : g = bY) ▸ hg
      rw [← c.first_eq] at hh
      obtain ⟨g,hg,he⟩ := hh
      have he' := congrArg c.action.groupEquiv he
      change c.action.groupEquiv (c.action.groupEquiv.symm g) = _ at he'
      rw [c.action.groupEquiv.apply_symm_apply] at he'
      exact (congrArg Prod.snd he').symm.trans hg.2
    · left
      have hh : bY ∈ d.second := by
        obtain ⟨g,hg,he⟩ := h ▸ hb
        exact (Subtype.ext he : g = bY) ▸ hg
      rw [← c.second_eq] at hh
      obtain ⟨g,hg,he⟩ := hh
      have he' := congrArg c.action.groupEquiv he
      change c.action.groupEquiv (c.action.groupEquiv.symm g) = _ at he'
      rw [c.action.groupEquiv.apply_symm_apply] at he'
      exact (congrArg Prod.fst he').symm.trans hg.1
  have hY : Y ≠ ⊥ := offenderSubgroup_ne_bot_of_ff ρ hff
  have hfix : (fixed (ρ.comp Y.subtype)).toSubmodule = ⊥ :=
    fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi Y hY
  have hfi : Function.Injective c.quotientMap := by
    apply LinearMap.ker_eq_bot.mp
    exact c.quotientMap_ker.trans hfix
  obtain ⟨h₁,h₂⟩ := pair_actor_projections_ne_bot ρ S hp hff hc d F c J hJ hne
  have hbound := MathieuCode.NormalizedShadowRows.NaturalMovement.pair_coordinates_movement_le
    (ρ.comp Y.subtype) c.action.groupEquiv.toMonoidHom c.quotientMap hfi
    c.quotientMap_action (J.subgroupOf Y) h₁ h₂ bY hbaxis
  rw [MathieuCode.NormalizedShadowRows.NaturalMovement.field_four_finrank hF] at hbound
  have hsub : fixedSpace ρ J ≤ fixedSpace (ρ.comp Y.subtype) (J.subgroupOf Y) := by
    rw [fixedSpace_comp_map,subgroupOf_map_subtype]
    exact fixedSpace_antitone ρ inf_le_left
  have hle := MathieuCode.NormalizedShadowRows.NaturalMovement.movement_le_of_injective
    ρ ρ b b (LinearMap.id) Function.injective_id (fun _ => rfl)
    (fixedSpace ρ J) (fixedSpace (ρ.comp Y.subtype) (J.subgroupOf Y))
    (fun _ hx => hsub hx)
  exact hle.trans hbound

/-- B.6.9 and the original component bound the large non-small chief action. -/
theorem non_small_natural_fixed_movement_le_two
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (S : Sylow 2 D) (hp : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule ρ) (hc : pCore 2 D = ⊥)
    (hnat : ChiefNaturalAlternatives ρ) (hsmall : ¬ ChiefSmallNaturalAlternatives ρ)
    (hdim : 5 ≤ Module.finrank (ZMod 2) W)
    {C : Subgroup D} (hC : IsComponent D C)
    (E : BinaryField) (hE : Nat.card E.Carrier = 4) (eC : C ≃* SL(2,E.Carrier))
    (J : Subgroup D) (hJ : (S : Subgroup D) ≤ normalizer (J : Set D))
    (A : Subgroup D) (hA : IsBestOffender ρ A) (hAJ : A ≤ J)
    (b : D) (hb : b ∈ C) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((ρ b - LinearMap.id).domRestrict (fixedSpace ρ J))) ≤ 2 := by
  rcases hnat with hs | ⟨hq,c,hm⟩ | ⟨d,hm⟩
  · exact (hsmall (Or.inl hs)).elim
  · rcases hm with ⟨F,⟨e⟩⟩ | hs
    · have hd := single_natural_finrank_le_four_of_component
        ρ hf hi S hp hff hc hq c.sectionData F e hC E hE eC
      omega
    · exact (hsmall (Or.inr (Or.inl ⟨hq,c,hs⟩))).elim
  · rcases hm with ⟨F,⟨e⟩⟩ | hs
    · have hne : J.subgroupOf (offenderSubgroup ρ) ≠ ⊥ := by
        intro hz
        have he := congrArg (Subgroup.map (offenderSubgroup ρ).subtype) hz
        rw [subgroupOf_map_subtype,Subgroup.map_bot] at he
        exact hA.1.1 (bot_unique ((le_inf hAJ (hA.le_offenderSubgroup ρ)).trans he.le))
      exact pair_natural_fixed_movement_le_two ρ hf hi S hp hff hc d F e hC E hE eC J hJ hne b hb
    · exact (hsmall (Or.inr (Or.inr ⟨d,hs⟩))).elim

end CFSG.Quasithin.Chapter8.MathieuShadowRows
