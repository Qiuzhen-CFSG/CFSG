module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.Quotient
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.TwoAndFive.LinearTwo
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import Theory.Representation.BinaryOffender.Stability
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The marked symmetric-five seed comparison

The natural A₅ constituent has vanishing first cohomology, as does its dual.
The existing cohomology splitting theorem therefore removes the central kernel
when the source moved space is the whole seed. This lifts the complete marked
S₅ action from the section to the seed. Minimality then selects one transposition
from the source commuting-transposition offender family, proving order two for
the actual offender image.

The image-rank equality supplies faithful restriction to the original offender.
Its image is disjoint from L⁺, so faithfulness on L makes the literal quotient
map injective on LA. The final marking uses that map and the original component
inclusion. Neither U=[V,L] nor A≤L is assumed.

The only remaining moved-space input is the explicitly permitted hypothesis
produced by qt-b05-compared-double-three and discharged by the comparison owner.
No additional A.1.31, B.4 or I.1.6 implication is assumed here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.3.2,
B.4.2(5), B.5.1(1i), B.5.9 and I.1.6(1), printed pp.83–84, 86, 99, 107 and 408.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
namespace TwoAndFive
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) D W}

omit [Finite D] in
/-- On the marked natural S₅ module, equal-weight minimality selects one
transposition from the full commuting-transposition family. -/
theorem minimal_symmetricFive_card (e : ActionEquiv σ (BinaryPermutation.naturalRepresentation (Fin 5)))
    {B : Subgroup D} (hB : IsMinimalBestOffender σ B)
    (hfamily : ChapterB.Offenders.CaseAFamily 5 (B.map e.groupEquiv.toMonoidHom)) :
    Nat.card B = 2 := by
  have hnot : ¬ IsStrongFFModule σ := by
    rintro ⟨C, hC, hc⟩
    have ho : IsOffender σ C := ⟨hC, hc.le⟩
    have ht := ho.map_equivariant σ _ e.groupEquiv.toMonoidHom e.groupEquiv.injective
      e.linearEquiv e.intertwines
    apply ChapterB.Offenders.Odd.not_isStrongOffender_natural (Or.inl rfl) _
    refine ⟨ht.1, ?_⟩
    rw [← fixedCodim_map_equivariant σ _ e.groupEquiv.toMonoidHom e.linearEquiv
      e.intertwines, rank_map_injective _ e.groupEquiv.injective]
    exact hc
  obtain ⟨m, hm, hmn, g, hg⟩ := hfamily
  let C := (ChapterB.Offenders.disjointTranspositions 5 1).map (MulAut.conj g).toMonoidHom
  have hCB : C ≤ B.map e.groupEquiv.toMonoidHom := by
    rw [hg]
    exact Subgroup.map_mono (ChapterB.Offenders.disjointTranspositions_mono hm)
  have hC : IsBestOffender (BinaryPermutation.naturalRepresentation (Fin 5)) C :=
    (ChapterB.Offenders.Odd.isBestOffender_disjointTranspositions (n := 5) (m := 1)
      (Or.inl rfl) (by decide) (by decide)).2.2.2.map_conj _ g
  let C' := C.map e.groupEquiv.symm.toMonoidHom
  have hC'B : C' ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb, he⟩ := hCB hx
    change e.groupEquiv.symm x ∈ B
    rw [← he]
    change e.groupEquiv.symm (e.groupEquiv b) ∈ B
    rw [MulEquiv.symm_apply_apply]
    exact hb
  let es := ExtensionConsequences.actionSymm e
  have hC'o : IsOffender σ C' :=
    (hC.isOffender _).map_equivariant _ σ e.groupEquiv.symm.toMonoidHom
      e.groupEquiv.symm.injective e.linearEquiv.symm es.intertwines
  have hc : fixedCodim σ C' = rank C' :=
    le_antisymm hC'o.2 (Nat.le_of_not_gt (fun ht => hnot ⟨C', hC'o.1, ht⟩))
  have hb : fixedCodim σ B = rank B := ((isBestOffender_iff_of_not_strong σ hnot B).mp hB.1).2
  have hC'b : IsBestOffender σ C' :=
    (isBestOffender_iff_of_not_strong σ hnot C').mpr ⟨hC'o.1, hc⟩
  have heq : C' = B := by
    apply hB.2 C' hC'b
    refine ⟨hC'B, ?_⟩
    have h₁ := fixedCodim_add_finrank σ C'
    have h₂ := fixedCodim_add_finrank σ B
    unfold weight
    omega
  rw [← heq]
  calc
    Nat.card C' = Nat.card C :=
      (Nat.card_congr (C.equivMapOfInjective e.groupEquiv.symm.toMonoidHom
        e.groupEquiv.symm.injective).toEquiv).symm
    _ = Nat.card (ChapterB.Offenders.disjointTranspositions 5 1) :=
      (Nat.card_congr ((ChapterB.Offenders.disjointTranspositions 5 1).equivMapOfInjective
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).symm
    _ = 2 := ChapterB.Offenders.Odd.card_disjointTranspositions (Or.inl rfl) (by decide)
/-- Odd alternating cohomology removes the central kernel on the whole moved
seed. The source marking is retained by the quotient intertwiner. -/
noncomputable def symmetricFive_fullMarked {X : Subgroup D}
    (s : MovedSection σ X) (ht : s.space.toSubmodule = ⊤)
    (hi : IsIrrPlus σ X s.space.toSubmodule)
    (mark : MarkedActionEquiv s.action (offenderSubgroup s.action) X
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (hj : offenderSubgroup s.action = ⊤) :
    MarkedActionEquiv σ ⊤ X (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5)) := by
  have hc := ExtensionConsequences.symmetricOdd_isCompl s hi (Or.inl rfl) mark
  have hz : fixedSpace σ X = ⊥ := by
    have hd := hc.disjoint
    rw [ht] at hd
    exact disjoint_top.mp hd.symm
  have hk : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hv : x.val ∈ fixedSpace σ X := fun l => congrArg Subtype.val (hx l)
    rw [hz] at hv
    exact hv
  let q : s.space.toSubmodule ≃ₗ[ZMod 2] (s.space.toSubmodule ⧸ s.central.toSubmodule) :=
    LinearEquiv.ofBijective s.central.toSubmodule.mkQ
      ⟨(LinearMap.ker_eq_bot).mp (by rw [Submodule.ker_mkQ, hk]),
        s.central.toSubmodule.mkQ_surjective⟩
  let E := (fullSectionSpaceEquiv s ht).trans q
  let f : (⊤ : Subgroup D) ≃* offenderSubgroup s.action := MulEquiv.subgroupCongr hj.symm
  exact {
    action := {
      groupEquiv := f.trans mark.action.groupEquiv
      linearEquiv := E.trans mark.action.linearEquiv
      intertwines := fun g v => mark.action.intertwines (f g) (E v) }
    contained := le_top
    subgroupEquiv := mark.subgroupEquiv
    compatible := fun l => mark.compatible l }

/-- Forgetting only the redundant top-subgroup carrier in a full marking. -/
noncomputable def fullMarkedAction {X : Subgroup D}
    (mark : MarkedActionEquiv σ ⊤ X (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) :
    ActionEquiv σ (BinaryPermutation.naturalRepresentation (Fin 5)) where
  groupEquiv := Subgroup.topEquiv.symm.trans mark.action.groupEquiv
  linearEquiv := mark.action.linearEquiv
  intertwines g v := mark.action.intertwines ⟨g, Subgroup.mem_top g⟩ v

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
/-- The full marked symmetric action has a proper alternating component. -/
theorem fullMarked_component_ne_top {X : Subgroup D}
    (mark : MarkedActionEquiv σ ⊤ X (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) : X ≠ ⊤ := by
  intro hx
  obtain ⟨g, hg⟩ := mark.action.groupEquiv.surjective (Equiv.swap (0 : Fin 5) 1)
  let l : X := ⟨g.val, hx.symm ▸ Subgroup.mem_top g.val⟩
  have he := mark.compatible l
  have hm : mark.action.groupEquiv g ∈ alternatingGroup (Fin 5) := by
    rw [show mark.action.groupEquiv g = (mark.subgroupEquiv l : Equiv.Perm (Fin 5)) from he]
    exact (mark.subgroupEquiv l).property
  rw [hg] at hm
  simp [Equiv.Perm.mem_alternatingGroup] at hm

omit [Finite D] in
/-- A subgroup of prime order disjoint from a subgroup it does not lie in. -/
theorem order_two_disjoint {B X : Subgroup D} (hb : Nat.card B = 2) (hn : ¬ B ≤ X) :
    Disjoint B X := by
  let : Fact (Nat.card B).Prime := ⟨hb ▸ Nat.prime_two⟩
  rcases (X.subgroupOf B).eq_bot_or_eq_top_of_prime_card with h | h
  · apply Subgroup.disjoint_def.mpr
    intro b hb hx
    have he : (⟨b, hb⟩ : B) = 1 := h.le hx
    exact congrArg Subtype.val he
  · exfalso
    apply hn
    intro b hb
    have hx : (⟨b, hb⟩ : B) ∈ X.subgroupOf B := h.symm ▸ Subgroup.mem_top _
    exact hx

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
theorem generated_of_commutator {X B : Subgroup D}
    (hb : IsBestOffender σ B) (hc : ⁅X, B⁆ = X) (hg : X ⊔ B = ⊤) :
    offenderSubgroup σ = ⊤ := by
  let J := offenderSubgroup σ
  let : J.Normal := offenderSubgroup_normal _
  have hBJ : B ≤ J := le_iSup_of_le _ (le_iSup_of_le ⟨hb, le_top⟩ le_rfl)
  have hXJ : X ≤ J := by
    rw [← hc]
    exact (commutator_mono le_rfl hBJ).trans (commutator_le_right _ _)
  exact top_unique (hg.symm ▸ sup_le hXJ hBJ)

end TwoAndFive

universe u v
variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)

omit [Finite G] in
/-- The quotient section is generated by its actual offenders: its offender
subgroup contains A⁺ and [L⁺,A⁺]=L⁺. -/
theorem seed_section_generated
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hb : IsBestOffender s.action (seedOffenderImage ρ hLA)) :
    offenderSubgroup s.action = ⊤ :=
  TwoAndFive.generated_of_commutator hb (Preparation.seed_commutator ρ hLA)
    (Preparation.seed_images_generate ρ hLA)

include p in
/-- Faithful restriction to L and A and disjointness of their quotient images
make the literal quotient map injective on LA. Normality is only used for L. -/
theorem seedQuotientMap_injective_of_disjoint
    (hk : subspaceKernel ρ (naturalSeedSpace ρ L A) A = ⊥)
    (hd : Disjoint (seedOffenderImage ρ hLA) (seedComponentImage ρ hLA)) :
    Function.Injective (seedQuotientMap ρ hLA) := by
  let : L.Normal := p.component_normal
  let q := seedQuotientMap ρ hLA
  apply (MonoidHom.ker_eq_bot_iff q).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  obtain ⟨l, hl, a, ha, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp g.property
  let l₀ : (L ⊔ A : Subgroup G) := ⟨l, (le_sup_left : L ≤ L ⊔ A) hl⟩
  let a₀ : (L ⊔ A : Subgroup G) := ⟨a, (le_sup_right : A ≤ L ⊔ A) ha⟩
  have hmul : l₀ * a₀ = g := Subtype.ext hprod
  have hqg : q g = 1 := MonoidHom.mem_ker.mp hg
  have hmulq : q l₀ * q a₀ = 1 := by rw [← map_mul, hmul, hqg]
  have hqaL : q a₀ ∈ seedComponentImage ρ hLA := by
    have he : q a₀ = (q l₀)⁻¹ := by
      calc
        q a₀ = (q l₀)⁻¹ * (q l₀ * q a₀) := by group
        _ = (q l₀)⁻¹ := by rw [hmulq, mul_one]
    rw [he]
    exact Subgroup.inv_mem _ ⟨l₀, hl, rfl⟩
  have hqa : q a₀ = 1 := Subgroup.disjoint_def.mp hd ⟨a₀, ha, rfl⟩ hqaL
  have haz : a = 1 := hk.le ⟨ha, by
    intro v hv
    change (seedQuotientAction ρ hLA (seedQuotientMap ρ hLA a₀) ⟨v, hv⟩).val = v
    rw [show seedQuotientMap ρ hLA a₀ = 1 from hqa, map_one, Module.End.one_apply]⟩
  have hql : q l₀ = 1 := by simpa only [hqa, mul_one] using hmulq
  have hlz : l = 1 := by
    have he : (⟨l, hl⟩ : L) = 1 := p.component_faithful (by
      apply LinearMap.ext
      intro v
      simp only [map_one, Module.End.one_apply]
      change seedQuotientAction ρ hLA (seedQuotientMap ρ hLA l₀) v = v
      rw [show seedQuotientMap ρ hLA l₀ = 1 from hql, map_one, Module.End.one_apply])
    exact congrArg Subtype.val he
  apply Subtype.ext
  change g.val = 1
  rw [← hprod, hlz, haz, one_mul]

noncomputable def seedOriginalMarked
    (hq : Function.Injective (seedQuotientMap ρ hLA))
    (mark : MarkedActionEquiv (seedQuotientAction ρ hLA) ⊤ (seedComponentImage ρ hLA)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    MarkedActionEquiv (seedSubrepresentation ρ hLA).toRepresentation
      ⊤ (L.subgroupOf (L ⊔ A))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)) := by
  let e : (L ⊔ A : Subgroup G) ≃* SeedQuotient ρ hLA :=
    MulEquiv.ofBijective (seedQuotientMap ρ hLA) ⟨hq, QuotientGroup.mk'_surjective _⟩
  let f : (⊤ : Subgroup (L ⊔ A : Subgroup G)) ≃* (⊤ : Subgroup (SeedQuotient ρ hLA)) :=
    Subgroup.topEquiv.trans (e.trans Subgroup.topEquiv.symm)
  let eL := (Subgroup.subgroupOfEquivOfLe (show L ≤ L ⊔ A from le_sup_left)).trans
    (seedComponentEquiv ρ hLA p)
  exact {
    action := {
      groupEquiv := f.trans mark.action.groupEquiv
      linearEquiv := mark.action.linearEquiv
      intertwines := fun g v => mark.action.intertwines (f g) v }
    contained := le_top
    subgroupEquiv := eL.trans mark.subgroupEquiv
    compatible := fun l => mark.compatible (eL l) }


include p in
/-- The S₅ row reconstructs the original LA marking. The order-two conclusion
uses minimality of the literal offender image, not an assumed order or A≤L. -/
theorem compared_symmetricFive_of_source
    (hyp : FFHypothesis K ρ) (hA : IsMinimalBestOffender ρ A)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      c.sectionData.space.toSubmodule)
    (_hf : Function.Injective c.sectionData.action)
    (_hir : IsIrreducible (c.sectionData.action.comp (seedComponentImage ρ hLA).subtype))
    (_hex : seedComponentImage ρ hLA = ⊤ ∨
      (∀ T : Sylow 2 (SeedQuotient ρ hLA), seedComponentImage ρ hLA ⊔ (T : Subgroup _) = ⊤) ∧
        OuterNaturalAction c.sectionData.action)
    (mark : MarkedActionEquiv c.sectionData.action (offenderSubgroup c.sectionData.action)
      (seedComponentImage ρ hLA) (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5)))
    (ho : ∀ B, IsBestOffender c.sectionData.action B → ChapterB.Offenders.CaseAFamily 5
      ((B.subgroupOf (offenderSubgroup c.sectionData.action)).map mark.action.groupEquiv.toMonoidHom))
    (hq : quadraticRatio c.sectionData.action = 1) : ComparedCase ρ hLA := by
  let := hyp.finite_module
  obtain ⟨hb, he⟩ := seed_section_ratio_one ρ hLA p c.sectionData hq
  have hj := seed_section_generated ρ hLA c.sectionData hb
  let mark₀ := TwoAndFive.symmetricFive_fullMarked c.sectionData
    (c.sectionData.space_eq.trans hm) hi mark hj
  let e := TwoAndFive.fullMarkedAction mark₀
  have hmap : (seedOffenderImage ρ hLA).map e.groupEquiv.toMonoidHom =
      ((seedOffenderImage ρ hLA).subgroupOf (offenderSubgroup c.sectionData.action)).map
        mark.action.groupEquiv.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hj.symm ▸ Subgroup.mem_top b⟩, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.val, hb, rfl⟩
  have hfamily : ChapterB.Offenders.CaseAFamily 5
      ((seedOffenderImage ρ hLA).map e.groupEquiv.toMonoidHom) := hmap.symm ▸ ho _ hb
  have hcard : Nat.card (seedOffenderImage ρ hLA) = 2 :=
    TwoAndFive.minimal_symmetricFive_card e p.minimal hfamily
  have hn : ¬ seedOffenderImage ρ hLA ≤ seedComponentImage ρ hLA := by
    intro h
    apply TwoAndFive.fullMarked_component_ne_top mark₀
    exact top_unique ((Preparation.seed_images_generate ρ hLA).symm ▸ sup_le le_rfl h)
  have hd := TwoAndFive.order_two_disjoint hcard hn
  obtain ⟨hk, _, _⟩ := seed_equality_of_image_rank ρ hyp.faithful hA hLA p.noncentral he
  have hqi := seedQuotientMap_injective_of_disjoint ρ hLA p hk hd
  exact .symmetricFive (seedOriginalMarked ρ hLA p hqi mark₀) hcard he

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
