module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Stable
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Geometry
public import Theory.Representation.BinaryOffender.ProductSplitting
public import Theory.Representation.BinaryOffender.StableRestriction
public import Theory.Representation.BinaryPermutation.FivePairExtension
import Mathlib.Tactic

/-!
# Stable offenders on the paired S₅ natural module

The independent coordinate actions have no strong offenders, so every
actual offender splits as the product of its projections. Equal-weight
restriction to either active axis yields the single-factor stable family.
Consequently a stable family active on both axes generates the actual
product of the transposition four-groups in a product Sylow subgroup.
Their natural fixed space has exactly that product as pointwise fixer.

Source: Aschbacher–Smith C.1.24 and E.2.3(3), pp.130–131 and216–217.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open BinaryPermutation ChapterB.Offenders
abbrev Core := BinaryPermutation.FivePair.Core
abbrev action := BinaryPermutation.FivePair.action

theorem core_not_strong : ¬ IsStrongFFModule (coreRepresentation (Fin 5)) := by
  rintro ⟨A,hA⟩
  exact Odd.not_isStrongOffender_core (Or.inl rfl) A hA

theorem not_strong : ¬ IsStrongFFModule action :=
  product_not_strong _ _ core_not_strong core_not_strong

theorem offender_factors {A : Subgroup (Sym × Sym)} (hA : IsOffender action A) :
    A = (A.map (MonoidHom.fst Sym Sym)).prod (A.map (MonoidHom.snd Sym Sym)) ∧
    (A.map (MonoidHom.fst Sym Sym) = ⊥ ∨ CaseAFamily 5 (A.map (MonoidHom.fst Sym Sym))) ∧
    (A.map (MonoidHom.snd Sym Sym) = ⊥ ∨ CaseAFamily 5 (A.map (MonoidHom.snd Sym Sym))) := by
  obtain ⟨he,h₁,h₂⟩ := offender_product_of_not_strong _ _ core_not_strong core_not_strong hA
  have hc {B : Subgroup Sym} (hb : IsOffender (coreRepresentation (Fin 5)) B) : CaseAFamily 5 B := by
    exact (Odd.isBestOffender_core_iff_caseAFamily (Or.inl rfl) B).mp
      ((isBestOffender_iff_of_not_strong _ core_not_strong B).mpr
        ⟨hb.1, le_antisymm hb.2 (Nat.le_of_not_gt (fun h => core_not_strong ⟨B,hb.1,h⟩))⟩)
  exact ⟨he,h₁.imp id hc,h₂.imp id hc⟩

theorem offender_le_transposition_product
    (P Q : Subgroup Sym) (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (hDP : D 5 ≤ P) (hDQ : D 5 ≤ Q)
    {A : Subgroup (Sym × Sym)} (hA : IsOffender action A) (hAP : A ≤ P.prod Q) :
    A ≤ (D 5).prod (D 5) := by
  obtain ⟨he,h₁,h₂⟩ := offender_factors hA
  have hf : A.map (MonoidHom.fst Sym Sym) ≤ P := by
    rintro _ ⟨a,ha,rfl⟩; exact (hAP ha).1
  have hs : A.map (MonoidHom.snd Sym Sym) ≤ Q := by
    rintro _ ⟨a,ha,rfl⟩; exact (hAP ha).2
  rw [he]
  apply Subgroup.prod_mono
  · rcases h₁ with h | h
    · rw [h]; exact bot_le
    · exact Odd.caseAFamily_le_D_of_isPGroup (Or.inl rfl) hP hDP h hf
  · rcases h₂ with h | h
    · rw [h]; exact bot_le
    · exact Odd.caseAFamily_le_D_of_isPGroup (Or.inl rfl) hQ hDQ h hs

theorem fixed_space_fixer (g : Sym × Sym)
    (hg : ∀ v ∈ fixedSpace action ((D 5).prod (D 5)), action g v = v) :
    g ∈ (D 5).prod (D 5) := by
  constructor
  · apply fixed_space_fixer_le_D
    intro v hv
    have hx : (v,0) ∈ fixedSpace action ((D 5).prod (D 5)) := by
      intro a
      exact Prod.ext (hv ⟨a.val.1,a.property.1⟩) (map_zero (coreRepresentation (Fin 5) a.val.2))
    exact congrArg Prod.fst (hg (v,0) hx)
  · apply fixed_space_fixer_le_D
    intro v hv
    have hx : (0,v) ∈ fixedSpace action ((D 5).prod (D 5)) := by
      intro a
      exact Prod.ext (map_zero (coreRepresentation (Fin 5) a.val.1)) (hv ⟨a.val.2,a.property.2⟩)
    exact congrArg Prod.snd (hg (0,v) hx)

theorem fixedCodim_axis_left (A : Subgroup Sym) :
    fixedCodim action (A.map (MonoidHom.inl Sym Sym)) =
      fixedCodim (coreRepresentation (Fin 5)) A := by
  rw [fixedCodim_prod]
  change Module.finrank (ZMod 2) (Core ⧸ fixedSpace
    ((coreRepresentation (Fin 5)).comp (MonoidHom.fst Sym Sym)) _) +
    Module.finrank (ZMod 2) (Core ⧸ fixedSpace
    ((coreRepresentation (Fin 5)).comp (MonoidHom.snd Sym Sym)) _) = _
  rw [fixedSpace_comp_map, fixedSpace_comp_map, map_map, map_map]
  have h₁ : (MonoidHom.fst Sym Sym).comp (MonoidHom.inl Sym Sym) = MonoidHom.id Sym := rfl
  have h₂ : (MonoidHom.snd Sym Sym).comp (MonoidHom.inl Sym Sym) = 1 := rfl
  have hb : A.map (1 : Sym →* Sym) = ⊥ := by ext x; simp
  rw [h₁,h₂,Subgroup.map_id,hb,fixedSpace_bot]
  simp only [fixedCodim, add_eq_left]
  have ht := (⊤ : Submodule (ZMod 2) Core).finrank_quotient_add_finrank
  simpa using ht

theorem fixedCodim_axis_right (A : Subgroup Sym) :
    fixedCodim action (A.map (MonoidHom.inr Sym Sym)) =
      fixedCodim (coreRepresentation (Fin 5)) A := by
  rw [fixedCodim_prod]
  change Module.finrank (ZMod 2) (Core ⧸ fixedSpace
    ((coreRepresentation (Fin 5)).comp (MonoidHom.fst Sym Sym)) _) +
    Module.finrank (ZMod 2) (Core ⧸ fixedSpace
    ((coreRepresentation (Fin 5)).comp (MonoidHom.snd Sym Sym)) _) = _
  rw [fixedSpace_comp_map, fixedSpace_comp_map, map_map, map_map]
  have h₁ : (MonoidHom.fst Sym Sym).comp (MonoidHom.inr Sym Sym) = 1 := rfl
  have h₂ : (MonoidHom.snd Sym Sym).comp (MonoidHom.inr Sym Sym) = MonoidHom.id Sym := rfl
  have hb : A.map (1 : Sym →* Sym) = ⊥ := by ext x; simp
  rw [h₁,h₂,Subgroup.map_id,hb,fixedSpace_bot]
  simp only [fixedCodim, add_eq_right]
  have ht := (⊤ : Submodule (ZMod 2) Core).finrank_quotient_add_finrank
  simpa using ht

private theorem offender_weight {A : Subgroup (Sym × Sym)} (hA : IsOffender action A) :
    weight action A = Module.finrank (ZMod 2) (Core × Core) := by
  have hc := fixedCodim_add_finrank action A
  have hl := hA.2
  have hu : rank A ≤ fixedCodim action A :=
    Nat.le_of_not_gt (fun h => not_strong ⟨A,hA.1,h⟩)
  unfold weight
  rw [←le_antisymm hl hu]
  exact hc

theorem stable_downward {P : Set (Subgroup (Sym × Sym))} (hP : IsStable action P)
    {A B : Subgroup (Sym × Sym)} (hA : A ∈ P) (hB : IsBestOffender action B)
    (hBA : B ≤ A) : B ∈ P := by
  exact hP.2.2.2 A hA B hB.1 ⟨hBA,
    (offender_weight (hB.isOffender action)).trans
      (offender_weight ((hP.2.1 A hA).isOffender action)).symm⟩

private theorem inl_injective : Function.Injective (MonoidHom.inl Sym Sym) :=
  fun _ _ h => congrArg Prod.fst h
private theorem inr_injective : Function.Injective (MonoidHom.inr Sym Sym) :=
  fun _ _ h => congrArg Prod.snd h

private theorem best_of_offender {A : Subgroup Sym}
    (hA : IsOffender (coreRepresentation (Fin 5)) A) :
    IsBestOffender (coreRepresentation (Fin 5)) A := by
  exact (isBestOffender_iff_of_not_strong _ core_not_strong A).mpr
    ⟨hA.1,le_antisymm hA.2 (Nat.le_of_not_gt (fun h => core_not_strong ⟨A,hA.1,h⟩))⟩

theorem stable_left_axis {P : Set (Subgroup (Sym × Sym))} (hP : IsStable action P)
    (hne : ∃ A ∈ P, A.map (MonoidHom.fst Sym Sym) ≠ ⊥) :
    IsStable (coreRepresentation (Fin 5))
      {B : Subgroup Sym | B.map (MonoidHom.inl Sym Sym) ∈ P} := by
  apply hP.restrict_of_fixedCodim _ _ (MonoidHom.inl Sym Sym) inl_injective
    (fun A => (fixedCodim_axis_left A).symm)
  obtain ⟨A,hA,hne⟩ := hne
  obtain ⟨he,h₁,_⟩ := offender_product_of_not_strong _ _ core_not_strong core_not_strong
    ((hP.2.1 A hA).isOffender action)
  have hb := best_of_offender (h₁.resolve_left hne)
  have hb' := hb.map_of_fixedCodim (coreRepresentation (Fin 5)) action
    (MonoidHom.inl Sym Sym) inl_injective (fun A => (fixedCodim_axis_left A).symm)
  refine ⟨A.map (MonoidHom.fst Sym Sym),stable_downward hP hA hb' ?_⟩
  rintro _ ⟨a,ha,rfl⟩
  rw [he]
  exact ⟨ha,one_mem _⟩

theorem stable_right_axis {P : Set (Subgroup (Sym × Sym))} (hP : IsStable action P)
    (hne : ∃ A ∈ P, A.map (MonoidHom.snd Sym Sym) ≠ ⊥) :
    IsStable (coreRepresentation (Fin 5))
      {B : Subgroup Sym | B.map (MonoidHom.inr Sym Sym) ∈ P} := by
  apply hP.restrict_of_fixedCodim _ _ (MonoidHom.inr Sym Sym) inr_injective
    (fun A => (fixedCodim_axis_right A).symm)
  obtain ⟨A,hA,hne⟩ := hne
  obtain ⟨he,_,h₂⟩ := offender_product_of_not_strong _ _ core_not_strong core_not_strong
    ((hP.2.1 A hA).isOffender action)
  have hb := best_of_offender (h₂.resolve_left hne)
  have hb' := hb.map_of_fixedCodim (coreRepresentation (Fin 5)) action
    (MonoidHom.inr Sym Sym) inr_injective (fun A => (fixedCodim_axis_right A).symm)
  refine ⟨A.map (MonoidHom.snd Sym Sym),stable_downward hP hA hb' ?_⟩
  rintro _ ⟨a,ha,rfl⟩
  rw [he]
  exact ⟨one_mem _,ha⟩

/-- Both nontrivial coordinate projections of a stable family force the full
product of the transposition four-groups in the original product Sylow. -/
theorem stable_generatedBy_product {P : Set (Subgroup (Sym × Sym))}
    (hP : IsStable action P)
    (hn₁ : ∃ A ∈ P, A.map (MonoidHom.fst Sym Sym) ≠ ⊥)
    (hn₂ : ∃ A ∈ P, A.map (MonoidHom.snd Sym Sym) ≠ ⊥)
    (R S : Subgroup Sym) (hR : IsPGroup 2 R) (hS : IsPGroup 2 S)
    (hDR : D 5 ≤ R) (hDS : D 5 ≤ S) :
    generatedBy P (R.prod S) = (D 5).prod (D 5) := by
  apply le_antisymm
  · apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA,hAR⟩
    exact offender_le_transposition_product R S hR hS hDR hDS
      ((hP.2.1 A hA).isOffender action) hAR
  · have hl : (D 5).map (MonoidHom.inl Sym Sym) ≤ generatedBy P (R.prod S) := by
      rw [←stable_generatedBy_eq_D (stable_left_axis hP hn₁) R hR hDR]
      rw [map_le_iff_le_comap]
      apply iSup_le
      intro A
      apply iSup_le
      rintro ⟨hA,hAR⟩
      apply map_le_iff_le_comap.mp
      refine le_iSup_of_le (A.map (MonoidHom.inl Sym Sym))
        (le_iSup_of_le ⟨hA,?_⟩ le_rfl)
      rintro _ ⟨a,ha,rfl⟩
      exact ⟨hAR ha,one_mem _⟩
    have hr : (D 5).map (MonoidHom.inr Sym Sym) ≤ generatedBy P (R.prod S) := by
      rw [←stable_generatedBy_eq_D (stable_right_axis hP hn₂) S hS hDS]
      rw [map_le_iff_le_comap]
      apply iSup_le
      intro A
      apply iSup_le
      rintro ⟨hA,hAS⟩
      apply map_le_iff_le_comap.mp
      refine le_iSup_of_le (A.map (MonoidHom.inr Sym Sym))
        (le_iSup_of_le ⟨hA,?_⟩ le_rfl)
      rintro _ ⟨a,ha,rfl⟩
      exact ⟨one_mem _,hAS ha⟩
    intro x hx
    have he : x = (x.1,1) * (1,x.2) := by ext <;> simp
    rw [he]
    exact mul_mem (hl (mem_map.mpr ⟨x.1,hx.1,rfl⟩))
      (hr (mem_map.mpr ⟨x.2,hx.2,rfl⟩))

end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
