module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneComparison
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.SymmetricThreeModule
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.ProductGeometry.Supplements
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.Reduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction

/-!
# Extracting the split rank-one rows on the literal fixed quotient

The quotient of a moved section by its fixed kernel is identified with its
actual image in V/C_V(D). In the ratio-one rows, the offender equality supplies
C_V(L)=C_V(D); Sylow averaging supplies the SL₂ supplement, and alternating
cohomology supplies the S₅ supplement. The doubled SL₃ branch uses the checked
extension splitting theorem, including the binary endpoint. Every output uses
the original moved space and compatible group and module identifications.

These implications consume already established B.5.1 action rows. They do not
assert a classifier. The remaining nonsupplemented natural SL₃ row and the
component-centralizer rank bound belong to the subsequent extraction assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.8 and
B.5.11(2), printed pp.106 and 109; B.5.1, pp.99–103; I.1.6, p.408.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences
open ComponentReduction.ProductGeometry
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

noncomputable def imageEquivOfDisjoint (U : Subrepresentation ρ)
    (hd : Disjoint U.toSubmodule ρ.invariants) :
    U.toSubmodule ≃ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule := by
  let f : U.toSubmodule →ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule := {
    toFun := fun v => ⟨ρ.invariants.mkQ v, ⟨v, v.property, rfl⟩⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have hmem : (v : V) ∈ ρ.invariants :=
      (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv)
    exact Subtype.ext ((disjoint_iff.mp hd).le ⟨v.property, hmem⟩)
  · rintro ⟨q, v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

theorem imageEquivOfDisjoint_equivariant (U : Subrepresentation ρ)
    (hd : Disjoint U.toSubmodule ρ.invariants) (g : D) (v : U.toSubmodule) :
    imageEquivOfDisjoint U hd (U.toRepresentation g v) =
      ((fixed ρ).quotientImage U).toRepresentation g (imageEquivOfDisjoint U hd v) := rfl

noncomputable def sectionImageEquiv {L : Subgroup D} (s : MovedSection ρ L)
    (hc : fixedSpace ρ L = ρ.invariants) :
    (s.space.toSubmodule ⧸ s.central.toSubmodule) ≃ₗ[ZMod 2]
      ((fixed ρ).quotientImage s.space).toSubmodule := by
  let f : s.space.toSubmodule →ₗ[ZMod 2]
      ((fixed ρ).quotientImage s.space).toSubmodule := {
    toFun := fun v => ⟨ρ.invariants.mkQ v, ⟨v, v.property, rfl⟩⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hk : s.central.toSubmodule = f.ker := by
    ext v
    rw [s.central_eq]
    change (∀ g : L, s.space.toRepresentation g v = v) ↔ f v = 0
    constructor
    · intro hv
      apply Subtype.ext
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [← hc]
      exact fun g => congrArg Subtype.val (hv g)
    · intro hv g
      apply Subtype.ext
      have hx : (v : V) ∈ ρ.invariants :=
        (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv)
      exact hx g
  let q := s.central.toSubmodule.liftQ f hk.le
  apply LinearEquiv.ofBijective q
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact (Submodule.Quotient.mk_eq_zero _).mpr (hk.symm ▸ hv)
  · rintro ⟨q, v, hv, rfl⟩
    exact ⟨s.central.toSubmodule.mkQ ⟨v, hv⟩, rfl⟩

theorem sectionImageEquiv_equivariant {L : Subgroup D} (s : MovedSection ρ L)
    (hc : fixedSpace ρ L = ρ.invariants) (g : D)
    (v : s.space.toSubmodule ⧸ s.central.toSubmodule) :
    sectionImageEquiv s hc ((MovedSection.action ρ s) g v) =
      ((fixed ρ).quotientImage s.space).toRepresentation g (sectionImageEquiv s hc v) := by
  induction v using Submodule.Quotient.induction_on with | _ v => rfl

noncomputable def imageSectionAction {L : Subgroup D} (s : MovedSection ρ L)
    (hc : fixedSpace ρ L = ρ.invariants) (A : Subgroup D) :
    ActionEquiv (((fixed ρ).quotientImage s.space).toRepresentation.comp A.subtype)
      (s.action.comp A.subtype) where
  groupEquiv := MulEquiv.refl A
  linearEquiv := (sectionImageEquiv s hc).symm
  intertwines g v := by
    apply (sectionImageEquiv s hc).injective
    change sectionImageEquiv s hc ((sectionImageEquiv s hc).symm
      (((fixed ρ).quotientImage s.space).toRepresentation g v)) =
      sectionImageEquiv s hc ((MovedSection.action ρ s) g ((sectionImageEquiv s hc).symm v))
    rw [LinearEquiv.apply_symm_apply, sectionImageEquiv_equivariant,
      LinearEquiv.apply_symm_apply]

def transAction {H W J X : Type*} [Group H] [Group J]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) H W} {τ : Representation (ZMod 2) J X}
    (e : ActionEquiv ρ σ) (f : ActionEquiv σ τ) : ActionEquiv ρ τ :=
  ⟨e.groupEquiv.trans f.groupEquiv, e.linearEquiv.trans f.linearEquiv,
    fun g v => (congrArg f.linearEquiv (e.intertwines g v)).trans (f.intertwines _ _)⟩

theorem moved_eq_of_supplement {L : Subgroup D} (s : MovedSection ρ L)
    (hs : s.space.toSubmodule ⊔ ρ.invariants = ⊤) :
    s.space.toSubmodule = moved ρ ⊤ := by
  apply le_antisymm
  · rw [s.space_eq]
    apply Submodule.span_mono
    rintro _ ⟨g, hg, v, hv, rfl⟩
    exact ⟨g, mem_top _, v, hv, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp (hs.symm ▸ Submodule.mem_top (x := v))
    change ρ g (w + c) - (w + c) ∈ s.space.toSubmodule
    rw [map_add, hc g, add_sub_add_right_eq_sub]
    exact s.space.toSubmodule.sub_mem (s.space.apply_mem_toSubmodule g hw) hw

theorem ff_of_generated [Nontrivial D] [Module.Finite (ZMod 2) V] (hj : offenderSubgroup ρ = ⊤) : IsFFModule ρ := by
  by_contra hn
  have hb : offenderSubgroup ρ = ⊥ := by
    apply bot_unique
    apply iSup₂_le
    intro A hA
    exact (hn ⟨A, hA.1.isOffender ρ⟩).elim
  exact top_ne_bot (hj.symm.trans hb)

theorem doubleThree_factor_module [Module.Finite (ZMod 2) V]
    {L : Subgroup D} (s : MovedSection ρ L) (F : BinaryField)
    (ho : Odd F.degree) (hL : L = ⊤) (hFF : IsFFModule ρ)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural F 3) 2)) : Nonempty (FactorModuleConclusion ρ) := by
  subst L
  have hc := doubleThree_isCompl s F rfl hFF e
  let q := imageEquivOfDisjoint s.space hc.disjoint
  let t : ActionEquiv
      (((fixed ρ).quotientImage s.space).toRepresentation.comp (⊤ : Subgroup D).subtype)
      (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype) := {
    groupEquiv := MulEquiv.refl _
    linearEquiv := q.symm
    intertwines := by
      intro g v
      apply q.injective
      rw [LinearEquiv.apply_symm_apply]
      exact ((imageEquivOfDisjoint_equivariant s.space hc.disjoint g (q.symm v)).trans
        (congrArg (((fixed ρ).quotientImage s.space).toRepresentation g) (q.apply_symm_apply v))).symm }
  exact ⟨⟨s.space, hc.sup_eq_top, .doubleNatural F ho s.space_eq ⟨transAction t e⟩⟩⟩

theorem linearTwo_factor_module [Finite D] [Nontrivial D] [Module.Finite (ZMod 2) V]
    {L : Subgroup D} [L.Normal] (s : MovedSection ρ L) (F : BinaryField)
    (hj : offenderSubgroup ρ = ⊤) (hg : offenderSubgroup s.action = L)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 2))
    (hoff : ∀ A, IsBestOffender s.action A → ∃ T : Sylow 2 L,
      A = (T : Subgroup L).map L.subtype)
    (hq : quadraticRatio s.action = 1) : Nonempty (FactorModuleConclusion ρ) := by
  have ht : L = ⊤ := hg.symm.trans (DualExtensions.section_generated s hq hj)
  subst L
  obtain ⟨A, hA⟩ := ff_of_generated hj
  obtain ⟨T, hT⟩ := hoff A (DualExtensions.offender_equality s hq hA).1
  have hs := sylow_supplement s ⟨T, hT⟩ (DualExtensions.offender_equality s hq hA).2.2.1
  rw [fixedSpace_top] at hs
  let t := imageSectionAction s fixedSpace_top ⊤
  exact ⟨⟨s.space, hs, .natural s.space_eq (.linearTwo F ⟨transAction t e⟩)⟩⟩

theorem symmetricFive_factor_module [Finite D] [Module.Finite (ZMod 2) V]
    {L : Subgroup D} [L.Normal] (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule) (hj : offenderSubgroup ρ = ⊤)
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action) L
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (hq : quadraticRatio s.action = 1) : Nonempty (FactorModuleConclusion ρ) := by
  have hg := DualExtensions.section_generated s hq hj
  have hf := DualExtensions.fixed_eq_invariants s hq hj
  have hs := (symmetricOdd_isCompl s hi (Or.inl rfl) e).sup_eq_top
  rw [hf] at hs
  let t : ActionEquiv (s.action.comp (⊤ : Subgroup D).subtype)
      (BinaryPermutation.naturalRepresentation (Fin 5)) := {
    groupEquiv := (MulEquiv.subgroupCongr hg.symm).trans e.action.groupEquiv
    linearEquiv := e.action.linearEquiv
    intertwines g v := e.action.intertwines ((MulEquiv.subgroupCongr hg.symm) g) v }
  exact ⟨⟨s.space, hs, .natural (moved_eq_of_supplement s hs)
    (.symmetricFive ⟨transAction (imageSectionAction s hf ⊤) t⟩)⟩⟩

theorem linearThree_supplement_factor_module {L : Subgroup D}
    (s : MovedSection ρ L) (F : BinaryField) (ho : Odd F.degree) (ht : L = ⊤)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 3))
    (hs : s.space.toSubmodule ⊔ ρ.invariants = ⊤) :
    Nonempty (FactorModuleConclusion ρ) := by
  subst L
  exact ⟨⟨s.space, hs, .natural s.space_eq
    (.linearThree F ho ⟨transAction (imageSectionAction s fixedSpace_top ⊤) e⟩)⟩⟩
end CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
