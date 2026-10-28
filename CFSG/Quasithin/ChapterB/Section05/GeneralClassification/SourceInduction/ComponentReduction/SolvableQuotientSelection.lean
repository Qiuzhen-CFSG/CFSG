module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.FactorSelection
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Selection
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GeneralClassification
public import Theory.Representation.BinaryOffender.FixedCodimTransport
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.RelativeQuotientMaps
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Selecting an offender moving a component with solvable quotient

A minimal best offender either moves the component or moves the Fitting
subgroup: otherwise the component commutator selection contradicts solvability
of the quotient. In the latter case B.1.9 splits off its supported S₃ factor.
The component lies in the smaller complementary factor, and finite induction
selects the desired offender there. Equality of fixed codimensions lifts its
minimality through the fixed direct-sum complement. Restriction to the actual
offender subgroup then handles actors which are not offender-generated.

Source: Aschbacher–Smith B.1.9, B.5.8 and13.6.15, printed pp.71–72,106,930.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource FittingReduction
universe u v

private theorem minimal_iff_fixedCodim
    {D V W : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) D W)
    (hc : ∀ A, fixedCodim ρ A = fixedCodim σ A) (A : Subgroup D) :
    IsMinimalBestOffender ρ A ↔ IsMinimalBestOffender σ A := by
  have hw (B E : Subgroup D) : weight σ B ≤ weight σ E ↔ weight ρ B ≤ weight ρ E := by
    simpa only [Subgroup.map_id] using
      weight_le_map_iff_of_fixedCodim ρ σ (MonoidHom.id D) Function.injective_id
        (fun A => by simpa only [Subgroup.map_id] using hc A) B E
  have hb (B : Subgroup D) : IsBestOffender ρ B ↔ IsBestOffender σ B := by
    simp only [IsBestOffender, hw]
  constructor
  · rintro ⟨hA, hm⟩
    refine ⟨(hb A).mp hA, fun B hB hBA => hm B ((hb B).mpr hB) ⟨hBA.1, ?_⟩⟩
    exact le_antisymm ((hw B A).mp hBA.2.le) ((hw A B).mp hBA.2.ge)
  · rintro ⟨hA, hm⟩
    refine ⟨(hb A).mpr hA, fun B hB hBA => hm B ((hb B).mp hB) ⟨hBA.1, ?_⟩⟩
    exact le_antisymm ((hw B A).mpr hBA.2.le) ((hw A B).mpr hBA.2.ge)

private theorem minimal_map_subtype
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (H : Subgroup D) {A : Subgroup H}
    (hA : IsMinimalBestOffender (ρ.comp H.subtype) A) :
    IsMinimalBestOffender ρ (A.map H.subtype) := by
  refine ⟨hA.1.map_subtype ρ, ?_⟩
  intro B hB hBA
  have hBH : B ≤ H := hBA.1.trans (map_subtype_le A)
  have he : EqualWeightLE (ρ.comp H.subtype) (B.subgroupOf H) A := by
    refine ⟨?_, ?_⟩
    · intro b hb
      obtain ⟨a, ha, he⟩ := hBA.1 hb
      exact H.subtype_injective he ▸ ha
    · rw [weight_comp_map ρ H.subtype H.subtype_injective,
        weight_comp_map ρ H.subtype H.subtype_injective,
        map_subgroupOf_eq_of_le hBH]
      exact hBA.2
  have hh := hA.2 _ (hB.subgroupOf ρ hBH) he
  have hm := congrArg (map H.subtype) hh
  rwa [map_subgroupOf_eq_of_le hBH] at hm

private theorem Configuration.fixedCodim_second
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] {ρ : Representation (ZMod 2) D V}
    {A : Subgroup D} (c : Configuration ρ A) (B : Subgroup c.second) :
    fixedCodim c.secondAction B = fixedCodim (ρ.comp c.second.subtype) B := by
  let W : Subrepresentation (ρ.comp c.second.subtype) :=
    ⟨c.secondSpace.toSubmodule, fun g => c.secondSpace.apply_mem_toSubmodule g⟩
  apply (fixedCodim_subrepresentation_eq_iff (ρ.comp c.second.subtype) W B).mpr
  apply top_unique
  rw [← c.decomposition.symm.sup_eq_top]
  refine sup_le le_sup_left (le_sup_of_le_right ?_)
  intro w hw b
  exact c.cross_fixed hw b.val

private theorem solvable_quotient_subgroup
    {D : Type*} [Group D] (C H : Subgroup D) [C.Normal]
    [Group.IsSolvable (D ⧸ C)] : Group.IsSolvable (H ⧸ C.subgroupOf H) := by
  let f := (QuotientGroup.mk' C).comp H.subtype
  have he : f.ker = C.subgroupOf H := by
    ext x
    exact QuotientGroup.eq_one_iff (N := C) x.val
  let e := (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

private theorem Configuration.component_le_second
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {A : Subgroup D}
    (c : Configuration ρ A) (C : Subgroup D) [Group.IsPerfect C] : C ≤ c.second := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable c.first := Group.isSolvable_of_isSolvable_injective
    (f := c.firstEquiv.toMonoidHom) c.firstEquiv.injective
  have hz : C.map c.product.fst = ⊥ := by
    let : Group.IsPerfect (C.map c.product.fst) := Group.IsPerfect.map _
    by_contra h
    let : Nontrivial (C.map c.product.fst) := (nontrivial_iff_ne_bot _).mpr h
    exact Group.IsPerfect.not_isSolvable (C.map c.product.fst) inferInstance
  exact c.product.ker_fst ▸ (map_eq_bot_iff C).mp hz


/-- A normal component with solvable quotient is moved by a minimal best
offender. Supported S₃ factors are removed by cardinal descent. -/
theorem exists_minimalBestOffender_not_centralizing_component
    {𝒦 : GroupClass.{u}} (h19 : EarlierB19.{u,v})
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hyp : FFHypothesis 𝒦 ρ)
    (C : Subgroup D) [C.Normal] [Group.IsSolvable (D ⧸ C)]
    (hc : IsQuasisimple C) :
    ∃ A, IsMinimalBestOffender ρ A ∧ ¬ A ≤ centralizer (C : Set D) := by
  classical
  have aux : ∀ n : ℕ, ∀ (D : Type u) [Group D] [Finite D]
      (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
      (ρ : Representation (ZMod 2) D V) (hyp : FFHypothesis 𝒦 ρ)
      (C : Subgroup D) [C.Normal] [Group.IsSolvable (D ⧸ C)],
      IsQuasisimple C → Nat.card D = n →
      ∃ A, IsMinimalBestOffender ρ A ∧ ¬ A ≤ centralizer (C : Set D) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro D _ _ V _ _ ρ hyp C _ _ hc hn
      let := hyp.finite_module
      let : IsQuasisimple C := hc
      let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
      let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
      let : Nontrivial D := Function.Injective.nontrivial C.subtype_injective
      obtain ⟨A, hA⟩ := hyp.exists_minimalBestOffender ρ
      by_cases hAC : A ≤ centralizer (C : Set D)
      · have hAF : ¬ A ≤ centralizer (fittingSubgroup D : Set D) := by
          intro hAF
          obtain ⟨L, hL, hLA⟩ := ComponentReduction.exists_component_moved
            ρ hyp.twoCore hA.1 hAF
          let : IsQuasisimple L := hL.2
          have hLC : L ≤ C := le_of_isPerfect_of_solvable_quotient L C
          exact hLA ((commutator_comm L A).trans
            (commutator_eq_bot_iff_le_centralizer.mpr (hAC.trans (centralizer_le hLC))))
        obtain ⟨c⟩ := FittingReduction.FFHypothesis.fitting_configuration hyp h19 hA hAF
        have hCB := Configuration.component_le_second c C
        let C' := C.subgroupOf c.second
        let : C'.Normal := normal_subgroupOf
        let : Group.IsSolvable (c.second ⧸ C') := solvable_quotient_subgroup C c.second
        have hC' : IsQuasisimple C' := IsQuasisimple.of_mulEquiv
          (subgroupOfEquivOfLe hCB).symm
        obtain ⟨hlt, hypB⟩ := c.descent hyp
        have hlt' : Nat.card c.second < n := hn ▸ hlt
        obtain ⟨B, hB, hBC⟩ := ih (Nat.card c.second) hlt' c.second
          c.secondSpace.toSubmodule c.secondAction hypB C' hC' rfl
        have hBfull : IsMinimalBestOffender (ρ.comp c.second.subtype) B :=
          (minimal_iff_fixedCodim c.secondAction (ρ.comp c.second.subtype)
            (Configuration.fixedCodim_second c) B).mp hB
        refine ⟨B.map c.second.subtype, minimal_map_subtype ρ c.second hBfull, ?_⟩
        intro hcentral
        apply hBC
        intro b hb x hx
        apply Subtype.ext
        exact hcentral (mem_map_of_mem c.second.subtype hb) x.val hx
      · exact ⟨A, hA, hAC⟩
  exact aux (Nat.card D) D V ρ hyp C hc rfl


/-- Restricting to the actual offender subgroup selects a minimal offender
of the original action moving the original component. -/
theorem exists_minimalBestOffender_not_centralizing_of_le_offenders
    {𝒦 : GroupClass.{u}} (h19 : EarlierB19.{u,v})
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (C : Subgroup D) [C.Normal]
    [Group.IsSolvable (D ⧸ C)] (hc : IsQuasisimple C)
    (hCJ : C ≤ offenderSubgroup ρ) (hcover : Nonempty (SQTKQuotient 𝒦 D)) :
    ∃ A, IsMinimalBestOffender ρ A ∧ ¬ A ≤ centralizer (C : Set D) := by
  let J := offenderSubgroup ρ
  let σ := ρ.comp J.subtype
  let : J.Normal := offenderSubgroup_normal ρ
  let C' := C.subgroupOf J
  let : C'.Normal := normal_subgroupOf
  let : Group.IsSolvable (J ⧸ C') := solvable_quotient_subgroup C J
  have hC' : IsQuasisimple C' := IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe hCJ).symm
  have hcoreJ : pCore 2 J = ⊥ := by
    have hn : ((pCore 2 J).map J.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hl : (pCore 2 J).map J.subtype ≤ pCore 2 D :=
      le_sSup ⟨hn,pCore_isPGroup.map _⟩
    rw [hcore] at hl
    exact ((pCore 2 J).map_eq_bot_iff_of_injective J.subtype_injective).mp (le_bot_iff.mp hl)
  obtain ⟨cover⟩ := hcover
  have hyp : FFHypothesis 𝒦 σ := ⟨inferInstance, hf.comp J.subtype_injective,
    hcoreJ, offenderSubgroup_restrict_eq_top ρ, ⟨cover.subgroup J⟩⟩
  obtain ⟨A,hA,hAC⟩ := exists_minimalBestOffender_not_centralizing_component
    h19 σ hyp C' hC'
  refine ⟨A.map J.subtype,minimal_map_subtype ρ J hA,?_⟩
  intro h
  apply hAC
  intro a ha c hc
  apply Subtype.ext
  exact h (mem_map_of_mem J.subtype ha) c.val hc

end CFSG.Quasithin.ChapterB.SourceInduction
