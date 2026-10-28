module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.Contracts
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleReduction

/-!
# Normal components and the fixed-space preparation in B.5.5

Offender generation and the complete earlier B.1.5(4) implication make each
component normal and supply an original best offender moving it. Inside LA,
the proved B.1 two-core reduction identifies the kernel on C_V(O₂(LA)).
The trivial two-core of L gives faithfulness there; the centralizer in the
abelian offender is central in LA and therefore lies in its two-core.
These calculations give the exact ambient fixed-space clause for every
moving offender.

For the existential chief-section step, choose a minimal offender in the
fixed-space image and lift it through the full pointwise kernel. The
restriction weight equality proves that the lift is still a best offender
on the original module. Nontriviality of its image proves that it still
moves L. The application `component_minimal_fixedCore` retains this original
offender and the same initial fixed space for the ensuing section choice.
No irreducible-section or classification conclusion is assumed here.

The sole universal input is B.1.5(4), produced by
`qt-b01-component-normalization`. Its final discharge belongs to
`qt-b05-quotient-components`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.5(1i–iii), printed pp.104–105; B.1.5 and B.7.1, pp.69 and 118–119.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.PreparationSource
open SourceInduction ComponentReduction ComponentReduction.PreliminaryActions
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- The entire B.1.5(4) implication, with the original faithful finite action. -/
@[expose]
def ComponentNormalizationInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (σ : Representation (ZMod 2) D V), Function.Injective σ →
      ∀ A, IsBestOffender σ A → ∀ L, IsComponent D L → A ≤ normalizer (L : Set D)

/-- Every noncentral subgroup is moved by a best offender when those offenders generate D. -/
theorem exists_moving_offender (hgen : offenderSubgroup ρ = ⊤)
    (X : Subgroup D) (hn : ¬ X ≤ center D) :
    ∃ A, IsBestOffender ρ A ∧ ⁅X,A⁆ ≠ ⊥ := by
  by_contra! h
  have hc : offenderSubgroup ρ ≤ centralizer (X : Set D) :=
    (offenderSubgroup_le_iff ρ _).mpr fun A hA =>
      commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm A X).trans (h A hA))
  rw [hgen] at hc
  exact hn (centralizer_eq_top_iff_subset.mp (top_unique hc))

/-- B.1.5(4) and offender generation make every original component normal. -/
theorem component_normal [Finite D] {K : GroupClass.{u}}
    (hn : ComponentNormalizationInput.{u,v}) (hyp : FFHypothesis K ρ)
    {L : Subgroup D} (hL : IsComponent D L) : L.Normal := by
  let := hyp.finite_module
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hyp.generated]
  exact (offenderSubgroup_le_iff ρ _).mpr fun A hA => hn D V ρ hyp.faithful A hA L hL

/-- A component is noncentral, and its nontrivial offender commutator is the whole component. -/
theorem component_moving [Finite D] {K : GroupClass.{u}}
    (hn : ComponentNormalizationInput.{u,v}) (hyp : FFHypothesis K ρ)
    {L : Subgroup D} (hL : IsComponent D L) :
    ∃ A, IsBestOffender ρ A ∧ ⁅L,A⁆ = L := by
  let := component_normal ρ hn hyp hL
  let := hL.2
  have hnc : ¬ L ≤ center D := by
    intro hc
    have hh : ⁅L,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hc.trans (center_le_centralizer _))
    rw [commutator_eq_self] at hh
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (nontrivial_iff_ne_bot L).mp inferInstance hh
  obtain ⟨A,hA,hm⟩ := exists_moving_offender ρ hyp.generated L hnc
  refine ⟨A,hA,?_⟩
  rcases hL.commutator_dichotomy A with hz | he
  · exact (hm hz).elim
  · simpa only [MulEquiv.toMonoidHom_eq_coe, Subgroup.Normal.map_conj_eq, iSup_const] using he

/-- Lift a minimal restricted offender with its full pointwise kernel. Equal weight proves best-offender status for the original representation. -/
theorem lift_minimal_offender [Finite D] [Module.Finite (ZMod 2) V]
    {A₀ : Subgroup D} (hA₀ : IsBestOffender ρ A₀)
    (W : Submodule (ZMod 2) V) (hW : A₀ ≤ subspaceStabilizer ρ W)
    (hm : ¬ W ≤ fixedSpace ρ A₀) :
    ∃ A ≤ A₀, subspaceKernel ρ W A₀ ≤ A ∧ IsBestOffender ρ A ∧
      EqualWeightLE ρ A A₀ ∧
      IsMinimalBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
  obtain ⟨B,hB,hBA⟩ := (hA₀.restricted ρ W hW hm).exists_minimal _
  obtain ⟨A,hAA,hKA,hAB⟩ := exists_subgroup_restrictedSubgroup ρ W hW B hBA.1
  have hne : A ≠ ⊥ := by
    intro he
    apply hB.1.1.1
    rw [← hAB,he,restrictedSubgroup_bot]
  have heq := ((hA₀.image_weight_eq_iff ρ W hW hAA hKA).mp
    (by rw [hAB]; exact hBA.2)).1
  exact ⟨A,hAA,hKA,hA₀.of_equalWeightLE ρ (hA₀.1.of_le hAA hne) heq,
    heq,hAB.symm ▸ hB⟩

private theorem centralizer_offender_le_core [Finite D]
    (L A : Subgroup D) (hgen : L ⊔ A = ⊤) (hA : IsElementaryAbelian 2 A) :
    A ⊓ centralizer (L : Set D) ≤ pCore 2 D := by
  let := hA
  let B := A ⊓ centralizer (L : Set D)
  have hcenter : B ≤ center D := by
    apply centralizer_eq_top_iff_subset.mp
    apply top_unique
    rw [← hgen]
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_right
    · apply le_centralizer_iff.mp
      exact inf_le_left.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  let : B.Normal := ⟨fun b hb g => by
    have he := mem_center_iff.mp (hcenter hb) g
    simpa only [he, mul_inv_cancel_right] using hb⟩
  exact le_sSup ⟨inferInstance,
    (IsElementaryAbelian.isPGroup 2 A).of_injective
      (inclusion (show B ≤ A from inf_le_left)) (inclusion_injective _)⟩

/-- For D=LA, the two-core fixed space is faithful on L and has exactly the L-centralizer as its A-kernel. -/
theorem generated_fixedCore [Finite D] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (L A : Subgroup D) [L.Normal] [IsQuasisimple L]
    (h2 : pCore 2 L = ⊥) (hLA : ⁅L,A⁆ = L) (hgen : L ⊔ A = ⊤)
    (hA : IsBestOffender ρ A) :
    (∀ l ∈ L, (∀ w ∈ fixedSpace ρ (pCore 2 D), ρ l w = w) → l = 1) ∧
    subspaceKernel ρ (fixedSpace ρ (pCore 2 D)) A = A ⊓ centralizer (L : Set D) := by
  have hr := irreducibleReduction_generated ρ hf L A hLA hgen hA
  have hk := irreducibleReduction_component_kernel ρ L hr.1
  rw [h2, Subgroup.map_bot] at hk
  constructor
  · intro l hl hw
    have hh : l ∈ subspaceKernel ρ (fixedSpace ρ (pCore 2 D)) L := ⟨hl,hw⟩
    simpa only [hk, mem_bot] using hh
  · apply le_antisymm
    · rintro a ⟨ha,hw⟩
      exact ⟨ha,hr.2.1 (hr.1 ▸ (show a ∈ subspaceKernel ρ (fixedSpace ρ (pCore 2 D)) ⊤ from ⟨mem_top _,hw⟩))⟩
    · intro a ha
      have hc := centralizer_offender_le_core L A hgen hA.1.2 ha
      exact ⟨ha.1,fun w hw => hw ⟨a,hc⟩⟩

/-- A normal subgroup inherits the trivial two-core of the ambient group. -/
theorem component_twoCore [Finite D] {L : Subgroup D} [L.Normal]
    (h2 : pCore 2 D = ⊥) : pCore 2 L = ⊥ := by
  have hle : (pCore 2 L).map L.subtype ≤ pCore 2 D :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map L.subtype⟩
  apply bot_unique
  intro x hx
  have hm := hle (mem_map_of_mem L.subtype hx)
  rw [h2, mem_bot] at hm
  exact Subtype.ext hm

/-- B.5.5(1ii) on the literal ambient fixed space, for every moving original best offender. -/
theorem fixedCore [Finite D] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (h2 : pCore 2 D = ⊥)
    (L A : Subgroup D) [L.Normal] [IsQuasisimple L]
    (hLA : ⁅L,A⁆ = L) (hA : IsBestOffender ρ A) :
    (∀ l ∈ L, (∀ w ∈ fixedSpace ρ (localTwoCore L A), ρ l w = w) → l = 1) ∧
    subspaceKernel ρ (fixedSpace ρ (localTwoCore L A)) A = A ⊓ centralizer (L : Set D) ∧
    IsBestOffender (subspaceImageRepresentation ρ (fixedSpace ρ (localTwoCore L A)))
      (restrictedSubgroup ρ (fixedSpace ρ (localTwoCore L A)) A) := by
  let H := L ⊔ A
  let L₀ := L.subgroupOf H
  let A₀ := A.subgroupOf H
  let τ := ρ.comp H.subtype
  let W := fixedSpace ρ (localTwoCore L A)
  let : L₀.Normal := inferInstanceAs (L.subgroupOf H).Normal
  let eL : L₀ ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let : IsQuasisimple L₀ := IsQuasisimple.of_mulEquiv eL.symm
  have h2L : pCore 2 L₀ = ⊥ := by
    apply Subgroup.map_injective (f := eL.toMonoidHom) eL.injective
    rw [pCore_map_iso, component_twoCore h2, Subgroup.map_bot]
  have hcomm : ⁅L₀,A₀⁆ = L₀ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_commutator]
    change ⁅(L.subgroupOf H).map H.subtype, (A.subgroupOf H).map H.subtype⁆ =
      (L.subgroupOf H).map H.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right), hLA]
  have hgen : L₀ ⊔ A₀ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (show L ≤ H from le_sup_left)
      (show A ≤ H from le_sup_right), Subgroup.subgroupOf_self]
  have hU : fixedSpace τ (pCore 2 H) = W := fixedSpace_comp_map ρ H.subtype _
  obtain ⟨hfL,hker⟩ := generated_fixedCore τ (hf.comp H.subtype_injective)
    L₀ A₀ h2L hcomm hgen (hA.subgroupOf ρ (show A ≤ H from le_sup_right))
  rw [hU] at hfL hker
  have hfaith : ∀ l ∈ L, (∀ w ∈ W, ρ l w = w) → l = 1 := by
    intro l hl hw
    exact congrArg Subtype.val (hfL ⟨l,(le_sup_left : L ≤ H) hl⟩ hl hw)
  have hcentral : subspaceKernel ρ W A = A ⊓ centralizer (L : Set D) := by
    ext a
    constructor
    · rintro ⟨ha,hw⟩
      have hh : (⟨a,(le_sup_right : A ≤ H) ha⟩ : H) ∈ subspaceKernel τ W A₀ := ⟨ha,hw⟩
      rw [hker] at hh
      refine ⟨ha,mem_centralizer_iff.mpr ?_⟩
      intro l hl
      exact congrArg Subtype.val ((mem_centralizer_iff.mp hh.2) ⟨l,(le_sup_left : L ≤ H) hl⟩ hl)
    · rintro ⟨ha,hc⟩
      have hh : (⟨a,(le_sup_right : A ≤ H) ha⟩ : H) ∈ A₀ ⊓ centralizer (L₀ : Set H) := by
        refine ⟨ha,mem_centralizer_iff.mpr ?_⟩
        intro l hl
        exact Subtype.ext ((mem_centralizer_iff.mp hc) l hl)
      rw [← hker] at hh
      exact ⟨ha,hh.2⟩
  have hQ : H ≤ normalizer (localTwoCore L A : Set D) := by
    simpa only [localTwoCore, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 H).le_normalizer_map H.subtype
  have hW : A ≤ subspaceStabilizer ρ W :=
    le_sup_right.trans (fixedSpace_invariant_normalizer ρ hQ)
  have hmove : ¬ W ≤ fixedSpace ρ A := by
    intro hh
    have hAC : A ≤ centralizer (L : Set D) := by
      intro a ha
      have hm : a ∈ subspaceKernel ρ W A := ⟨ha,fun w hw => hh hw ⟨a,ha⟩⟩
      exact (hcentral ▸ hm).2
    have hLb : L = ⊥ := hLA.symm.trans
      ((commutator_comm L A).trans (commutator_eq_bot_iff_le_centralizer.mpr hAC))
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (nontrivial_iff_ne_bot L).mp inferInstance hLb
  exact ⟨hfaith,hcentral,hA.restricted ρ W hW hmove⟩

/-- Choose the original best offender while retaining minimality on the fixed space
of the initially chosen offender. The new offender still moves the same component. -/
theorem exists_minimal_fixedCore_offender [Finite D] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (h2 : pCore 2 D = ⊥)
    {L A₀ : Subgroup D} (hL : IsComponent D L) [L.Normal]
    (hLA₀ : ⁅L,A₀⁆ = L) (hA₀ : IsBestOffender ρ A₀) :
    let W := fixedSpace ρ (localTwoCore L A₀)
    ∃ A ≤ A₀, subspaceKernel ρ W A₀ ≤ A ∧ IsBestOffender ρ A ∧
      EqualWeightLE ρ A A₀ ∧ ⁅L,A⁆ = L ∧
      IsMinimalBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
  let := hL.2
  let W := fixedSpace ρ (localTwoCore L A₀)
  obtain ⟨_,hker,hbest⟩ := fixedCore ρ hf h2 L A₀ hLA₀ hA₀
  have hQ : L ⊔ A₀ ≤ normalizer (localTwoCore L A₀ : Set D) := by
    simpa only [localTwoCore, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 ↥(L ⊔ A₀)).le_normalizer_map (L ⊔ A₀).subtype
  have hW : A₀ ≤ subspaceStabilizer ρ W :=
    le_sup_right.trans (fixedSpace_invariant_normalizer ρ hQ)
  have hmove : ¬ W ≤ fixedSpace ρ A₀ := by
    intro hc
    apply hbest.1.1
    apply bot_unique
    rintro _ ⟨a,ha,rfl⟩
    apply subspaceImageRepresentation_injective ρ W
    ext w
    exact hc w.property ⟨a,ha⟩
  obtain ⟨A,hAA,hKA,hA,heq,hmin⟩ := lift_minimal_offender ρ hA₀ W hW hmove
  refine ⟨A,hAA,hKA,hA,heq,?_,hmin⟩
  rcases hL.commutator_dichotomy A with hz | he
  · have hAC : A ≤ centralizer (L : Set D) :=
      commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm A L).trans hz)
    have hAK : A ≤ subspaceKernel ρ W A₀ := by
      rw [hker]
      exact le_inf hAA hAC
    exfalso
    apply hmin.1.1.1
    apply bot_unique
    rintro _ ⟨a,ha,rfl⟩
    apply subspaceImageRepresentation_injective ρ W
    ext w
    exact (hAK ha).2 w w.property
  · simpa only [MulEquiv.toMonoidHom_eq_coe, Subgroup.Normal.map_conj_eq, iSup_const] using he

/-- The original B.5.3 action supplies both the initial moving offender and
its equal-weight lift, without assuming a nontrivial ambient actor. -/
theorem component_minimal_fixedCore [Finite D] {K : GroupClass.{u}}
    (hn : ComponentNormalizationInput.{u,v}) (hyp : FFHypothesis K ρ)
    {L : Subgroup D} (hL : IsComponent D L) :
    ∃ A₀, IsBestOffender ρ A₀ ∧ ⁅L,A₀⁆ = L ∧
      let W := fixedSpace ρ (localTwoCore L A₀)
      ∃ A ≤ A₀, subspaceKernel ρ W A₀ ≤ A ∧ IsBestOffender ρ A ∧
        EqualWeightLE ρ A A₀ ∧ ⁅L,A⁆ = L ∧
        IsMinimalBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
  let := hyp.finite_module
  let := component_normal ρ hn hyp hL
  obtain ⟨A₀,hA₀,hLA₀⟩ := component_moving ρ hn hyp hL
  exact ⟨A₀,hA₀,hLA₀,exists_minimal_fixedCore_offender ρ hyp.faithful hyp.twoCore hL hLA₀ hA₀⟩

end CFSG.Quasithin.ChapterB.PreparationSource
