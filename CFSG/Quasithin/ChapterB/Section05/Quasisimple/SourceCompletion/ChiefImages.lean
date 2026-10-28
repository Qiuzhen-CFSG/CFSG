module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.ChiefFlag
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.CenterBounds
public import Theory.Representation.BinaryOffender.KernelQuotient
public import Theory.Representation.Quotient
public import Theory.Representation.NormalPSubgroupKernel

/-!
# Faithful chief images and strict dimension recursion

A noncentral chief factor has a possibly nontrivial central kernel. Its
quotient by that kernel, in the original group universe, has quasisimple
component, trivial two-core and the required two-group quotient. The genuine
A.2.1 input passes SQTK to the component section. B.1.5(8) supplies a contained
best offender, whose overgroup satisfies every B.5.1 source hypothesis.

Every noncentral factor of the constructed LA-chief flag therefore supports
a strict smaller-dimension induction application. No faithfulness is asserted
for the original covering component, and no universal B.5.1 classifier is
assumed: the recursive premise is restricted by the actual dimension bound.

Source: Aschbacher--Smith, B.5.1, printed p.100, immediately after (+).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped BigOperators ENNReal IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
open SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

namespace ChiefImage
open KernelQuotient

def component (L : Subgroup G) : Subgroup (Actor ρ) := L.map (projection ρ)

theorem irreducible (hi : IsIrreducible ρ) : IsIrreducible (action ρ) :=
  (irreducible_comp_surjective_iff (projection ρ) (projection_surjective ρ) (action ρ)).mp hi

theorem component_ne_bot (L : Subgroup G)
    (hn : subspaceCommutator ρ ⊤ L ≠ ⊥) : component ρ L ≠ ⊥ := by
  intro he
  apply hn
  apply (subspaceCommutator_eq_bot_iff ρ ⊤ L).mpr
  intro v _ l
  have hp : projection ρ l = 1 := (map_eq_bot_iff L).mp he l.property
  have hh := congrArg (fun x => action ρ x v) hp
  change ρ l v = v
  simpa only [action_projection, map_one, Module.End.one_apply] using hh

theorem component_normal (L : Subgroup G) [L.Normal] : (component ρ L).Normal :=
  Subgroup.Normal.map inferInstance (projection ρ) (projection_surjective ρ)

theorem component_quasisimple (L : Subgroup G) [IsQuasisimple L]
    (hn : subspaceCommutator ρ ⊤ L ≠ ⊥) : IsQuasisimple (component ρ L) := by
  let : Nontrivial (component ρ L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr (component_ne_bot ρ L hn)
  exact IsQuasisimple.of_surjective ((projection ρ).subgroupMap L)
    ((projection ρ).subgroupMap_surjective L)

theorem component_quotient_isTwoGroup (L : Subgroup G) [L.Normal]
    (hq : IsPGroup 2 (G ⧸ L)) :
    let := component_normal ρ L
    IsPGroup 2 (Actor ρ ⧸ component ρ L) := by
  let := component_normal ρ L
  have hm : L ≤ (component ρ L).comap (projection ρ) :=
    fun _ hl => mem_map_of_mem (projection ρ) hl
  exact hq.of_surjective (QuotientGroup.map L (component ρ L) (projection ρ) hm)
    (QuotientGroup.map_surjective_of_surjective _ _ (projection ρ)
      ((QuotientGroup.mk'_surjective _).comp (projection_surjective ρ)) hm)

theorem twoCore_eq_bot [Finite G] [FiniteDimensional (ZMod 2) V]
    (hi : IsIrreducible ρ) : pCore 2 (Actor ρ) = ⊥ := by
  let := irreducible ρ hi
  exact bot_unique ((normal_p_subgroup_le_ker (action ρ) (pCore 2 (Actor ρ))
    (pCore_isPGroup (p := 2))).trans ((MonoidHom.ker_eq_bot_iff _).mpr (faithful ρ)).le)

theorem fitting_eq_component [Finite G] [FiniteDimensional (ZMod 2) V]
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hi : IsIrreducible ρ) (hn : subspaceCommutator ρ ⊤ L ≠ ⊥)
    (hq : IsPGroup 2 (G ⧸ L)) : generalizedFitting (Actor ρ) = component ρ L := by
  let := component_normal ρ L
  let := component_quasisimple ρ L hn
  exact generalizedFitting_eq_of_quasisimple_two_quotient (component ρ L)
    (component_quotient_isTwoGroup ρ L hq) (twoCore_eq_bot ρ hi)

theorem component_sqtk [Finite G] {K : GroupClass.{u}}
    (hA : SemisimpleInput K) (L : Subgroup G) [IsQuasisimple L]
    (hL : IsSQTK K L) (hn : subspaceCommutator ρ ⊤ L ≠ ⊥) :
    IsSQTK K (component ρ L) := by
  let := component_quasisimple ρ L hn
  exact quasisimple_section_sqtk hA hL
    (ChapterA.Section02.IsSectionOf.of_surjective ((projection ρ).subgroupMap L)
      ((projection ρ).subgroupMap_surjective L))

end ChiefImage

/-- B.5.1 applies to the original representation restricted to LB whenever
L is the quasisimple generalized Fitting subgroup and B is a best offender. -/
theorem local_source_hypothesis [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (L : Subgroup G) [IsQuasisimple L]
    (hL : IsSQTK K L) (hf : generalizedFitting G = L)
    (hcore : pCore 2 G = ⊥) (hfaith : Function.Injective ρ)
    {B : Subgroup G} (hB : IsBestOffender ρ B) :
    QuasisimpleSourceHypothesis (ρ.comp (L ⊔ B).subtype) K (L.subgroupOf (L ⊔ B)) := by
  let : L.Normal := hf ▸ generalizedFitting_normal (G := G)
  let H := L ⊔ B
  let C := L.subgroupOf H
  let J := offenderSubgroup (ρ.comp H.subtype)
  let : J.Normal := offenderSubgroup_normal _
  have hAJ : B.subgroupOf H ≤ J := (hB.subgroupOf ρ le_sup_right).le_offenderSubgroup _
  have hp : IsPGroup 2 B := hB.1.2.isPGroup 2 B
  have hquasi : IsQuasisimple (generalizedFitting G) := hf.symm ▸ inferInstance
  have hcomm : ⁅L, B⁆ = L := by
    simpa only [hf] using QuasisimpleSections.commutator_fitting_eq hcore hquasi hB.1.1 hp
  have hc : ⁅C, B.subgroupOf H⁆ = C := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show B ≤ H from le_sup_right), hcomm]
  have hCJ : C ≤ J := by
    rw [← hc]
    exact (commutator_mono le_rfl hAJ).trans (commutator_le_right _ _)
  have hgen : J = ⊤ := by
    apply top_unique
    rw [← subgroupOf_self H, subgroupOf_sup (show L ≤ H from le_sup_left)
      (show B ≤ H from le_sup_right)]
    exact sup_le hCJ hAJ
  have hcenter : center G ≤ L := by
    rw [← hf]
    exact le_trans (show center G ≤ fittingSubgroup G from
      le_sSup ⟨inferInstance, inferInstance⟩) le_sup_left
  have hf' : generalizedFitting G = L ⊔ center G := by rw [hf, sup_of_le_left hcenter]
  have hfit : generalizedFitting H = C :=
    IrreducibleBranch.local_generalizedFitting L B hf' hcore hp
  refine ⟨inferInstance, hfaith.comp H.subtype_injective,
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm,
    (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))).mpr hL,
    ?_, IrreducibleBranch.local_twoCore_eq_bot L H hf' hcore le_sup_left, hgen⟩
  rw [hfit]
  apply (sup_of_le_left ?_).symm
  rw [← hfit]
  exact le_trans (show center H ≤ fittingSubgroup H from
    le_sSup ⟨inferInstance, inferInstance⟩) le_sup_left



/-- The full chief-section kernel is central in F*, rather than silently
being identified with the trivial subgroup. -/
theorem section_kernel_central [Finite G]
    (hL : IsQuasisimple (generalizedFitting G))
    (hn : subspaceCommutator ρ ⊤ (generalizedFitting G) ≠ ⊥) :
    (actionHom ρ).ker ≤ (center (generalizedFitting G)).map (generalizedFitting G).subtype := by
  apply QuasisimpleSections.kernel_le_fitting_center hL (actionHom ρ)
  intro hker
  apply hn
  apply (subspaceCommutator_eq_bot_iff ρ ⊤ (generalizedFitting G)).mpr
  intro v _ l
  change ρ l v = v
  exact (actionHom_eq_one_iff ρ l).mp (hker l.property) v

/-- B.1.5(8) on the literal kernel quotient, with the offender containment
retained under the actual quotient projection. -/
theorem section_bestOffender [Finite G] [FiniteDimensional (ZMod 2) V]
    (hfaith : Function.Injective ρ)
    (hL : IsQuasisimple (generalizedFitting G)) (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    {U W : Subrepresentation ρ} (hUW : U ≤ W)
    (hn : subspaceCommutator (sectionRepresentation ρ U W) ⊤ (generalizedFitting G) ≠ ⊥) :
    ∃ B ≤ A.map (KernelQuotient.projection (sectionRepresentation ρ U W)),
      IsBestOffender (KernelQuotient.action (sectionRepresentation ρ U W)) B := by
  let τ := sectionRepresentation ρ U W
  obtain ⟨B, hBA, hB⟩ := (source_lemma_B_1_5_8 ρ hfaith hA hL hcore hUW hn).2.2.1
  refine ⟨B.map (KernelQuotient.equiv τ).symm.toMonoidHom, ?_,
    KernelQuotient.bestOffender_transport τ hB⟩
  exact (Subgroup.map_mono hBA).trans_eq (KernelQuotient.actionSubgroup_transport τ A)

/-- Strict descent for every noncentral member of the constructed source flag. -/
theorem ReducibleChiefFlag.strictDimension [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (f : ReducibleChiefFlag ρ L) {i : ℕ} (hi : i ∈ f.noncentral) :
    sectionDimension ρ (f.chain i) (f.chain (i + 1)) < Module.finrank (ZMod 2) V := by
  obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne f.multiple i
  exact sectionDimension_lt_of_second_factor ρ f.chain f.monotone f.length
    ((f.mem_noncentral i).mp hi).1 ((f.mem_noncentral j).mp hj).1 hji.symm
    (f.chief j ((f.mem_noncentral j).mp hj).1).lt

/-- The complete source conclusion for the actual offender overgroup. -/
def LocalSourceConclusion (L B : Subgroup G) : Prop :=
  Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
    (ρ.comp (L ⊔ B).subtype) (L.subgroupOf (L ⊔ B)))

/-- The induction hypothesis on strictly smaller module dimensions. -/
def SmallerDimensionInput (K : GroupClass.{u}) (d : ℕ) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (W : Type v) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (δ : Representation (ZMod 2) D W) (C : Subgroup D),
    Module.finrank (ZMod 2) W < d → QuasisimpleSourceHypothesis δ K C →
      Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion δ C)

/-- Apply the strict induction hypothesis after proving all source hypotheses
on the actual component/offender overgroup in the faithful kernel quotient. -/
theorem recursive_action_image [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} {d : ℕ} (hsemisimple : SemisimpleInput K)
    (ih : SmallerDimensionInput.{u,v} K d)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hL : IsSQTK K L) (hi : IsIrreducible ρ)
    (hn : subspaceCommutator ρ ⊤ L ≠ ⊥) (hq : IsPGroup 2 (G ⧸ L))
    (hd : Module.finrank (ZMod 2) V < d)
    {B : Subgroup (KernelQuotient.Actor ρ)} (hB : IsBestOffender (KernelQuotient.action ρ) B) :
    LocalSourceConclusion (KernelQuotient.action ρ) (ChiefImage.component ρ L) B := by
  let C := ChiefImage.component ρ L
  let : IsQuasisimple C := ChiefImage.component_quasisimple ρ L hn
  have hC := ChiefImage.component_sqtk ρ hsemisimple L hL hn
  have hs := local_source_hypothesis (KernelQuotient.action ρ) C hC
    (ChiefImage.fitting_eq_component ρ L hi hn hq)
    (ChiefImage.twoCore_eq_bot ρ hi) (KernelQuotient.faithful ρ) hB
  exact ih ↥(C ⊔ B) V ((KernelQuotient.action ρ).comp (C ⊔ B).subtype)
    (C.subgroupOf (C ⊔ B)) hd hs

/-- The literal source conclusion at a section, with the offender still
contained in the original offender's quotient image. -/
def ChiefFactorConclusion (L A : Subgroup G) (U W : Subrepresentation ρ) : Prop :=
  let τ := sectionRepresentation ρ U W
  ∃ B : Subgroup (KernelQuotient.Actor τ),
    B ≤ A.map (KernelQuotient.projection τ) ∧
    IsBestOffender (KernelQuotient.action τ) B ∧
    LocalSourceConclusion (KernelQuotient.action τ) (ChiefImage.component τ L) B

/-- Every noncentral member of the full flag is an actual strict induction
application, using its own faithful kernel quotient and contained offender. -/
theorem recursive_flag_factor [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hsemisimple : SemisimpleInput K)
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    (hfaith : Function.Injective ρ) [IsQuasisimple (generalizedFitting G)]
    (hsq : IsSQTK K (generalizedFitting G)) (hcore : pCore 2 G = ⊥)
    (hq : IsPGroup 2 (G ⧸ generalizedFitting G))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (f : ReducibleChiefFlag ρ (generalizedFitting G)) {i : ℕ} (hi : i ∈ f.noncentral) :
    ChiefFactorConclusion ρ (generalizedFitting G) A (f.chain i) (f.chain (i + 1)) := by
  let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
  have hn := ((f.mem_noncentral i).mp hi).2
  have hiτ := f.irreducible ρ ((f.mem_noncentral i).mp hi).1
  obtain ⟨B, hBA, hB⟩ := section_bestOffender ρ hfaith inferInstance hcore hA
    (f.chief i ((f.mem_noncentral i).mp hi).1).le hn
  exact ⟨B, hBA, hB, recursive_action_image τ hsemisimple ih (generalizedFitting G)
    hsq hiτ hn hq (f.strictDimension ρ hi) hB⟩

/-- Genuine recursive applicability at every noncentral LA-chief factor.
`ih` is the strict smaller-dimension induction hypothesis, not a universal
B.5.1 input. All source hypotheses on the literal LB actor are proved here. -/
theorem recursive_chief_factor [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} {L : Subgroup G}
    (hsemisimple : SemisimpleInput K) (h : QuasisimpleSourceHypothesis ρ K L)
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (f : ReducibleChiefFlag (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A)))
    {i : ℕ} (hi : i ∈ f.noncentral) :
    ChiefFactorConclusion (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A))
      (A.subgroupOf (L ⊔ A)) (f.chain i) (f.chain (i + 1)) := by
  classical
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let H := L ⊔ A
  let σ := ρ.comp H.subtype
  have hp : IsPGroup 2 A := hA.1.1.2.isPGroup 2 A
  have hfit : generalizedFitting H = L.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hp
  have hcore : pCore 2 H = ⊥ :=
    IrreducibleBranch.local_twoCore_eq_bot L H h.fitting h.twoCore le_sup_left
  let : IsQuasisimple (L.subgroupOf H) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm
  let : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hfsq : IsSQTK K (generalizedFitting H) := by
    rw [hfit]
    exact (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))).mpr h.sqtk
  have hfaith : Function.Injective σ := h.faithful.comp H.subtype_injective
  have hq : IsPGroup 2 (H ⧸ generalizedFitting H) := by
    exact (IrreducibleBranch.local_quotient_isTwoGroup L A hp).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hfit.symm)
  exact recursive_flag_factor σ hsemisimple ih hfaith hfsq hcore hq
    (hA.1.subgroupOf ρ (show A ≤ H from le_sup_right)) f hi

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
