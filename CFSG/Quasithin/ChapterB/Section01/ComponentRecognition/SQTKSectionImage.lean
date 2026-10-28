module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.AlternatingCovers.CenterSections
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.SourceCatalogue
public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.Representation.NormalPSubgroupKernel

/-!
# The actual SQTK actor on a B.1.11 section

Retain the source containment H ≤ LA by carrying out the existing section
construction inside LA. A faithful irreducible L-action identifies L with
its literal image. The quotient of the H-image by that L-image is a
two-group. Consequently odd-prime ranks and the full known-simple K-group
condition pass to the H-image. Irreducibility kills its two-core, and the
quasisimple two-quotient theorem identifies its generalized Fitting subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.11–13,
printed pp.72–74, and B.4.2, printed p.86. The final application retains
the genuine earlier B.4.2 implication as its sole classification input.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SQTKSectionImage
open AlternatingCovers QuasisimpleSource.IrreducibleBranch

universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
private theorem local_commutator (L A : Subgroup G) (hLA : ⁅L, A⁆ = L) :
    ⁅L.subgroupOf (L ⊔ A), A.subgroupOf (L ⊔ A)⁆ = L.subgroupOf (L ⊔ A) := by
  apply Subgroup.map_injective (L ⊔ A).subtype_injective
  rw [Subgroup.map_commutator,
    map_subgroupOf_eq_of_le (show L ≤ L ⊔ A from le_sup_left),
    map_subgroupOf_eq_of_le (show A ≤ L ⊔ A from le_sup_right), hLA]

/-- B.1.11 with its already-constructed containment in LA retained. -/
theorem source_lemma_B_1_11_contained (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [IsQuasisimple L]
    (hLA : ⁅L, A⁆ = L) (hA : IsBestOffender ρ A) :
    ∃ (H : Subgroup G) (I : Submodule (ZMod 2) V),
      L ≤ H ∧ H ≤ L ⊔ A ∧ IsIrrPlus ρ L I ∧
      ∃ (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)),
        IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)) ∧
        (centralSectionRepresentation ρ L H I hHI hHN).ker.map H.subtype ≤
          H ⊓ centralizer (L : Set G) := by
  let K := L ⊔ A
  let L₀ := L.subgroupOf K
  let A₀ := A.subgroupOf K
  let : IsQuasisimple L₀ :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ K from le_sup_left)).symm
  obtain ⟨H, I, hLH, hI, hHI, hHN, hFF, hcent⟩ :=
    source_lemma_B_1_11 (ρ.comp K.subtype) (hfaith.comp K.subtype_injective)
      L₀ A₀ (local_commutator L A hLA)
      (hA.subgroupOf ρ (show A ≤ K from le_sup_right))
  refine ⟨H.map K.subtype, I, ?_, ?_,
    (IsIrrPlus.subgroupOf_iff ρ L K le_sup_left I).mp hI,
    map_stabilizes ρ K H I hHI, map_normalizes L K le_sup_left H hHN,
    section_image_isFFModule_to_ambient ρ L K le_sup_left H I hHI hHN hFF,
    section_centralizer_to_ambient ρ L K le_sup_left H I hHI hHN hcent⟩
  · have hm := Subgroup.map_mono (f := K.subtype) hLH
    rwa [map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left)] at hm
  · rintro _ ⟨h, _, rfl⟩
    exact h.property

/-- The cubic-center source construction with its containment in LA retained. -/
theorem faithful_section_of_cubic_center_contained (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [IsQuasisimple L]
    (hc : Nat.card (center L) = 3) (hLA : ⁅L, A⁆ = L) (hA : IsBestOffender ρ A) :
    ∃ (H : Subgroup G) (I : Submodule (ZMod 2) V),
      L ≤ H ∧ H ≤ L ⊔ A ∧
      ∃ (hI : IsIrrPlus ρ L I)
        (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)),
        IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)) ∧
        Function.Injective (centralQuotientRepresentation ρ L I hI.choose) := by
  let K := L ⊔ A
  let L₀ := L.subgroupOf K
  let A₀ := A.subgroupOf K
  let : IsQuasisimple L₀ :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ K from le_sup_left)).symm
  have hc₀ : Nat.card (center L₀) = 3 :=
    (Nat.card_congr (centerCongr (subgroupOfEquivOfLe
      (show L ≤ K from le_sup_left))).toEquiv).trans hc
  obtain ⟨H, I, hLH, hI, hHI, hHN, hFF, hIfaith⟩ :=
    hasFaithfulIrreducibleFFSection_of_cubic_center
      (ρ.comp K.subtype) (hfaith.comp K.subtype_injective)
      L₀ A₀ hc₀ (local_commutator L A hLA)
      (hA.subgroupOf ρ (show A ≤ K from le_sup_right))
  refine ⟨H.map K.subtype, I, ?_, ?_,
    (IsIrrPlus.subgroupOf_iff ρ L K le_sup_left I).mp hI,
    map_stabilizes ρ K H I hHI, map_normalizes L K le_sup_left H hHN,
    section_image_isFFModule_to_ambient ρ L K le_sup_left H I hHI hHN hFF,
    centralQuotientRepresentation_injective_to_ambient ρ L K le_sup_left I hI hIfaith⟩
  · have hm := Subgroup.map_mono (f := K.subtype) hLH
    rwa [map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left)] at hm
  · rintro _ ⟨h, _, rfl⟩
    exact h.property

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- On a centerless L, the original central-kernel output is already faithful. -/
theorem centralQuotient_injective_of_center_eq_bot
    (L H : Subgroup G) [IsQuasisimple L] (hLH : L ≤ H) (hc : center L = ⊥)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I)
    (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)) :
    Function.Injective (centralQuotientRepresentation ρ L I hI.choose) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro l hl
  have hk : inclusion hLH l ∈
      (centralSectionRepresentation ρ L H I hHI hHN).ker := hl
  have hz := (centralSection_kernel_le_centralizer ρ L H hLH I hI hHI hHN
    (mem_map_of_mem H.subtype hk)).2
  have hcl : l ∈ center L := mem_center_iff.mpr fun k =>
    Subtype.ext ((mem_centralizer_iff.mp hz) k k.property)
  simpa only [hc, mem_bot] using hcl

/-- The exact center alternatives supplied earlier by A.3 give a faithful section
of the original L, with no central quotient substituted for that actor. -/
theorem faithful_section_contained (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [IsQuasisimple L]
    (hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (hLA : ⁅L, A⁆ = L) (hA : IsBestOffender ρ A) :
    ∃ (H : Subgroup G) (I : Submodule (ZMod 2) V),
      L ≤ H ∧ H ≤ L ⊔ A ∧
      ∃ (hI : IsIrrPlus ρ L I)
        (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)),
        IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)) ∧
        Function.Injective (centralQuotientRepresentation ρ L I hI.choose) := by
  rcases hc with hc | hc
  · obtain ⟨H, I, hLH, hHA, hI, hHI, hHN, hFF, _⟩ :=
      source_lemma_B_1_11_contained ρ hfaith L A hLA hA
    exact ⟨H, I, hLH, hHA, hI, hHI, hHN, hFF,
      centralQuotient_injective_of_center_eq_bot ρ L H hLH
        (Subgroup.card_eq_one.mp hc) I hI hHI hHN⟩
  · exact faithful_section_of_cubic_center_contained ρ hfaith L A hc hLA hA

omit [Finite G] in
/-- The actual quotient H/L embeds in LA/L, and hence is a two-group. -/
theorem quotient_isTwoGroup_of_between (L A H : Subgroup G)
    [hLHn : (L.subgroupOf H).Normal]
    (hLA : ⁅L, A⁆ = L) (hHA : H ≤ L ⊔ A) (hA : IsPGroup 2 A) :
    IsPGroup 2 (H ⧸ L.subgroupOf H) := by
  let K := L ⊔ A
  let L₀ := L.subgroupOf K
  let : L₀.Normal := irreducibleReduction_normal L A hLA
  have hquot : IsPGroup 2 (K ⧸ L₀) := by
    apply isPGroup_quotient_of_sup_eq_top L₀ (A.subgroupOf K) hA.comap_subtype
    rw [← Subgroup.subgroupOf_sup (show L ≤ K from le_sup_left)
      (show A ≤ K from le_sup_right), Subgroup.subgroupOf_self]
  have hmap : L.subgroupOf H ≤ L₀.comap (inclusion hHA) := fun _ hl => hl
  let q := QuotientGroup.map (L.subgroupOf H) L₀ (inclusion hHA) hmap
  apply hquot.of_injective q
  apply (MonoidHom.ker_eq_bot_iff q).mp
  rw [QuotientGroup.ker_map]
  change (L.subgroupOf H).map (QuotientGroup.mk' (L.subgroupOf H)) = ⊥
  exact QuotientGroup.map_mk'_self (L.subgroupOf H)

/-- The full known-simple catalogue contains every finite simple two-group. -/
theorem knownSimple_containsSimpleTwoGroups :
    ContainsSimpleTwoGroups KnownSimple.IsKnownSimple.{u} := by
  intro S _ _ _ hp
  let : Group.IsNilpotent S := hp.isNilpotent
  exact ⟨inferInstance, inferInstance,
    .cyclic (MainConverse.primeCyclic_of_solvable_simple S)⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem irreducible_of_pullback {D : Type*} [Group D]
    (f : D →* G) (hi : IsIrreducible (ρ.comp f)) : IsIrreducible ρ := by
  let : IsIrreducible (ρ.comp f) := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp f)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (ρ.comp f) :=
    ⟨S.toSubmodule, fun d _ hv => S.apply_mem_toSubmodule (f d) hv⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (ρ.comp f) => U.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation (ρ.comp f) => U.toSubmodule) h

/-- All B.4.2 hypotheses, with the literal image of L marked inside the actual
action image. The quotient is formed using the displayed normality proof. -/
structure ImageHypotheses (L : Subgroup G) : Prop where
  normal : (actionSubgroup ρ L).Normal
  quotient : letI : (actionSubgroup ρ L).Normal := normal
    IsPGroup 2 (actionImage ρ ⧸ actionSubgroup ρ L)
  marking : ∃ e : L ≃* actionSubgroup ρ L,
    ∀ l, (e l : actionImage ρ) = actionHom ρ l
  twoCore : pCore 2 (actionImage ρ) = ⊥
  fitting : generalizedFitting (actionImage ρ) = actionSubgroup ρ L
  sqtk : IsSQTK KnownSimple.IsKnownSimple (actionImage ρ)
  quasisimple : IsQuasisimple (actionSubgroup ρ L)
  faithful : Function.Injective (imageRepresentation ρ)
  irreducible : IsIrreducible ((imageRepresentation ρ).comp (actionSubgroup ρ L).subtype)
  bestOffender : ∃ B, IsBestOffender (imageRepresentation ρ) B

/-- Passing from a faithful irreducible normal L-action to the actual action
image discharges every group and module premise of B.4.2. -/
theorem image_hypotheses (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hL : IsSQTK KnownSimple.IsKnownSimple L) (hq : IsPGroup 2 (G ⧸ L))
    (hfaith : Function.Injective (ρ.comp L.subtype))
    (hirr : IsIrreducible (ρ.comp L.subtype))
    (hFF : IsFFModule (imageRepresentation ρ)) : ImageHypotheses ρ L := by
  let M := actionSubgroup ρ L
  let f := actionHom ρ
  have hf : Function.Surjective f := ρ.asGroupHom.rangeRestrict_surjective
  let : M.Normal := Subgroup.Normal.map inferInstance f hf
  have hmap : L ≤ M.comap f := fun _ hl => mem_map_of_mem f hl
  have hqM : IsPGroup 2 (actionImage ρ ⧸ M) :=
    hq.of_surjective (QuotientGroup.map L M f hmap)
      (QuotientGroup.map_surjective_of_surjective L M f
        ((QuotientGroup.mk'_surjective M).comp hf) hmap)
  have hfix : ∀ l ∈ L, (∀ v, ρ l v = v) → l = 1 := by
    intro l hl hv
    have he : (⟨l, hl⟩ : L) = 1 := by
      apply hfaith
      change ρ l = ρ 1
      rw [map_one]
      exact LinearMap.ext hv
    exact congrArg Subtype.val he
  let e : L ≃* M := faithfulActionEquiv ρ L hfix
  let : IsQuasisimple M := IsQuasisimple.of_mulEquiv e
  have hMirr : IsIrreducible ((imageRepresentation ρ).comp M.subtype) :=
    RepEquiv.irreducible_of_group_iso e (fun _ _ => rfl) hirr
  have hi : IsIrreducible ρ := irreducible_of_pullback ρ L.subtype hirr
  have hiD : IsIrreducible (imageRepresentation ρ) :=
    irreducible_of_pullback (imageRepresentation ρ) f hi
  let : IsIrreducible (imageRepresentation ρ) := hiD
  have hcore : pCore 2 (actionImage ρ) = ⊥ := by
    have hk := normal_p_subgroup_le_ker (imageRepresentation ρ)
      (pCore 2 (actionImage ρ)) (pCore_isPGroup (p := 2))
    exact bot_unique (hk.trans ((MonoidHom.ker_eq_bot_iff _).mpr
      (imageRepresentation_injective ρ)).le)
  obtain ⟨B, hB⟩ := hFF
  obtain ⟨C, _, hC⟩ := hB.exists_bestOffender (imageRepresentation ρ)
  exact ⟨inferInstance, hqM, ⟨e, fun _ => rfl⟩, hcore,
    generalizedFitting_eq_of_quasisimple_two_quotient M hqM hcore,
    sqtk_of_twoGroup_quotient knownSimple_containsSimpleTwoGroups M hqM
      ((IsSQTK.equiv e).mp hL),
    inferInstance, imageRepresentation_injective ρ, hMirr, C, hC⟩

/-- The complete corrected B.4.2 output on this actor, retaining all marked
group, module and offender clauses of the source catalogue. -/
theorem ImageHypotheses.classification {L : Subgroup G} (h : ImageHypotheses ρ L)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase (imageRepresentation ρ)
      (actionSubgroup ρ L) (offenderSubgroup (imageRepresentation ρ)) := by
  have hF : IsQuasisimple (generalizedFitting (actionImage ρ)) :=
    h.fitting.symm ▸ h.quasisimple
  have hi : IsIrreducible ((imageRepresentation ρ).comp
      (generalizedFitting (actionImage ρ)).subtype) := by
    rw [h.fitting]
    exact h.irreducible
  simpa only [h.fitting] using
    earlier (actionImage ρ) V (imageRepresentation ρ) h.sqtk hF h.faithful hi h.bestOffender

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem centralSection_comp_subgroupOf (L H : Subgroup G) (hLH : L ≤ H)
    (I : Submodule (ZMod 2) V) (hLI : L ≤ subspaceStabilizer ρ I)
    (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)) :
    (centralSectionRepresentation ρ L H I hHI hHN).comp (L.subgroupOf H).subtype =
      (centralQuotientRepresentation ρ L I hLI).comp
        (subgroupOfEquivOfLe hLH).toMonoidHom := by
  rfl

/-- The actual B.1.11 section supplies the hypotheses, on its original maps. -/
theorem section_image_hypotheses (L A H : Subgroup G) [IsQuasisimple L]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (hLA : ⁅L, A⁆ = L) (hA : IsPGroup 2 A) (hLH : L ≤ H) (hHA : H ≤ L ⊔ A)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I)
    (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G))
    (hFF : IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)))
    (hfaith : Function.Injective (centralQuotientRepresentation ρ L I hI.choose)) :
    ImageHypotheses (centralSectionRepresentation ρ L H I hHI hHN) (L.subgroupOf H) := by
  let : (L.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  let e := subgroupOfEquivOfLe hLH
  let : IsQuasisimple (L.subgroupOf H) := IsQuasisimple.of_mulEquiv e.symm
  apply image_hypotheses _ (L.subgroupOf H) ((IsSQTK.equiv e).mpr hL)
    (quotient_isTwoGroup_of_between L A H hLA hHA hA) ?_ ?_ hFF
  · rw [centralSection_comp_subgroupOf ρ L H hLH I hI.choose hHI hHN]
    exact hfaith.comp e.injective
  · rw [centralSection_comp_subgroupOf ρ L H hLH I hI.choose hHI hHN]
    exact RepEquiv.irreducible_of_group_iso e.symm (fun _ _ => rfl) hI.choose_spec.2

/-- The complete B.1.11-to-B.4.2 bridge for the specialized B.1.13 route.
The center bound and SQTK property of L are genuine earlier A.2/A.3 inputs;
the only classification premise is the actual corrected B.4.2 producer. -/
theorem exists_classified_section (hfaith : Function.Injective ρ)
    (L A : Subgroup G) [IsQuasisimple L]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (hLA : ⁅L, A⁆ = L) (hA : IsBestOffender ρ A)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple) :
    ∃ (H : Subgroup G) (I : Submodule (ZMod 2) V),
      L ≤ H ∧ H ≤ L ⊔ A ∧
      ∃ (hI : IsIrrPlus ρ L I)
        (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)),
        let σ := centralSectionRepresentation ρ L H I hHI hHN
        let M := actionSubgroup σ (L.subgroupOf H)
        Function.Injective (centralQuotientRepresentation ρ L I hI.choose) ∧
        ImageHypotheses σ (L.subgroupOf H) ∧
        (∃ e : L ≃* M, ∀ l, imageRepresentation σ (e l) =
          centralQuotientRepresentation ρ L I hI.choose l) ∧
        SourceInduction.ProjectiveLine.IrreducibleActionCase (imageRepresentation σ) M
          (offenderSubgroup (imageRepresentation σ)) := by
  obtain ⟨H, I, hLH, hHA, hI, hHI, hHN, hFF, hf⟩ :=
    faithful_section_contained ρ hfaith L A hc hLA hA
  let : IsElementaryAbelian 2 A := hA.1.2
  have h := section_image_hypotheses ρ L A H hL hLA
    (IsElementaryAbelian.isPGroup 2 A) hLH hHA I hI hHI hHN hFF hf
  refine ⟨H, I, hLH, hHA, hI, hHI, hHN, hf, h, ?_, h.classification _ earlier⟩
  obtain ⟨e, he⟩ := h.marking
  refine ⟨(subgroupOfEquivOfLe hLH).symm.trans e, fun l => ?_⟩
  change imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)
    (e ((subgroupOfEquivOfLe hLH).symm l)) = _
  rw [he]
  rfl

end CFSG.Quasithin.ChapterB.ComponentRecognition.SQTKSectionImage
