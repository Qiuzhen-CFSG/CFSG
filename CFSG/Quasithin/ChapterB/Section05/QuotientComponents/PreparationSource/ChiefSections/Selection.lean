module

public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.ComponentStructure
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleSections
public import Theory.Representation.BinaryOffender.CubicCenterSections

/-!
# Choosing an original offender and its faithful chief section

Choose a minimal offender in the action on W = C_V(O₂(LA₀)), and lift it
with the fixed-space weight equality to a best offender A on the original V.
The actual center orders one and three supply a faithful Irr⁺ constituent;
B.1.5(3) makes it A-invariant. Equivariant embeddings lift its literal
central quotient back to V without changing A.

For the offender clause of B.1.5(8), the central-section kernel centralizes L,
so C_A(W) = C_A(L) identifies the kernels of A on W and on the section.
Their image ranks therefore agree. The fixed-codimension inequalities for
nested invariant spaces and quotients make the section image an offender,
and it contains a best offender. This argument retains containment in the
literal quotient offender image, including a possibly nontrivial original
kernel; it does not replace A by an unrelated section offender.

`exists_chiefSection` supplies the section and offender premises used by
`PreparationSource.chief` in the parent ChiefSections module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.5(1iii), printed pp.104–105; B.1.5(3,8), printed pp.69–70.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.PreparationSource.ChiefSections
open SourceInduction ComponentReduction ComponentReduction.PreliminaryActions Preparation
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

private theorem perfect_twoResidual (X : Type*) [Group X] [Finite X] [Group.IsPerfect X] :
    pResidual 2 X = ⊤ := by
  apply (pResidual_eq_top_iff 2 X).mpr
  intro N hN hp
  let := hN
  have hsub : Subsingleton (X ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (X ⧸ N) hp.isNilpotent
  apply top_unique
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem faithful_constituent [Finite D] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (L : Subgroup D) [IsQuasisimple L]
    (hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3) :
    ∃ I, ∃ hI : IsIrrPlus ρ L I,
      Function.Injective (centralQuotientRepresentation ρ L I hI.choose) := by
  rcases hc with hc | hc
  · let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    obtain ⟨I, hI⟩ := exists_isIrrPlus_of_faithful ρ hf L
      ((nontrivial_iff_ne_bot L).mp inferInstance)
    refine ⟨I, hI, (MonoidHom.ker_eq_bot_iff _).mp (bot_unique ?_)⟩
    intro l hl
    have hz := (centralSection_kernel_le_centralizer ρ L L le_rfl I hI
      hI.choose L.le_normalizer (mem_map_of_mem L.subtype hl)).2
    have hh : l ∈ center L := mem_center_iff.mpr fun k =>
      Subtype.ext ((mem_centralizer_iff.mp hz) k k.property)
    simpa only [Subgroup.card_eq_one.mp hc, mem_bot] using hh
  · exact exists_faithful_isIrrPlus_of_cubic_center ρ L
      (hf.comp L.subtype_injective) hc

/-- Lift a faithful minimal-offender-invariant constituent to the original V,
retaining original best-offender status and minimality on the fixed space. -/
theorem invariant_faithful_constituent [Finite D] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (h2 : pCore 2 D = ⊥)
    {L A₀ : Subgroup D} (hL : IsComponent D L) [L.Normal]
    (hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (hA₀ : IsBestOffender ρ A₀) (hm₀ : ⁅L,A₀⁆ = L) :
    ∃ A ≤ A₀, IsBestOffender ρ A ∧ ⁅L,A⁆ = L ∧
      IsMinimalBestOffender
        (subspaceImageRepresentation ρ (fixedSpace ρ (localTwoCore L A₀)))
        (restrictedSubgroup ρ (fixedSpace ρ (localTwoCore L A₀)) A) ∧
      ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I),
        I ≤ fixedSpace ρ (localTwoCore L A₀) ∧
        L ⊔ A ≤ subspaceStabilizer ρ I ∧
        Function.Injective (centralQuotientRepresentation ρ L I hI.choose) := by
  let := hL.2
  let W := fixedSpace ρ (localTwoCore L A₀)
  have hQ : L ⊔ A₀ ≤ normalizer (localTwoCore L A₀ : Set D) := by
    simpa only [localTwoCore, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 ↥(L ⊔ A₀)).le_normalizer_map (L ⊔ A₀).subtype
  have hW : L ⊔ A₀ ≤ subspaceStabilizer ρ W := fixedSpace_invariant_normalizer ρ hQ
  obtain ⟨A, hAA, _, hA, _, hm, hmin⟩ :=
    exists_minimal_fixedCore_offender ρ hf h2 hL hm₀ hA₀
  obtain ⟨hfL, _, _⟩ := fixedCore ρ hf h2 L A₀ hm₀ hA₀
  have hLW : L ≤ subspaceStabilizer ρ W := le_sup_left.trans hW
  have hAW : A ≤ subspaceStabilizer ρ W := hAA.trans (le_sup_right.trans hW)
  let P := subspaceStabilizer ρ W
  let τ := ρ.comp P.subtype
  let σ := subspaceImageRepresentation ρ W
  let f := subspaceActionHom ρ W
  let L₀ := L.subgroupOf P
  let Lw := restrictedSubgroup ρ W L
  have hf₀ : Function.Injective (f.subgroupMap L₀) := by
    apply (injective_iff_map_eq_one _).mpr
    intro l hl
    apply Subtype.ext
    apply Subtype.ext
    apply hfL l l.property
    intro w hw
    exact congrArg Subtype.val (congrArg (fun q => σ q (⟨w, hw⟩ : W))
      (congrArg Subtype.val hl))
  let e : L ≃* Lw := (subgroupOfEquivOfLe hLW).symm.trans
    (MulEquiv.ofBijective (f.subgroupMap L₀) ⟨hf₀, f.subgroupMap_surjective L₀⟩)
  let : IsQuasisimple Lw := IsQuasisimple.of_mulEquiv e
  have hcw : Nat.card (center Lw) = 1 ∨ Nat.card (center Lw) = 3 := by
    rw [← Nat.card_congr (centerCongr e).toEquiv]
    exact hc
  obtain ⟨I, hI, hfaith⟩ := faithful_constituent σ
    (subspaceImageRepresentation_injective ρ W) Lw hcw
  have hiA : restrictedSubgroup ρ W A ≤ subspaceStabilizer σ I :=
    source_lemma_B_1_5_3 σ (subspaceImageRepresentation_injective ρ W) hmin
      (perfect_twoResidual Lw) (restrictedSubgroup_commutator ρ W hLW hAW hm)
      (hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
        (⊥ : Subgroup Lw) (by simp)
        (IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm)) hI
  let J := I.map W.subtype
  have hJ₀ : IsIrrPlus τ L₀ J :=
    IsIrrPlus.map_embedding τ σ f W.subtype W.subtype_injective
      (fun _ _ => rfl) L₀ I hI
  have hJ : IsIrrPlus ρ L J := (IsIrrPlus.subgroupOf_iff ρ L P hLW J).mp hJ₀
  have hAJ₀ : A.subgroupOf P ≤ subspaceStabilizer τ J :=
    map_subspace_invariant τ σ f W.subtype (fun _ _ => rfl) (A.subgroupOf P) I hiA
  have hAJ : A ≤ subspaceStabilizer ρ J := by
    intro a ha
    exact hAJ₀ (show (⟨a, hAW ha⟩ : P) ∈ A.subgroupOf P from ha)
  have hfaith₀ := centralQuotientRepresentation_injective_map_embedding τ σ f W.subtype
    W.subtype_injective (fun _ _ => rfl) L₀ hf₀ I hI.choose hfaith
  exact ⟨A, hAA, hA, hm, hmin, J, hJ, Submodule.map_subtype_le _ _, sup_le hJ.choose hAJ,
    centralQuotientRepresentation_injective_to_ambient ρ L P hLW J hJ₀ hfaith₀⟩

/-- The literal I/C_I(L) as an A-invariant L-chief section of V. -/
noncomputable def sectionOfConstituent {L A : Subgroup D} [L.Normal]
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I)
    (hIA : L ⊔ A ≤ subspaceStabilizer ρ I)
    (hf : Function.Injective (centralQuotientRepresentation ρ L I hI.choose)) :
    ChiefSection ρ A L where
  upper := invariantSubspace ρ (L ⊔ A) I hIA
  lower := centralSectionFixedSubspace ρ L (L ⊔ A) I hIA le_normalizer_of_normal
  faithful := hf
  irreducible := hI.choose_spec.2

private theorem fixedCodim_subrepresentation_mono [Module.Finite (ZMod 2) V]
    (U W : Subrepresentation ρ) (hUW : U ≤ W) (B : Subgroup D) :
    fixedCodim U.toRepresentation B ≤ fixedCodim W.toRepresentation B := by
  have hu := fixedCodim_add_finrank U.toRepresentation B
  have hw := fixedCodim_add_finrank W.toRepresentation B
  have heu := (subrepresentationFixedEquiv ρ U B).finrank_eq
  have hew := (subrepresentationFixedEquiv ρ W B).finrank_eq
  have hsu := U.toSubmodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ B)
  have hsw := W.toSubmodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ B)
  have hle := Submodule.finrank_mono
    (sup_le_sup_right (show U.toSubmodule ≤ W.toSubmodule from hUW) (fixedSpace ρ B))
  omega

/-- Equality of the two relative A-kernels preserves image rank; section
codimension then supplies a best offender inside the literal A-image. -/
theorem section_contains_offender [Finite D] [Module.Finite (ZMod 2) V]
    {L A : Subgroup D} [L.Normal] [IsQuasisimple L]
    (hA : IsElementaryAbelian 2 A)
    (W I : Submodule (ZMod 2) V) (hW : L ⊔ A ≤ subspaceStabilizer ρ W)
    (hker : subspaceKernel ρ W A = A ⊓ centralizer (L : Set D))
    (hbest : IsBestOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A))
    (hI : IsIrrPlus ρ L I) (hIW : I ≤ W)
    (hIA : L ⊔ A ≤ subspaceStabilizer ρ I)
    (hf : Function.Injective (centralQuotientRepresentation ρ L I hI.choose)) :
    let s := sectionOfConstituent ρ I hI hIA hf
    ∃ B ≤ s.offender, IsBestOffender s.action B := by
  let s := sectionOfConstituent ρ I hI hIA hf
  let H := L ⊔ A
  let B := A.subgroupOf H
  let τ := ρ.comp H.subtype
  let U := invariantSubspace ρ H W hW
  let σ := subspaceImageRepresentation ρ W
  let f : H →* subspaceActionImage ρ W :=
    (subspaceActionHom ρ W).comp (inclusion hW)
  have hmap : B.map f = restrictedSubgroup ρ W A := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, hW a.property⟩, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, (le_sup_right : A ≤ H) ha⟩, ha, rfl⟩
  have hfix : ∀ a : H, f a = 1 ↔ ∀ w ∈ W, ρ a w = w := by
    intro a
    constructor
    · intro ha w hw
      exact congrArg Subtype.val (congrArg (fun g => σ g (⟨w,hw⟩ : W)) ha)
    · intro ha
      apply subspaceImageRepresentation_injective ρ W
      ext w
      exact ha w w.property
  have hk : ∀ a ∈ B, s.projection a = 1 ↔ f a = 1 := by
    intro a ha
    constructor
    · intro hq
      have hs : a ∈ (centralSectionRepresentation ρ L H I hIA le_normalizer_of_normal).ker := by
        change s.lower.quotientRepresentation a = 1
        exact (congrArg s.action hq).trans s.action.map_one
      have hc := (centralSection_kernel_le_centralizer ρ L H le_sup_left I hI hIA
        le_normalizer_of_normal (mem_map_of_mem H.subtype hs)).2
      exact (hfix a).mpr (show ∀ w ∈ W, ρ a w = w from
        ((hker.symm ▸ (show (a : D) ∈ A ⊓ centralizer (L : Set D) from ⟨ha,hc⟩)) :
          (a : D) ∈ subspaceKernel ρ W A).2)
    · intro hfa
      apply (QuotientGroup.eq_one_iff a).mpr
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with | _ x =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      apply Subtype.ext
      exact (hfix a).mp hfa x (hIW x.property)
  have hcard : Nat.card s.offender = Nat.card (restrictedSubgroup ρ W A) := by
    rw [← hmap]
    change Nat.card (B.map s.projection) = Nat.card (B.map f)
    rw [← relIndex_ker, ← relIndex_ker]
    unfold relIndex
    congr 1
    ext a
    exact hk a a.property
  have hne : s.offender ≠ ⊥ := by
    intro hb
    apply hbest.1.1
    rw [← hmap]
    apply (map_eq_bot_iff B).mpr
    intro a ha
    exact (hk a ha).mp ((map_eq_bot_iff B).mp hb ha)
  let := hA
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf (show A ≤ H from le_sup_right)
  have helem : IsElementaryAbelian 2 s.offender := IsElementaryAbelian.map s.projection
  have hcodim : fixedCodim s.action s.offender ≤
      fixedCodim σ (restrictedSubgroup ρ W A) := by
    have hq := fixedCodim_quotient_add_subrepresentation_le s.upper.toRepresentation s.lower B
    have hu := fixedCodim_subrepresentation_mono τ s.upper U hIW B
    have he : fixedCodim U.toRepresentation B = fixedCodim σ (restrictedSubgroup ρ W A) := by
      change fixedCodim (σ.comp f) B = _
      unfold fixedCodim
      rw [fixedSpace_comp_map, hmap]
    have heq : fixedCodim s.lower.quotientRepresentation B = fixedCodim s.action s.offender := by
      change fixedCodim (s.action.comp s.projection) B = _
      unfold fixedCodim
      rw [fixedSpace_comp_map]
      rfl
    omega
  have ho : IsOffender s.action s.offender :=
    ⟨⟨hne, helem⟩, hcodim.trans (by
      simpa only [rank, hcard] using (hbest.isOffender σ).2)⟩
  exact ho.exists_bestOffender s.action

/-- The existential, offender-preserving B.5.5(1iii) section construction.
The original offender is chosen before lifting its faithful constituent. -/
theorem exists_chiefSection [Finite D] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (h2 : pCore 2 D = ⊥)
    {L A₀ : Subgroup D} (hL : IsComponent D L) [L.Normal]
    (hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (hA₀ : IsBestOffender ρ A₀) (hm₀ : ⁅L,A₀⁆ = L) :
    ∃ A, IsBestOffender ρ A ∧ ⁅L,A⁆ = L ∧
      ∃ s : ChiefSection ρ A L, ∃ B ≤ s.offender, IsBestOffender s.action B := by
  let := hL.2
  obtain ⟨A, hAA, hA, hm, hmin, I, hI, hIW, hIA, hfaith⟩ :=
    invariant_faithful_constituent ρ hf h2 hL hc hA₀ hm₀
  let W := fixedSpace ρ (localTwoCore L A₀)
  have hQ : L ⊔ A₀ ≤ normalizer (localTwoCore L A₀ : Set D) := by
    simpa only [localTwoCore, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 ↥(L ⊔ A₀)).le_normalizer_map (L ⊔ A₀).subtype
  have hW : L ⊔ A ≤ subspaceStabilizer ρ W :=
    (sup_le_sup_left hAA L).trans (fixedSpace_invariant_normalizer ρ hQ)
  have hk₀ := (fixedCore ρ hf h2 L A₀ hm₀ hA₀).2.1
  have hk : subspaceKernel ρ W A = A ⊓ centralizer (L : Set D) := by
    ext a
    constructor
    · rintro ⟨ha, hfix⟩
      exact ⟨ha, (hk₀ ▸ (show a ∈ subspaceKernel ρ W A₀ from ⟨hAA ha, hfix⟩)).2⟩
    · rintro ⟨ha, hc⟩
      exact ⟨ha, (hk₀.symm ▸ (show a ∈ A₀ ⊓ centralizer (L : Set D) from ⟨hAA ha,hc⟩)).2⟩
  exact ⟨A, hA, hm, sectionOfConstituent ρ I hI hIA hfaith,
    section_contains_offender ρ hA.1.2 W I hW hk hmin.1 hI hIW hIA hfaith⟩

end CFSG.Quasithin.ChapterB.PreparationSource.ChiefSections
