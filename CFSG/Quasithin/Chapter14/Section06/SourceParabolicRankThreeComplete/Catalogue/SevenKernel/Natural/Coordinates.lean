module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Preparation
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SourceCore
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalSource

/-!
# Natural coordinates on the literal component-radical product

The full moved-space chart relabels the original star quotient by S₇. Its
kernel remains the centralizer of the original omega-center, and its natural
six-space embeds equivariantly in that same omega-center. Fixed summands do
not change any subgroup fixed codimension. Radical saturation and B.2.10 give
the actual kernel Sylow and its intersection with the prescribed radical.

Source: Aschbacher--Smith C.1.24(a) and C.2.7(1--2), pp.130--131, 145--146.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {G : Type*} [Group G] [Finite G] {K R H M : Subgroup G}

/-- Relabel the actual star map, rather than choosing an unrelated action. -/
noncomputable def naturalMap
    (m : AlternatingModels.ActionData (starRepresentation K R) (starImage K R K))
    (a : ActionEquiv m.sectionData.space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 7))) :
    (K ⊔ R : Subgroup G) →* Equiv.Perm (Fin 7) :=
  a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (starKernel K R))

omit [Finite G] in
theorem naturalMap_surjective
    (m : AlternatingModels.ActionData (starRepresentation K R) (starImage K R K))
    (a : ActionEquiv m.sectionData.space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 7))) :
    Function.Surjective (naturalMap m a) :=
  a.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem naturalMap_ker
    (m : AlternatingModels.ActionData (starRepresentation K R) (starImage K R K))
    (a : ActionEquiv m.sectionData.space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 7))) :
    (naturalMap m a).ker = centralizer (starV K R : Set (K ⊔ R : Subgroup G)) :=
  (MonoidHom.ker_comp_of_injective _ _ a.groupEquiv.injective).trans
    (QuotientGroup.ker_mk' _)

omit [Finite G] in
theorem naturalMap_component
    (m : AlternatingModels.ActionData (starRepresentation K R) (starImage K R K))
    (a : ActionEquiv m.sectionData.space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 7)))
    (ha : (starImage K R K).map a.groupEquiv.toMonoidHom = alternatingGroup (Fin 7)) :
    (K.subgroupOf (K ⊔ R)).map (naturalMap m a) = alternatingGroup (Fin 7) := by
  rw [naturalMap, ←map_map]
  exact ha

omit [Finite G] in
/-- The original conjugation representation in the new actor coordinates. -/
theorem naturalMap_representation
    (m : AlternatingModels.ActionData (starRepresentation K R) (starImage K R K))
    (a : ActionEquiv m.sectionData.space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 7))) (g : Equiv.Perm (Fin 7))
    (v : Additive (starV K R)) :
    NormalElementaryQuotient.representation (starV K R) (naturalMap m a)
      (naturalMap_surjective m a) (naturalMap_ker m a) g v =
      starRepresentation K R (a.groupEquiv.symm g) v := by
  obtain ⟨x, rfl⟩ := naturalMap_surjective m a g
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [NormalElementaryQuotient.representation_apply]
  change _ = ((starRepresentation K R
    (a.groupEquiv.symm (a.groupEquiv (QuotientGroup.mk' (starKernel K R) x))) v).toMul :
      (K ⊔ R : Subgroup G))
  rw [a.groupEquiv.symm_apply_apply, starRepresentation_apply]

/-- Both the fixed-codimension comparison and the actual natural embedding. -/
theorem naturalMap_module
    (m : AlternatingModels.ActionData (starRepresentation K R) (starImage K R K))
    (a : ActionEquiv m.sectionData.space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 7))) :
    let ρ := NormalElementaryQuotient.representation (starV K R) (naturalMap m a)
      (naturalMap_surjective m a) (naturalMap_ker m a)
    (∀ A, fixedCodim ρ A = fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) A) ∧
    ∃ s : BinaryPermutation.natural (Fin 7) →ₗ[ZMod 2] Additive (starV K R),
      Function.Injective s ∧ ∀ g v,
        s (BinaryPermutation.naturalRepresentation (Fin 7) g v) = ρ g (s v) := by
  let ρ := NormalElementaryQuotient.representation (starV K R) (naturalMap m a)
    (naturalMap_surjective m a) (naturalMap_ker m a)
  constructor
  · intro A
    rw [fixedCodim_map_equivariant ρ (starRepresentation K R) a.groupEquiv.symm.toMonoidHom
      (LinearEquiv.refl (ZMod 2) _) (naturalMap_representation m a) A,
      m.fixedCodim_natural (starRepresentation K R) (starImage K R K) a]
    congr 1
    rw [map_map]
    have he : a.groupEquiv.toMonoidHom.comp a.groupEquiv.symm.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro g
      exact a.groupEquiv.apply_symm_apply g
    rw [he, Subgroup.map_id]
  · refine ⟨m.naturalLift _ _ a, m.naturalLift_injective _ _ a, ?_⟩
    intro g v
    rw [naturalMap_representation]
    have hh := m.naturalLift_intertwines _ _ a (a.groupEquiv.symm g) v
    simpa only [a.groupEquiv.apply_symm_apply] using hh

/-- Source saturation places the ambient core inside the actual radical. -/
theorem relative_core_le (h : Input KnownSimple.IsKnownSimple H R M K) :
    pCore 2 (K ⊔ R : Subgroup G) ≤ R.subgroupOf (K ⊔ R) := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  have hh := source_joinCore_le_radical (source_join_input h)
  intro x hx
  exact hh (mem_map_of_mem (K ⊔ R : Subgroup G).subtype hx)

/-- The prescribed radical has the actual kernel Sylow of B.2.10; it is
not asserted to be Sylow in the component-radical product. -/
theorem naturalMap_kernel_sylow (h : Input KnownSimple.IsKnownSimple H R M K)
    (m : AlternatingModels.ActionData (starRepresentation K R) (starImage K R K))
    (a : ActionEquiv m.sectionData.space.toRepresentation
      (BinaryPermutation.naturalRepresentation (Fin 7)))
    (ha : (starImage K R K).map a.groupEquiv.toMonoidHom = alternatingGroup (Fin 7)) :
    (∃ P : Sylow 2 (naturalMap m a).ker,
      (P : Subgroup (naturalMap m a).ker).map (naturalMap m a).ker.subtype =
        pCore 2 (K ⊔ R : Subgroup G)) ∧
    R.subgroupOf (K ⊔ R) ⊓ (naturalMap m a).ker = pCore 2 (K ⊔ R : Subgroup G) := by
  let J := K ⊔ R
  let L := K.subgroupOf J
  let R₀ := R.subgroupOf J
  let V := starV K R
  let q := naturalMap m a
  let : L.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  let eL : L ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : IsQuasisimple (L ⧸ pCore 2 L) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).symm
  have hpR : IsPGroup 2 R₀ := (source_relative_radical h).isPGroup
  obtain ⟨T, hRT⟩ := hpR.exists_le_sylow
  have hgen : L ⊔ R₀ = ⊤ := by
    rw [←subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hprod : ∀ g : J, ∃ l ∈ L, ∃ t ∈ (T : Subgroup J), l*t=g := by
    intro g
    obtain ⟨l, hl, r, hr, he⟩ := mem_sup_of_normal_left.mp (hgen.ge (mem_top g))
    exact ⟨l, hl, r, hRT hr, he⟩
  have hm : ⁅V,L⁆ ≠ ⊥ := by
    intro hz
    have hfix : L ≤ q.ker := by
      rw [naturalMap_ker, ←commutator_eq_bot_iff_le_centralizer, commutator_comm]
      exact hz
    have hb : alternatingGroup (Fin 7) = ⊥ :=
      (naturalMap_component m a ha).symm.trans ((Subgroup.map_eq_bot_iff _).mpr hfix)
    have hc := congrArg (fun A : Subgroup (Equiv.Perm (Fin 7)) => Nat.card A) hb
    rw [nat_card_alternatingGroup, Nat.card_fin, card_bot] at hc
    norm_num at hc
  have hd := ChapterB.lemma_B_2_10_two V R₀ q (naturalMap_surjective m a)
    (naturalMap_ker m a) T (relative_core_le h) hRT
    ChapterC.RankOne.SevenSource.Natural.symmetric_seven_twoCore_eq_bot L
    (Or.inl ⟨(source_join_input h).component.2, inferInstance⟩) hm hprod
  have hk := naturalMap_ker m a
  have hP0 := hd.1
  have hcore := hd.2.1
  rw [←hk] at hP0 hcore
  obtain ⟨P, _, hP⟩ := hP0
  exact ⟨⟨P, hP⟩, hcore.symm⟩

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
