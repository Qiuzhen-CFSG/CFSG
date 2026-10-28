module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefExistence
public import Theory.Representation.BinaryOffender.SimpleCoreKernel

/-!
# Faithfulness on the literal partner two-core quotient

In the noncore branch of 15.2.27, the preceding structural alternatives give
one simple-core C-component, or a conjugate pair of them, supplemented by T.
Every nontrivial irreducible binary action detects this component orbit.
The component kernel bounds then identify its full kernel with O₂(L), where
L = Kc T. Thus the chief action already constructed on L/O₂(L) is faithful
on that quotient itself, with its original section and displacement bounds.

The explicit source inputs are the wreath quotient and residual conclusions
of 15.2.8--12 and the seed/partner marking of 15.2.14. They are the same
inputs used by ChiefExistence. No transvection exclusion or action model is
assumed here. The remaining recognition and partner-core assembly belongs
to the critical-pair owner.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119
(refs/quasithin.pdf p.1136), before the B.4.2/B.4.5 classification step.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

private theorem model_simple {X : Type*} [Group X] [Group.IsPerfect X]
    {n q : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL X n q) : IsSimpleGroup X := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
  by_cases he : n = 2
  · subst n
    let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hh : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
        PSL2.Iwasawa inferInstance
    exact e.isSimpleGroup_congr.mpr hh
  · let := Atlas.psl_simple_high_rank (F := F) n (by omega)
    exact e.isSimpleGroup

omit [Finite G] in
private theorem component_model_simple {B Mc : Subgroup G}
    (hc : B ∈ Chapter1.cComponentsIn Mc) {n q : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (Chapter1.XiQuotient B) n q) :
    IsSimpleGroup (B ⧸ pCore 2 B) := by
  let := hc.2.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hc.1).toMonoidHom) (subgroupOfEquivOfLe hc.1).surjective
  let : Group.IsPerfect (B ⧸ pCore 2 B) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact model_simple hn hm

omit [Finite G] in
private theorem component_restriction_simple {B L : Subgroup G} (hBL : B ≤ L)
    [IsSimpleGroup (B ⧸ pCore 2 B)] :
    IsSimpleGroup (B.subgroupOf L ⧸ pCore 2 (B.subgroupOf L)) := by
  let e := subgroupOfEquivOfLe hBL
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).isSimpleGroup

/-- Every nontrivial irreducible binary action of the actual partner span
has exactly its two-core as kernel in the two surviving structural rows. -/
theorem source_chosen_partner_irreducible_kernel
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∀ (ρ : Representation (ZMod 2) L W) [IsIrreducible ρ],
      (∃ g, ρ g ≠ 1) → ρ.ker = pCore 2 L := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  dsimp only
  intro ρ hirr hnontrivial
  let K := (partnerSpan H Mc).subgroupOf L
  let S := (T : Subgroup G).subgroupOf L
  have hTM := hg.outside.1.1.2.trans hg.in_partner
  have hKM : partnerSpan H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner)
  have hLM : L ≤ Mc := sup_le hKM hTM
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (hLM.trans (le_normalizer_conjugateSpanBy _ _))
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype
  have hgen : K ⊔ S = ⊤ := by
    rw [← subgroupOf_sup (show partnerSpan H Mc ≤ L from le_sup_left)
      (show (T : Subgroup G) ≤ L from le_sup_right)]
    exact subgroupOf_self L
  rcases hs with he | ⟨_, hc, n, hn', hm, _⟩ | ⟨B,t,_,hc,ht,htn,he,_,hm⟩
  · exact ((source_chosen_noncore_residual_lt h hg hquotient hres hn).ne he.symm).elim
  · have hK : K.IsCComponent := hc.2.subgroupOf_of_le le_sup_left hLM
    let : IsSimpleGroup (partnerSpan H Mc ⧸ pCore 2 (partnerSpan H Mc)) :=
      component_model_simple hc (by rcases hn' with rfl | rfl <;> decide) hm
    let : IsSimpleGroup (K ⧸ pCore 2 K) := component_restriction_simple le_sup_left
    exact BinaryOffender.kernel_eq_twoCore_of_simpleCore_supplement ρ K S hK hS hgen hnontrivial
  · have hBL : B ≤ L := (show B ≤ partnerSpan H Mc from he ▸ le_sup_left).trans le_sup_left
    have hDL : B.conjBy t ≤ L := (show B.conjBy t ≤ partnerSpan H Mc from he ▸ le_sup_right).trans le_sup_left
    let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
    have hconj : (B.conjBy t).subgroupOf L = (B.subgroupOf L).conjBy tL := by
      apply map_injective L.subtype_injective
      rw [map_subgroupOf_eq_of_le hDL,map_conjBy_hom,map_subgroupOf_eq_of_le hBL]
      rfl
    have hpair : K = B.subgroupOf L ⊔ (B.subgroupOf L).conjBy tL := by
      change (partnerSpan H Mc).subgroupOf L = _
      rw [he,subgroupOf_sup hBL hDL,hconj]
    have hB : (B.subgroupOf L).IsCComponent := hc.2.subgroupOf_of_le hBL hLM
    let : IsSimpleGroup (B ⧸ pCore 2 B) := by
      rcases hm with ⟨n,_,hm⟩ | ⟨p,_,_,hm⟩
      · exact component_model_simple hc (by decide) hm
      · exact component_model_simple hc (by decide) hm
    let : IsSimpleGroup (B.subgroupOf L ⧸ pCore 2 (B.subgroupOf L)) :=
      component_restriction_simple hBL
    have hne : B.subgroupOf L ≠ (B.subgroupOf L).conjBy tL := by
      intro hh
      apply htn
      apply mem_normalizer_iff_map_conj_eq.mpr
      have hm := congrArg (Subgroup.map L.subtype) hh
      rw [map_conjBy_hom,map_subgroupOf_eq_of_le hBL] at hm
      exact hm.symm
    let : (B.subgroupOf L ⊔ (B.subgroupOf L).conjBy tL).Normal := hpair ▸ inferInstance
    exact BinaryOffender.kernel_eq_twoCore_of_conjugate_simpleCore_pair ρ
      (B.subgroupOf L) S tL hB hne hS (hpair ▸ hgen) hnontrivial


/-- In either noncore structural case, every nontrivial irreducible action
of the literal two-core quotient is faithful. -/
theorem source_chosen_partner_quotient_faithful
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∀ (σ : Representation (ZMod 2) (L ⧸ pCore 2 L) W) [IsIrreducible σ],
      (∃ g, σ g ≠ 1) → Function.Injective σ := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  dsimp only
  intro σ hi hnontrivial
  let ρ := σ.comp q
  let : IsIrreducible ρ :=
    (irreducible_comp_surjective_iff q (QuotientGroup.mk'_surjective _) σ).mpr hi
  have hmove : ∃ a, ρ a ≠ 1 := by
    obtain ⟨g,hg⟩ := hnontrivial
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) g
    exact ⟨a,hg⟩
  have hk := source_chosen_partner_irreducible_kernel h hg hquotient hres hs hn ρ hmove
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  apply bot_unique
  intro g hg
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) g
  exact (QuotientGroup.eq_one_iff a).mpr (hk ▸ (show a ∈ ρ.ker from hg))

/-- The constructed partner chief action is faithful on L/O₂(L), with the
same literal chief interval, actor, and displacement bounds. -/
theorem source_chosen_partner_faithful_chief_action
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∃ (B U : NormalNode L) (hc : B ⋖ U)
      (hU : U.val.map L.subtype ≤ twoCoreIn Mc),
      centralInvolutions T ≤ B.val.map L.subtype ∧
      let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
        (map_le_iff_le_comap.mp hU)
      letI := chief_elementary B U hc hp
      ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Section B U)),
        Function.Injective σ ∧ IsIrreducible σ ∧
        σ.comp (QuotientGroup.mk' (pCore 2 L)) = binarySectionRepresentation B U ∧
        ∃ a : L, (a : G) ∈ V ∧
          orderOf (QuotientGroup.mk' (pCore 2 L) a) = 2 ∧
          1 ≤ Module.finrank (ZMod 2)
            (LinearMap.range (σ (QuotientGroup.mk' (pCore 2 L) a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ∧
          Module.finrank (ZMod 2)
            (LinearMap.range (σ (QuotientGroup.mk' (pCore 2 L) a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ≤ 2 := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨B,U,hc,hU,hB,hσ⟩ :=
    source_chosen_partner_chief_action h hg hMc hZ hquotient hres hs hn
  refine ⟨B,U,hc,hU,hB,?_⟩
  let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,hi,he,a,ha,ho,hlo,hhi⟩ := hσ
  let := hi
  have hmove : σ (QuotientGroup.mk' (pCore 2 L) a) ≠ 1 := by
    intro hh
    rw [hh,sub_self,LinearMap.range_zero] at hlo
    simp at hlo
  have hfaith := source_chosen_partner_quotient_faithful h hg hquotient hres hs hn σ
    ⟨_,hmove⟩
  exact ⟨σ,hfaith,hi,he,a,ha,ho,hlo,hhi⟩

end CFSG.Quasithin.Chapter15.Section02
