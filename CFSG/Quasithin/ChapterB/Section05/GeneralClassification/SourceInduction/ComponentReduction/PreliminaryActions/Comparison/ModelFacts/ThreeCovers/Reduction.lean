module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Centers
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Transport
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# Reduction of the odd-degree SL₃ comparison to the binary central cover

The literal seed quotient acts on U. If its central denominator is zero, the
natural action on the B.5.1 section becomes the actual L-action on U. For field
degree greater than one, the proved natural-module cohomology calculation makes
that denominator zero. Offender generation then makes the component image the
whole quotient. At degree one, the retained B.5.1 outer-extension alternatives
and the order-168 argument independently give the same whole-quotient conclusion.
Thus the original A induces inner automorphisms of the original L in both cases.

The Irr⁺ assertion is transported through the literal quotient map and U → V.
The terminal theorem consumes the complete earlier source conclusion and its
linear-three row. It leaves precisely degree one with a nonzero central
subspace; it does not claim the dimension-four or offender statements in this
remaining case. Those must still be proved before the full comparison is done.
The hypothesis [U,L⁺] = U is retained for its independent producer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.107, cases (IV)–(V); I.1.5–6, printed p.408; B.4.8(2), printed p.91.
The cohomology and whole-actor lemmas reused below have actual natural-action
identifications. No legacy triple-cover offender clause is used.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences
universe u v
variable {D : Type u} [Group D] {U : Type v} [AddCommGroup U] [Module (ZMod 2) U]
  {σ : Representation (ZMod 2) D U}

/-- Removing a zero central denominator from a full moved section retains the
whole ambient action, not just the component action. -/
noncomputable def wholeSectionEquiv {M : Subgroup D} (s : MovedSection σ M)
    (hm : moved σ M = ⊤) (hz : fixedSpace σ M = ⊥) : ActionEquiv σ s.action := by
  have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans hm
  have hc : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply bot_unique
    intro v hv
    apply Subtype.ext
    exact hz.le (show (v : U) ∈ fixedSpace σ M from fun g => congrArg Subtype.val (hv g))
  let e : s.space.toSubmodule ≃ₗ[ZMod 2] U :=
    LinearEquiv.ofBijective s.space.toSubmodule.subtype ⟨Subtype.val_injective,
      fun v => ⟨⟨v, hs.symm ▸ Submodule.mem_top⟩, rfl⟩⟩
  let q := s.central.toSubmodule.quotEquivOfEqBot hc
  refine ⟨MulEquiv.refl D, e.symm.trans q.symm, ?_⟩
  intro g v
  apply q.injective
  change e.symm (σ g v) = q (MovedSection.action σ s g (q.symm (e.symm v)))
  have hq (w : s.space.toSubmodule ⧸ s.central.toSubmodule) :
      q (MovedSection.action σ s g w) = s.space.toRepresentation g (q w) := by
    induction w using Submodule.Quotient.induction_on with | _ w => rfl
  rw [hq, q.apply_symm_apply]
  apply e.injective
  rw [e.apply_symm_apply]
  change σ g v = σ g (e (e.symm v))
  rw [e.apply_symm_apply]

/-- Composition retains the group identification and a compatible linear map. -/
def transAction {H W J X : Type*} [Group H] [Group J]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    {τ : Representation (ZMod 2) H W} {υ : Representation (ZMod 2) J X}
    (e : ActionEquiv σ τ) (f : ActionEquiv τ υ) : ActionEquiv σ υ where
  groupEquiv := e.groupEquiv.trans f.groupEquiv
  linearEquiv := e.linearEquiv.trans f.linearEquiv
  intertwines g v := (congrArg f.linearEquiv (e.intertwines g v)).trans (f.intertwines _ _)

set_option backward.isDefEq.respectTransparency false in
/-- With zero central denominator, a natural quotient is the natural action
on the whole module. -/
noncomputable def naturalOfWholeSection {M : Subgroup D} (s : MovedSection σ M)
    (hm : moved σ M = ⊤) (hz : fixedSpace σ M = ⊥) {F : BinaryField}
    (e : ActionEquiv (s.action.comp M.subtype) (linearNatural F 3)) :
    ActionEquiv (σ.comp M.subtype) (linearNatural F 3) := by
  let q := wholeSectionEquiv s hm hz
  let t : ActionEquiv (σ.comp M.subtype) (s.action.comp M.subtype) :=
    ⟨MulEquiv.refl M, q.linearEquiv, fun g v => by
      simpa only [q, wholeSectionEquiv, MulEquiv.refl_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] using q.intertwines g v⟩
  exact transAction t e

private theorem best_linearEquiv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) W]
    {τ : Representation (ZMod 2) D W} (e : U ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (σ g v) = τ g (e v)) {A : Subgroup D}
    (hA : IsBestOffender σ A) : IsBestOffender τ A := by
  have hd (B : Subgroup D) : fixedCodim σ B = fixedCodim τ B := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant σ τ
      (MonoidHom.id D) e he B
  refine ⟨hA.1, fun B hB => ?_⟩
  have h := hA.2 B hB
  have h₁ := fixedCodim_add_finrank σ A
  have h₂ := fixedCodim_add_finrank τ A
  have h₃ := fixedCodim_add_finrank σ B
  have h₄ := fixedCodim_add_finrank τ B
  have hf := e.finrank_eq
  rw [hd A] at h₁
  rw [hd B] at h₃
  unfold weight at h ⊢
  omega

/-- If the moved section is the entire module and its central denominator
vanishes, its offender generation is the original offender generation. -/
theorem component_eq_top_of_fixed_eq_bot [FiniteDimensional (ZMod 2) U]
    {M : Subgroup D} (s : MovedSection σ M) (hm : moved σ M = ⊤)
    (hz : fixedSpace σ M = ⊥) (hgen : offenderSubgroup σ = ⊤)
    (hsection : offenderSubgroup s.action = M) : M = ⊤ := by
  let e := wholeSectionEquiv s hm hz
  apply top_unique
  rw [← hgen, ← hsection]
  apply iSup_le
  intro B
  apply iSup_le
  rintro ⟨hB, _⟩
  have hb := best_linearEquiv (τ := s.action) e.linearEquiv (fun g v => by
    simpa only [e, wholeSectionEquiv, MulEquiv.refl_apply] using e.intertwines g v) hB
  exact le_iSup_of_le B (le_iSup_of_le ⟨hb, le_top⟩ le_rfl)

variable {G : Type u} [Group G] [Finite G] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
/-- The Irr⁺ assertion on the literal quotient returns to U inside the original
V, through the actual quotient homomorphism and the inclusion U → V. -/
theorem seed_irrPlus {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      s.space.toSubmodule) : IsIrrPlus ρ L (naturalSeedSpace ρ L A) := by
  have hi' : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) ⊤ :=
    s.space_eq.trans hm ▸ hi
  have ht := IsIrrPlus.map_embedding (ρ.comp (L ⊔ A).subtype)
    (seedQuotientAction ρ hLA) (seedQuotientMap ρ hLA)
    (naturalSeedSpace ρ L A).subtype Subtype.val_injective
    (fun _ _ => rfl) (L.subgroupOf (L ⊔ A)) ⊤ hi'
  have hmap : (⊤ : Submodule (ZMod 2) (naturalSeedSpace ρ L A)).map
      (naturalSeedSpace ρ L A).subtype = naturalSeedSpace ρ L A := by
    exact (Submodule.map_top _).trans (Submodule.range_subtype _)
  have ht' : IsIrrPlus (ρ.comp (L ⊔ A).subtype) (L.subgroupOf (L ⊔ A))
      (naturalSeedSpace ρ L A) := hmap ▸ ht
  exact (IsIrrPlus.subgroupOf_iff ρ L (L ⊔ A) le_sup_left _).mp ht'

/-- Over fields larger than F₂, the actual central denominator of U vanishes
by the proved SL₃ cohomology calculation. -/
theorem seed_fixed_eq_bot_of_large {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      s.space.toSubmodule)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) (linearNatural F 3)) :
    fixedSpace (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊥ := by
  let := p.source.finite_module
  have hc := linearThree_large_isCompl s hi F hF e
  have ht : s.space.toSubmodule = ⊤ := s.space_eq.trans hm
  exact (disjoint_top.mp (ht ▸ hc.disjoint.symm))

/-- Once the central denominator vanishes, the given natural quotient action
is the actual L-action on U and the offender image induces inner action on L. -/
theorem compared_of_fixed_eq_bot {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hz : fixedSpace (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊥)
    (F : BinaryField) (ho : Odd F.degree)
    (hg : offenderSubgroup s.action = seedComponentImage ρ hLA)
    (e : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) (linearNatural F 3)) :
    ComparedCase ρ hLA := by
  let := p.source.finite_module
  have htop := component_eq_top_of_fixed_eq_bot s hm hz p.source.generated hg
  have ha : seedOffenderImage ρ hLA ≤ seedComponentImage ρ hLA := by rw [htop]; exact le_top
  let a := transAction (seedComponentActionEquiv ρ hLA p) (naturalOfWholeSection s hm hz e)
  exact .naturalThree F ho a (inducesInner_of_seedOffenderImage_le ρ hLA p ha)

/-- The odd-degree SL₃ comparison over every field larger than F₂. All module
and group data come from the literal source section; no extension conclusion
is assumed. -/
theorem compared_of_large {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      s.space.toSubmodule)
    (F : BinaryField) (ho : Odd F.degree) (hF : 1 < F.degree)
    (hg : offenderSubgroup s.action = seedComponentImage ρ hLA)
    (e : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) (linearNatural F 3)) :
    ComparedCase ρ hLA :=
  compared_of_fixed_eq_bot ρ hLA p s hm (seed_fixed_eq_bot_of_large ρ hLA p s hm hi F hF e)
    F ho hg e

/-- The linear-three source row makes the component the entire faithful seed
quotient. For larger fields use cohomology and offender generation; over F₂ use
the actual B.5.1 outer-extension alternatives and the order-168 exclusion. -/
theorem seedComponentImage_eq_top {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      s.space.toSubmodule)
    (hf : Function.Injective s.action)
    (hir : IsIrreducible (s.action.comp (seedComponentImage ρ hLA).subtype))
    (hext : seedComponentImage ρ hLA = ⊤ ∨
      (∀ T : Sylow 2 (SeedQuotient ρ hLA),
        seedComponentImage ρ hLA ⊔ (T : Subgroup (SeedQuotient ρ hLA)) = ⊤) ∧
      OuterNaturalAction s.action)
    (F : BinaryField)
    (hg : offenderSubgroup s.action = seedComponentImage ρ hLA)
    (e : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) (linearNatural F 3))
    (hq : quadraticRatio s.action = 1 / 2) : seedComponentImage ρ hLA = ⊤ := by
  let := p.source.finite_module
  by_cases hF : 1 < F.degree
  · exact component_eq_top_of_fixed_eq_bot s hm
      (seed_fixed_eq_bot_of_large ρ hLA p s hm hi F hF e) p.source.generated hg
  · have hdegree : F.degree = 1 := by have hpos := F.degree_pos; omega
    let q := degreeOneNaturalEquiv F hdegree 3
    let hrow : IrreducibleAlternative (seedComponentImage ρ hLA) s :=
      ⟨hi, hf, hir, .linearThree F hg e hq, hext⟩
    exact linearThree_eq_top p.source s hrow
      ⟨(e.groupEquiv.trans q.groupEquiv).trans Matrix.PSL3Two.equiv⟩

/-- In both the natural and central-cover branches, the original offender
induces inner automorphisms on the original component. -/
theorem inner_of_linearThree {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      s.space.toSubmodule)
    (hf : Function.Injective s.action)
    (hir : IsIrreducible (s.action.comp (seedComponentImage ρ hLA).subtype))
    (hext : seedComponentImage ρ hLA = ⊤ ∨
      (∀ T : Sylow 2 (SeedQuotient ρ hLA),
        seedComponentImage ρ hLA ⊔ (T : Subgroup (SeedQuotient ρ hLA)) = ⊤) ∧
      OuterNaturalAction s.action)
    (F : BinaryField)
    (hg : offenderSubgroup s.action = seedComponentImage ρ hLA)
    (e : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) (linearNatural F 3))
    (hq : quadraticRatio s.action = 1 / 2) : InducesInner A L := by
  apply inducesInner_of_seedOffenderImage_le ρ hLA p
  rw [seedComponentImage_eq_top ρ hLA p s hm hi hf hir hext F hg e hq]
  exact le_top

/-- Exhaustive reduction of the actual irreducible SL₃ row. The unfinished
case is exactly the binary-field central cover, retaining the full actor,
the original Irr⁺ assertion and inner action. This does not assert the
four-dimensional or offender conclusions of that remaining case. -/
theorem compared_or_binary_central_cover {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      c.sectionData.space.toSubmodule)
    (hf : Function.Injective c.sectionData.action)
    (hir : IsIrreducible (c.sectionData.action.comp (seedComponentImage ρ hLA).subtype))
    (hext : seedComponentImage ρ hLA = ⊤ ∨
      (∀ T : Sylow 2 (SeedQuotient ρ hLA),
        seedComponentImage ρ hLA ⊔ (T : Subgroup (SeedQuotient ρ hLA)) = ⊤) ∧
      OuterNaturalAction c.sectionData.action)
    (F : BinaryField) (ho : Odd F.degree)
    (hg : offenderSubgroup c.sectionData.action = seedComponentImage ρ hLA)
    (e : ActionEquiv (c.sectionData.action.comp (seedComponentImage ρ hLA).subtype)
      (linearNatural F 3))
    (hq : quadraticRatio c.sectionData.action = 1 / 2) :
    ComparedCase ρ hLA ∨
      (F.degree = 1 ∧
        fixedSpace (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) ≠ ⊥ ∧
        seedComponentImage ρ hLA = ⊤ ∧
        IsIrrPlus ρ L (naturalSeedSpace ρ L A) ∧ InducesInner A L) := by
  by_cases hz : fixedSpace (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊥
  · exact Or.inl (compared_of_fixed_eq_bot ρ hLA p c.sectionData hm hz F ho hg e)
  · have hF : F.degree = 1 := by
      have hnot : ¬ 1 < F.degree := fun h =>
        hz (seed_fixed_eq_bot_of_large ρ hLA p c.sectionData hm hi F h e)
      have hpos := F.degree_pos
      omega
    exact Or.inr ⟨hF, hz,
      seedComponentImage_eq_top ρ hLA p c.sectionData hm hi hf hir hext F hg e hq,
      seed_irrPlus ρ hLA c.sectionData hm hi,
      inner_of_linearThree ρ hLA p c.sectionData hm hi hf hir hext F hg e hq⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers
