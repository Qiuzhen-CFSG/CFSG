module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.LinearThreeOmega
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.CentralQuotients
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.G2Recognition
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Symplectic
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.Representation.G2NaturalExtensions.FixedSpaces

/-!
# The whole radical omega-center in the Sp₄ and G₂ image rows

The full B.5.1 conclusion excludes the reducible SL₃ and binary higher-linear
rows by actual group comparisons. The original FF action then selects the
natural Sp₄ or G₂ quotient over the original field through the proved Chapter K
recognition. No natural-action or splitting premise is added.

Every natural vector fixed by the radical has every lift fixed in the actual
commutator-generated central cover: this follows from the orthogonal quadratic
form for Sp₄ and the octonion norm for G₂. A two-group fixes a nonzero natural
vector, hence its entire field line. Choose lifts of this line and add the
whole component-fixed space. The literal central quotient makes this an
injection into the radical-fixed space. The original nonidentity point z
makes the second factor nontrivial, so the fixed space has more than q elements.
Characteristic two identifies it with the whole radical omega-center.

The chosen-flag theorem constructs FF and inner radical placement from the
retained earlier inputs. Comparison.Complete applies the strict containment in
the original radical-normalizer alternative and finishes with the actual
point-fixed Hall actor and Cartan contradiction. This is a calculation under
the original strict-comparison hypotheses, not an assertion about arbitrary
blocks. Earlier-source discharge remains with qt-d-1222-shadow-components.
Source: Aschbacher–Smith 11.4.2, printed p.777, using B.5.1 and I.2.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open ChapterB.QuasisimpleSource

private theorem fixed_card_lt_of_cover
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) A W) (C R : Subgroup A) (hRC : R ≤ C)
    (hR : IsPGroup 2 R) (hc : fixedSpace ρ C ≠ ⊥)
    (s : MovedSection ρ C) (F : BinaryField)
    {B N : Type*} [Group B] [AddCommGroup N] [Module F.Carrier N]
    [Module (ZMod 2) N] [IsScalarTower (ZMod 2) F.Carrier N]
    [FiniteDimensional (ZMod 2) N] [Nontrivial N]
    (τ : Representation F.Carrier B N)
    (e : ActionEquiv (s.action.comp C.subtype) (restrictScalars (k := ZMod 2) τ))
    (hlift : ∀ g w, τ g (s.coverProjection e w) = s.coverProjection e w →
      s.coverAction e g w = w) :
    Nat.card F.Carrier < Nat.card (fixedSpace ρ R) := by
  let Q := (R.subgroupOf C).map e.groupEquiv.toMonoidHom
  obtain ⟨v,_,hv,hvf⟩ := PermutedSupports.exists_nonzero_fixed
    (restrictScalars (k := ZMod 2) τ) Q (hR.comap_subtype.map _) ⊤ top_ne_bot
    (le_subspaceStabilizer _ ⊤ (fun _ _ _ _ => Submodule.mem_top))
  let p := s.coverProjection e
  have hp : Function.Surjective p :=
    e.linearEquiv.surjective.comp (Submodule.mkQ_surjective _)
  choose u hu using fun t : F.Carrier => hp (t • v)
  have huf (t : F.Carrier) : (u t).val ∈ fixedSpace ρ R := by
    intro r
    let g : C := ⟨r,hRC r.property⟩
    have hf : τ (e.groupEquiv g) v = v := hvf ⟨_,mem_map_of_mem _ r.property⟩
    have he := hlift (e.groupEquiv g) (u t) (by
      change τ (e.groupEquiv g) (p (u t)) = p (u t)
      rw [hu,map_smul,hf])
    have he' := congrArg Subtype.val he
    change ρ (e.groupEquiv.symm (e.groupEquiv g)) (u t).val = (u t).val at he'
    rw [e.groupEquiv.symm_apply_apply] at he'
    exact he'
  let φ : F.Carrier × fixedSpace ρ C → fixedSpace ρ R := fun a =>
    ⟨(u a.1).val + a.2.val,(fixedSpace ρ R).add_mem (huf a.1)
      (fun r => a.2.property ⟨r,hRC r.property⟩)⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have hh : (u a.1).val+a.2.val = (u b.1).val+b.2.val := congrArg Subtype.val hab
    have hd : (u a.1).val-(u b.1).val = b.2.val-a.2.val :=
      (sub_eq_sub_iff_add_eq_add).mpr (by simpa [add_comm] using hh)
    have hz : u a.1-u b.1 ∈ s.central.toSubmodule := by
      rw [s.central_eq]
      intro g
      apply Subtype.ext
      change ρ g ((u a.1).val-(u b.1).val) = (u a.1).val-(u b.1).val
      rw [hd,map_sub]
      exact congrArg₂ (fun x y : W => x-y) (b.2.property g) (a.2.property g)
    have hpz : p (u a.1-u b.1) = 0 := by
      change e.linearEquiv (s.central.toSubmodule.mkQ _) = 0
      exact (congrArg e.linearEquiv ((Submodule.Quotient.mk_eq_zero _).mpr hz)).trans
        e.linearEquiv.map_zero
    rw [map_sub,hu,hu,←sub_smul] at hpz
    have ht : a.1 = b.1 := sub_eq_zero.mp ((smul_eq_zero.mp hpz).resolve_right hv)
    apply Prod.ext ht
    apply Subtype.ext
    rw [ht] at hh
    exact add_left_cancel hh
  have hcard := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod] at hcard
  let : Nontrivial (fixedSpace ρ C) := Submodule.nontrivial_iff_ne_bot.mpr hc
  have htwo : 1 < Nat.card (fixedSpace ρ C) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hpos : 0 < Nat.card F.Carrier := Nat.card_pos
  nlinarith


private theorem no_linearThree_of_centerless_rankTwo
    {C : Type*} [Group C] [Finite C] (hz : center C = ⊥) (hr : 2 ≤ primeRank 3 C)
    (F : BinaryField) (e : C ≃* SL(3,F.Carrier)) : False := by
  have hzero : center SL(3,F.Carrier) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [←Nat.card_congr (centerCongr e).toEquiv,hz,Subgroup.card_bot]
  have ho : Odd F.degree := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mp hzero
    rw [F.card_eq,Nat.BinaryTorusParity.two_pow_mod_three,if_pos (Nat.even_iff.mp he)] at hh
    exact hh rfl
  have hb := Matrix.PSL3.BinaryCubicRankParity.rank_le_one_of_odd F.card_eq ho
  rw [primeRank_equiv 3 (e.trans (Matrix.SL3.equivProjectiveOfCenterEqBot F.Carrier hzero))] at hr
  omega

private theorem nonlinear_source_irreducible
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (C : Subgroup A)
    (d : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hz : center C = ⊥) (hr : 2 ≤ primeRank 3 C)
    (hbin : ∀ n, n = 4 ∨ n = 5 → ¬ Nonempty (C ≃* SL(n,ZMod 2))) :
    IsIrrPlus ρ C d.sectionData.space.toSubmodule ∧ Function.Injective d.sectionData.action ∧
      IsIrreducible (d.sectionData.action.comp C.subtype) := by
  cases d.clause_one with
  | irreducible hi hf hir _ _ => exact ⟨hi,hf,hir⟩
  | doubleThree F _ e _ _ =>
    exact (no_linearThree_of_centerless_rankTwo hz hr F e.groupEquiv).elim
  | naturalDual n hn _ e => exact (hbin n hn ⟨e.some.groupEquiv⟩).elim
  | repeatedNatural n _ hn _ _ _ e => exact (hbin n hn ⟨e.some.groupEquiv⟩).elim

private theorem center_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply bot_unique
  intro a ha
  exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨a,ha⟩).property)

private def quotient_equiv_of_centerless {A : Type*} [Group A]
    (hz : center A = ⊥) : (A ⧸ center A) ≃* A :=
  (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot

private theorem nonlinear_section_ff
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) {C : Subgroup A}
    (d : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hff : IsFFModule ρ) : IsFFModule d.sectionData.action := by
  obtain ⟨B,hB⟩ := hff
  exact ⟨B,IrreducibleBranch.moved_offender d.sectionData hB⟩

private theorem symplectic_source_natural
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (C : Subgroup A)
    (d : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hsq : IsSQTK KnownSimple.IsKnownSimple A) (hC : IsQuasisimple C)
    (hff : IsFFModule ρ) (F : BinaryField) (hF : 1 < F.degree)
    (e : C ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) :
    IsIrrPlus ρ C d.sectionData.space.toSubmodule ∧
      Nonempty (ActionEquiv (d.sectionData.action.comp C.subtype) (binarySymplectic F)) := by
  have hz := center_bot_of_equiv e
    (Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot (F := F.Carrier))
  have hr : 2 ≤ primeRank 3 C := by
    rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator _).subtype (commutator _).subtype_injective)
  obtain ⟨hi,hfaith,hir⟩ := nonlinear_source_irreducible ρ C d hz hr (by
    rintro n hn ⟨a⟩
    exact SourceCompletion.no_symplectic_binary_equiv F hn (e.symm.trans a))
  have hffQ := nonlinear_section_ff ρ d hff
  have hs := ChapterB.SourceClassification.source_hypotheses hsq d.fitting_eq.symm hC hfaith hir hffQ
  have hs' : ChapterK.Symplectic.SourceHypothesis KnownSimple.IsKnownSimple d.sectionData.action C := {
    finite_group := inferInstance
    finite_module := inferInstance
    sqtk := hs.sqtk
    fitting := hs.fitting
    quasisimple := hs.quasisimple
    faithful := hs.faithful
    irreducible := hs.irreducible
    cubic_le_two := hs.smallCubic }
  let := hs.irreducible
  obtain ⟨_,_,_,hnat | hten⟩ := ChapterK.Symplectic.source_complete hs' hF F.card_eq
    ((quotient_equiv_of_centerless hz).trans e)
  · obtain ⟨M,_⟩ := hnat
    exact ⟨hi,⟨⟨M.groupEquiv,M.linearEquiv,M.intertwines⟩⟩⟩
  · obtain ⟨s,_,_,a,M,hgeom⟩ := hten
    have hq := (isFFModule_iff_quadraticRatio_le_one _).mp hffQ
    exact (not_lt_of_ge (hq.trans (by norm_num : (1 : ENNReal) ≤ 2)) hgeom.2.1).elim

private theorem g2_no_binary (F : BinaryField) (hF : 1 < F.degree)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : Atlas.G2.Model F.Carrier ≃* SL(n,ZMod 2)) : False := by
  have hc := Nat.card_congr e.toEquiv
  have hq : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hF
  have hb : 4^6*(4^6-1)*(4^2-1) ≤ Nat.card (Atlas.G2.Model F.Carrier) := by
    rw [Atlas.G2.card_Model]
    gcongr
  rw [hc, Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv,
    ← Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
    Matrix.card_GL_field] at hb
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at hb

private theorem g2_source_natural
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (C : Subgroup A)
    (d : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hsq : IsSQTK KnownSimple.IsKnownSimple A) (hC : IsQuasisimple C)
    (hff : IsFFModule ρ) (F : BinaryField) (hF : 1 < F.degree)
    (e : C ≃* Atlas.G2.Model F.Carrier) :
    IsIrrPlus ρ C d.sectionData.space.toSubmodule ∧
      Nonempty (ActionEquiv (d.sectionData.action.comp C.subtype) (binaryG2 F)) := by
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hF
  have hz := center_bot_of_equiv e (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq)
  have hr : 2 ≤ primeRank 3 C := by
    rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator _).subtype (commutator _).subtype_injective)
  obtain ⟨hi,hfaith,hir⟩ := nonlinear_source_irreducible ρ C d hz hr (by
    rintro n hn ⟨a⟩
    exact g2_no_binary F hF hn (e.symm.trans a))
  have hffQ := nonlinear_section_ff ρ d hff
  have hs := ChapterB.SourceClassification.source_hypotheses hsq d.fitting_eq.symm hC hfaith hir hffQ
  exact ⟨hi,ChapterB.SourceClassification.g2_natural_action hs F hF
    ((quotient_equiv_of_centerless hz).trans e)⟩

private theorem symplectic_cover_lift
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}
    (s : MovedSection ρ C) (hi : IsIrrPlus ρ C s.space.toSubmodule)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (s.action.comp C.subtype) (binarySymplectic F))
    (g : Matrix.symplecticGroup (Fin 2) F.Carrier) (w : s.space.toSubmodule)
    (hw : binarySymplectic F g (s.coverProjection e w) = s.coverProjection e w) :
    s.coverAction e g w = w := by
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hF
  have hall := Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hq
  let d : commutator (Matrix.symplecticGroup (Fin 2) F.Carrier) ≃*
      Matrix.symplecticGroup (Fin 2) F.Carrier :=
    (MulEquiv.subgroupCongr hall).trans topEquiv
  let p := s.coverProjection e
  have hp := s.coverProjection_isCover hi e
  let P : Representation.IntertwiningMap ((s.coverAction e).comp (commutator _).subtype)
      (SymplecticFourOrthogonalCover.binaryNatural (K := F.Carrier)) :=
    p.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (fun g w => LinearMap.congr_fun (p.isIntertwining' g.val) w)
  have hP : Representation.OneCohomology.IsCover P :=
    ⟨hp.1,fun w hw g => hp.2.1 hw g.val,
      (Representation.OneCohomology.CentralCoverOriginalAction.commutator_comp_equiv
        (s.coverAction e) d).trans hp.2.2⟩
  exact SymplecticFourOrthogonalCover.cover_fixed_of_projection_fixed P hP
    ⟨g,hall ▸ mem_top g⟩ w hw

private theorem g2_cover_lift
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}
    (s : MovedSection ρ C) (hi : IsIrrPlus ρ C s.space.toSubmodule)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (s.action.comp C.subtype) (binaryG2 F))
    (g : Atlas.G2.Model F.Carrier) (w : s.space.toSubmodule)
    (hw : binaryG2 F g (s.coverProjection e w) = s.coverProjection e w) :
    s.coverAction e g w = w := by
  have hq : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hF
  let := Atlas.G2.isPerfect hq
  let d : commutator (Atlas.G2.Model F.Carrier) ≃* Atlas.G2.Model F.Carrier :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans topEquiv
  let p := s.coverProjection e
  have hp := s.coverProjection_isCover hi e
  have hgen : Coinvariants.ker ((s.coverAction e).comp (commutator _).subtype) = ⊤ :=
    (Representation.OneCohomology.CentralCoverOriginalAction.commutator_comp_equiv
      (s.coverAction e) d).trans hp.2.2
  exact Atlas.G2.Natural.Extensions.fixed_of_natural_fixed (s.coverAction e)
    p.toLinearMap hp.1 hp.2.1 hgen (fun g w => LinearMap.congr_fun (p.isIntertwining' g) w) g w hw

private theorem nonlinear_source_fixed_card_lt
    {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (C R : Subgroup A) (hRC : R ≤ C)
    (hR : IsPGroup 2 R) (hc : fixedSpace ρ C ≠ ⊥)
    (d : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (hsq : IsSQTK KnownSimple.IsKnownSimple A) (hC : IsQuasisimple C)
    (hff : IsFFModule ρ) (F : BinaryField) (hF : 1 < F.degree)
    (hm : Nonempty (C ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) ∨
      Nonempty (C ≃* Atlas.G2.Model F.Carrier)) :
    Nat.card F.Carrier < Nat.card (fixedSpace ρ R) := by
  rcases hm with hm | hm
  · obtain ⟨m⟩ := hm
    obtain ⟨hi,⟨e⟩⟩ := symplectic_source_natural ρ C d hsq hC hff F hF m
    exact fixed_card_lt_of_cover ρ C R hRC hR hc d.sectionData F
      (symplecticNatural (k := F.Carrier) 2) e (symplectic_cover_lift d.sectionData hi F hF e)
  · obtain ⟨m⟩ := hm
    obtain ⟨hi,⟨e⟩⟩ := g2_source_natural ρ C d hsq hC hff F hF m
    let : Nontrivial (Atlas.G2.Natural.Space F.Carrier) :=
      Module.nontrivial_of_finrank_pos (by rw [Atlas.G2.Natural.finrank_space]; decide)
    exact fixed_card_lt_of_cover ρ C R hRC hR hc d.sectionData F
      (g2Natural F.Carrier) e (g2_cover_lift d.sectionData hi F hF e)

open Classification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- In either nonlinear rank-two image, every radical-fixed natural vector
lifts through the literal central cover. Its field line together with the
original component-fixed point makes the whole omega-center larger than q. -/
theorem nonlinear_field_lt_radicalOmega
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hff : IsFFModule (action E))
    (hinner : (radical E).map (projection E) ≤ componentImage E)
    (hm : Source.IsSp (componentImage E) 2 (2^E.input.field.degree) ∨
      ClassificationModels.IsG2At (componentImage E) (2^E.input.field.degree)) :
    2^E.input.field.degree < Nat.card (radicalOmega E) := by
  obtain ⟨hC,⟨d⟩⟩ := source_classification E h hf hne hstar hcent hff
  let : IsQuasisimple (componentImage E) := (action_structure E h hf hne hstar hcent).2.2
  let : IsQuasisimple (offenderComponent E) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hC).symm
  let R := ((radical E).map (projection E)).subgroupOf (offenderGroup E)
  have hRC : R ≤ offenderComponent E := comap_mono hinner
  have hR : IsPGroup 2 R :=
    (((isPGroup_pCoreIn 2 (E.L₁ ⊔ (T : Subgroup G))).comap_subtype).map (projection E)).comap_subtype
  have hfix : fixedSpace (offenderAction E) (offenderComponent E) ≠ ⊥ := by
    rw [offenderComponent,offenderAction,fixedSpace_comp_map,map_subgroupOf_eq_of_le hC]
    exact component_fixedSpace_ne_bot E h hstar hcent
  have hbound (F : BinaryField) (hF : F.degree = E.input.field.degree)
      (hm : Nonempty (offenderComponent E ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) ∨
        Nonempty (offenderComponent E ≃* Atlas.G2.Model F.Carrier)) :
      2^E.input.field.degree < Nat.card (radicalOmega E) := by
    have hh := nonlinear_source_fixed_card_lt (offenderAction E) (offenderComponent E) R
      hRC hR hfix d (offenderGroup_sqtk E h) inferInstance (offenderAction_ff E hff)
      F (hF.symm ▸ E.input.nonbinary) hm
    rw [F.card_eq,hF] at hh
    have hRf : fixedSpace (offenderAction E) R =
        fixedSpace (action E) ((radical E).map (projection E)) := by
      rw [offenderAction,fixedSpace_comp_map,map_subgroupOf_eq_of_le (hinner.trans hC)]
    rw [hRf] at hh
    exact hh.trans_le (radical_fixedSpace_card_le_omega E hstar)
  rcases hm with hm | hm
  all_goals
    obtain ⟨F,inst,fin,hF,⟨m⟩⟩ := hm
    let : Field F := inst
    let : Finite F := fin
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let : Algebra (ZMod 2) F := ZMod.algebra F 2
    let F₀ : BinaryField := {
      Carrier := F
      degree := E.input.field.degree
      degree_pos := E.input.field.degree_pos
      card_eq := hF }
    apply hbound F₀ rfl
  · exact .inl ⟨(subgroupOfEquivOfLe hC).trans m⟩
  · exact .inr ⟨(subgroupOfEquivOfLe hC).trans m⟩

variable {E}

/-- The original chosen line is strictly smaller than the radical omega-center
for either nonlinear point image. The FF and inner-radical premises are proved
from the retained earlier geometry and the original quotient marking. -/
theorem ofFlag_nonlinear_line_lt_radicalOmega
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (e₁ : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hm : Source.IsSp (componentImage (ofFlag S f X z H)) 2 (2^S.field.degree) ∨
      ClassificationModels.IsG2At (componentImage (ofFlag S f X z H)) (2^S.field.degree)) :
    (ofFlag S f X z H).V₁ < radicalOmega (ofFlag S f X z H) := by
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  obtain ⟨_,_,_,_,_,hff,_⟩ := ofFlag_ff_reduction S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  have hi := rankTwo_radical_image_le_component (ofFlag S f X z H)
    h hf hne hstar hcent (f.invariant 0) e₁ (.inr hm)
  have hc := nonlinear_field_lt_radicalOmega (ofFlag S f X z H)
    h hf hne hstar hcent hff hi hm
  apply lt_of_le_of_ne (line_le_radicalOmega _ hstar hcent)
  intro he
  rw [←he,ofFlag_line_card S f X z H hf] at hc
  exact lt_irrefl _ hc
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
