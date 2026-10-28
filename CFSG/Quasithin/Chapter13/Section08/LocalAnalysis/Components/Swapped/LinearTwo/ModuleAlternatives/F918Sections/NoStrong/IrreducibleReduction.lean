module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.SectionImages
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.SourceB42
public import CFSG.Quasithin.ChapterB.Section01.IrreducibleReduction
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient
public import Theory.GroupTheory.PResidual.Defs
public import Theory.Quasithin.Rank

/-!
# Strong-action reductions through one exchanged component

A strong minimal best offender remains strong on every invariant subspace
on which it acts nontrivially, after taking the actual faithful image. For a
normalized component L, the fixed space of O₂(LA) therefore gives a faithful
strong action of LA/O₂(LA). Its entire generalized Fitting subgroup is the
image of L, and the marked product identifies it with the original PSL₂(F).
SQTK descends here through a normal two-group kernel.

For the resulting action, a stabilized Irr⁺ section gives the genuine B.4.2
witness: the actor is F*(E)A, the space is I/C_I(F*(E)), the action kernel is
trivial, and the entire new F* acts irreducibly. All the two-residual,
commutator and central-two-chief-factor hypotheses of B.1.5(3) are proved.

The source exclusion is not asserted here. Component normalization B.1.5(4)
and irreducible-section stabilization B.1.5(3), via B.7.2(1), remain explicit
in the two assembly helpers. Their source owners must discharge those inputs
before this task supplies an unconditional StrongPSLTwoAction witness. No
classification implication or exclusion of a PSL₂ model is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.4–5,
printed pp.68–70; B.1.11, pp.72–73; B.4.2, pp.86–87; B.7.2, p.119;
and the no-strong-FF step of 13.8.16(1), p.952 (PDF p.969).
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction
universe u v w
variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

/-- A strong minimal best offender remains strong on every noncentral
invariant subspace, after quotienting by the actual pointwise kernel. -/
theorem strong_restricted {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hs : IsStrongOffender ρ A)
    (W : Submodule (ZMod 2) V) (hW : A ≤ subspaceStabilizer ρ W)
    (hn : ¬ W ≤ fixedSpace ρ A) :
    IsStrongOffender (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
  have hb := hA.1.restricted ρ W hW hn
  refine ⟨hb.1, ?_⟩
  by_contra h
  have heq : rank (restrictedSubgroup ρ W A) =
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) :=
    le_antisymm (Nat.le_of_not_gt h) (hb.isOffender _).2
  have hk := (hA.faithful_span_of_image_rank_eq ρ W hW hn heq).1
  have hw := (hA.1.kernel_equalWeight_of_image_rank_eq ρ W hW heq).1.2
  rw [hk, weight_bot] at hw
  exact (ne_of_lt ((fixedCodim_lt_rank_iff ρ A).mp hs.2)) hw

omit [Finite G] in
/-- Strong offending passes to a faithful action on a literal invariant section. -/
theorem strong_on_faithful_section {A : Subgroup G} (hs : IsStrongOffender ρ A)
    (U W : Subrepresentation ρ)
    (hf : ∀ a ∈ A, (∀ s, sectionRepresentation ρ U W a s = s) → a = 1) :
    IsStrongOffender (imageRepresentation (sectionRepresentation ρ U W))
      (actionSubgroup (sectionRepresentation ρ U W) A) := by
  refine ⟨hs.1.actionSubgroup _ hf, ?_⟩
  rw [fixedCodim_actionSubgroup, actionSubgroup_rank _ A hf]
  exact (fixedCodim_section_le ρ U W A).trans_lt hs.2

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Minimal best offending survives restriction of the actor to an overgroup. -/
theorem minimal_subgroupOf {A H : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hAH : A ≤ H) :
    IsMinimalBestOffender (ρ.comp H.subtype) (A.subgroupOf H) := by
  refine ⟨hA.1.subgroupOf ρ hAH, ?_⟩
  intro B hB hBA
  have hm : (A.subgroupOf H).map H.subtype = A := map_subgroupOf_eq_of_le hAH
  have hle : B.map H.subtype ≤ A := hm ▸ Subgroup.map_mono hBA.1
  have hne : B.map H.subtype ≠ ⊥ := fun hb =>
    hB.1.1 ((B.map_eq_bot_iff_of_injective H.subtype_injective).mp hb)
  have hw : weight ρ (B.map H.subtype) = weight ρ A := by
    rw [← weight_comp_map ρ H.subtype H.subtype_injective,
      ← hm, ← weight_comp_map ρ H.subtype H.subtype_injective]
    exact hBA.2
  have he := hA.2 _ (hA.1.of_equalWeightLE ρ (hA.1.1.of_le hle hne) ⟨hle, hw⟩)
    ⟨hle, hw⟩
  exact Subgroup.map_injective H.subtype_injective (he.trans hm.symm)

omit [FiniteDimensional (ZMod 2) V] in
/-- A normal two-group quotient preserves both genuine SQTK clauses. -/
theorem sqtk_two_quotient {𝒦 : GroupClass.{u}} (hs : IsSQTK 𝒦 G)
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q) : IsSQTK 𝒦 (G ⧸ Q) := by
  refine ⟨?_, hs.isKGroup.quotient Q⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho Q hQ).trans
    (hs.stronglyQuasithin p hp ho)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction

open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction
universe u v w
open CFSG.Quasithin.ChapterB
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions

/-- The intermediate action after removing the two-core. Irreducibility is
not part of this record and still has to be proved on a subsequent section. -/
structure Preaction (𝒦 : GroupClass.{u}) (F : Type w) [Field F] where
  Actor : Type u
  [actor_group : Group Actor]
  [actor_finite : Finite Actor]
  Space : Type v
  [space_add : AddCommGroup Space]
  [space_module : Module (ZMod 2) Space]
  [space_finite : Finite Space]
  representation : Representation (ZMod 2) Actor Space
  sqtk : IsSQTK 𝒦 Actor
  faithful : Function.Injective representation
  strong : IsStrongFFModule representation
  quasisimple : IsQuasisimple (generalizedFitting Actor)
  componentEquiv : generalizedFitting Actor ≃* PSL(2,F)

attribute [instance] Preaction.actor_group Preaction.actor_finite
  Preaction.space_add Preaction.space_module Preaction.space_finite

/-- The fixed-space kernel is the actual two-core; the original centerless
component embeds in the image, which is the whole generalized Fitting subgroup.
The actor is a quotient of G, so it remains in G's universe and inherits SQTK. -/
noncomputable def preaction_of_generated
    {𝒦 : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    {F : Type w} [Field F] [CharP F 2]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ)
    (hsqtk : IsSQTK 𝒦 G) (L A : Subgroup G) [L.Normal] [IsQuasisimple L]
    (eL : L ≃* PSL(2,F)) (hLA : ⁅L,A⁆ = L) (hgen : L ⊔ A = ⊤)
    (hA : IsMinimalBestOffender ρ A) (hstrong : IsStrongOffender ρ A) :
    Preaction.{u,v,w} 𝒦 F := by
  let U := fixedSpace ρ (pCore 2 G)
  have hU := fixedSpace_stable_of_normal ρ (pCore 2 G)
  let f := invariantActionHom ρ U hU
  obtain ⟨hk, hc, hcore, hquasi, hfit, hne, hbest, _⟩ :=
    irreducibleReduction_generated ρ hfaith L A hLA hgen hA.1
  have hn : ¬ U ≤ fixedSpace ρ A := by
    intro hn
    apply hne
    rw [← invariantActionHom_map ρ U hU]
    apply (Subgroup.map_eq_bot_iff A).mpr
    rw [invariantActionHom_ker]
    exact fun a ha => ⟨mem_top a, fun v hv => hn hv ⟨a, ha⟩⟩
  have hs := strong_restricted ρ hA hstrong U (le_trans le_top hU) hn
  let E := G ⧸ pCore 2 G
  let e : E ≃* subspaceActionImage ρ U :=
    irreducibleReduction_quotientEquiv ρ U hU hk
  let σ : Representation (ZMod 2) E U :=
    (subspaceImageRepresentation ρ U).comp e.toMonoidHom
  have hsσ : IsStrongFFModule σ := by
    apply strongFF_map_equivariant (subspaceImageRepresentation ρ U) σ
      e.symm.toMonoidHom e.symm.injective (LinearEquiv.refl _ _) _ ⟨_, hs⟩
    intro g v
    change subspaceImageRepresentation ρ U g v =
      subspaceImageRepresentation ρ U (e (e.symm g)) v
    rw [e.apply_symm_apply]
  have hz : center L = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro l hl
    have h := (centerCongr eL ⟨l, hl⟩).property
    change eL l ∈ center PSL(2,F) at h
    rw [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] at h
    exact mem_bot.mpr (eL.injective (h.trans eL.map_one.symm))
  have hfL : Function.Injective (f.subgroupMap L) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply _root_.eq_bot_iff.mpr
    intro l hl
    have hlf : f l = 1 := congrArg Subtype.val hl
    have hlQ : (l : G) ∈ pCore 2 G := by
      have hh : (l : G) ∈ f.ker := hlf
      rwa [invariantActionHom_ker, hk] at hh
    have hlZ : l ∈ center L := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (hc hlQ k k.property)
    simpa only [hz] using hlZ
  let el : L ≃* restrictedSubgroup ρ U L :=
    (MulEquiv.ofBijective (f.subgroupMap L) ⟨hfL, f.subgroupMap_surjective L⟩).trans
      (MulEquiv.subgroupCongr (invariantActionHom_map ρ U hU L))
  let ef : generalizedFitting E ≃* restrictedSubgroup ρ U L :=
    (e.subgroupMap (generalizedFitting E)).trans
      (MulEquiv.subgroupCongr ((map_generalizedFitting_equiv e).trans hfit))
  exact
    { Actor := E
      Space := U
      representation := σ
      sqtk := sqtk_two_quotient hsqtk (pCore 2 G) pCore_isPGroup
      faithful := (subspaceImageRepresentation_injective ρ U).comp e.injective
      strong := hsσ
      quasisimple := by
        let : IsQuasisimple (restrictedSubgroup ρ U L) := hquasi
        exact IsQuasisimple.of_mulEquiv ef.symm
      componentEquiv := ef.trans (el.symm.trans eL) }

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction
universe u v w

private def firstFactorEquiv (P : Type*) [Group P] :
    (⊤ : Subgroup P).prod (⊥ : Subgroup P) ≃* P where
  toFun x := x.val.1
  invFun x := ⟨(x, 1), mem_top x, (mem_bot.mpr rfl)⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl (mem_bot.mp x.property.2).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def secondFactorEquiv (P : Type*) [Group P] :
    (⊥ : Subgroup P).prod (⊤ : Subgroup P) ≃* P where
  toFun x := x.val.2
  invFun x := ⟨(1, x), (mem_bot.mpr rfl), mem_top x⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext (mem_bot.mp x.property.1).symm rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {𝒦 : GroupClass.{u}} {D : Type u} [Group D] [Finite D]
    {F : Type w} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (d : ExchangedActor 𝒦 D F n)

/-- The marked first component is the actual projective factor. -/
noncomputable def firstComponentEquiv : d.component ≃* PSL(2,F) :=
  (subgroupOfEquivOfLe d.component_le).symm.trans
    ((d.productEquiv.subgroupMap (d.component.subgroupOf d.orbit)).trans
      ((MulEquiv.subgroupCongr d.first_mark).trans (firstFactorEquiv PSL(2,F))))

/-- The marked second component is the same actual projective model. -/
noncomputable def secondComponentEquiv : d.second ≃* PSL(2,F) :=
  (subgroupOfEquivOfLe d.second_le).symm.trans
    ((d.productEquiv.subgroupMap (d.second.subgroupOf d.orbit)).trans
      ((MulEquiv.subgroupCongr d.second_mark).trans (secondFactorEquiv PSL(2,F))))

/-- The two marked components generate the entire orbit, as witnessed by
its actual product equivalence. -/
theorem components_sup : d.component ⊔ d.second = d.orbit := by
  have h : d.component.subgroupOf d.orbit ⊔ d.second.subgroupOf d.orbit = ⊤ := by
    apply Subgroup.map_injective (f := d.productEquiv.toMonoidHom) d.productEquiv.injective
    rw [Subgroup.map_sup, d.first_mark, d.second_mark,
      map_top_of_surjective _ d.productEquiv.surjective]
    apply top_unique
    intro x _
    have h1 : (x.1, (1 : PSL(2,F))) ∈ (⊤ : Subgroup PSL(2,F)).prod (⊥ : Subgroup PSL(2,F)) := ⟨mem_top _, mem_bot.mpr rfl⟩
    have h2 : ((1 : PSL(2,F)), x.2) ∈ (⊥ : Subgroup PSL(2,F)).prod (⊤ : Subgroup PSL(2,F)) := ⟨mem_bot.mpr rfl, mem_top _⟩
    simpa only [Prod.mk_mul_mk, mul_one, one_mul] using
      Subgroup.mul_mem ((⊤ : Subgroup PSL(2,F)).prod ⊥ ⊔ (⊥ : Subgroup PSL(2,F)).prod ⊤)
        (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  have hm := congrArg (Subgroup.map d.orbit.subtype) h
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le d.component_le,
    map_subgroupOf_eq_of_le d.second_le, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] using hm

/-- A nontrivial subgroup normalizing both components moves at least one
by commutation. Otherwise it centralizes the self-centralizing orbit. -/
theorem exists_component_commutator {A : Subgroup D} (hne : A ≠ ⊥)
    (hN₁ : A ≤ normalizer (d.component : Set D))
    (hN₂ : A ≤ normalizer (d.second : Set D)) :
    ∃ L : Subgroup D, IsComponent D L ∧ Nonempty (L ≃* PSL(2,F)) ∧ ⁅L,A⁆ = L := by
  have dichotomy (L : Subgroup D) (hL : IsComponent D L)
      (hN : A ≤ normalizer (L : Set D)) : ⁅L,A⁆ = ⊥ ∨ ⁅L,A⁆ = L := by
    rcases hL.commutator_dichotomy A with h | h
    · exact Or.inl h
    · right
      have he (a : A) : L.map (MulAut.conj (a : D)).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq.mp (hN a.property)
      simpa only [he, iSup_const] using h
  rcases dichotomy d.component d.component_isComponent hN₁ with hz₁ | he₁
  · rcases dichotomy d.second d.second_isComponent hN₂ with hz₂ | he₂
    · exfalso
      apply hne
      apply bot_unique
      rw [← d.centralizer_eq_bot, ← components_sup d]
      exact le_centralizer_iff.mpr (sup_le
        (commutator_eq_bot_iff_le_centralizer.mp hz₁)
        (commutator_eq_bot_iff_le_centralizer.mp hz₂))
    · exact ⟨d.second, d.second_isComponent, ⟨secondComponentEquiv d⟩, he₂⟩
  · exact ⟨d.component, d.component_isComponent, ⟨firstComponentEquiv d⟩, he₁⟩

/-- Conditional on B.1.5(4) for these two components, a strong faithful
exchanged action yields a strong faithful SQTK action with simple F* of the
correct PSL₂ type. No irreducibility or classification is asserted here. -/
theorem preaction_of_component_normalization
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (hfaith : Function.Injective ρ)
    (hs : IsStrongFFModule ρ)
    (hN : ∀ A, IsBestOffender ρ A →
      A ≤ normalizer (d.component : Set D) ∧ A ≤ normalizer (d.second : Set D)) :
    Nonempty (Preaction.{u,v,w} 𝒦 F) := by
  obtain ⟨A₀, hs₀⟩ := hs
  obtain ⟨A, _, hA, _, hsA⟩ := hs₀.exists_quadratic_minimalBestOffender ρ
  obtain ⟨L, hL, ⟨eL⟩, hLA⟩ := exists_component_commutator d hA.1.1.1
    (hN A hA.1).1 (hN A hA.1).2
  let K := L ⊔ A
  let L₀ := L.subgroupOf K
  let A₀ := A.subgroupOf K
  let : L₀.Normal := CFSG.Quasithin.ChapterB.irreducibleReduction_normal L A hLA
  let : IsQuasisimple L := hL.2
  let : IsQuasisimple L₀ :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ K from le_sup_left)).symm
  have hcomm : ⁅L₀,A₀⁆ = L₀ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator]
    change ⁅(L.subgroupOf K).map K.subtype, (A.subgroupOf K).map K.subtype⁆ =
      (L.subgroupOf K).map K.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ K from le_sup_right), hLA]
  have hgen : L₀ ⊔ A₀ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup]
    change (L.subgroupOf K).map K.subtype ⊔ (A.subgroupOf K).map K.subtype =
      (⊤ : Subgroup K).map K.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ K from le_sup_right)]
    exact K.range_subtype.symm.trans K.subtype.range_eq_map
  refine ⟨preaction_of_generated (ρ.comp K.subtype) (hfaith.comp K.subtype_injective)
    (d.sqtk.subgroup K) L₀ A₀ ((subgroupOfEquivOfLe le_sup_left).trans eL)
    hcomm hgen (minimal_subgroupOf ρ hA le_sup_right)
    (CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.strongOffender_subgroupOf
      ρ hsA le_sup_right)⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction
universe u v w
open CFSG.Quasithin.ChapterB
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

variable {𝒦 : GroupClass.{u}} {F : Type w} [Field F] [CharP F 2]

/-- The center of the entire generalized Fitting subgroup vanishes, using
its actual equivalence with the characteristic-two projective group. -/
theorem Preaction.fitting_center (a : Preaction.{u,v,w} 𝒦 F) :
    center (generalizedFitting a.Actor) = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro x hx
  have h := (centerCongr a.componentEquiv ⟨x, hx⟩).property
  change a.componentEquiv x ∈ center PSL(2,F) at h
  rw [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] at h
  exact mem_bot.mpr (a.componentEquiv.injective (h.trans a.componentEquiv.map_one.symm))

/-- The simple generalized Fitting subgroup is self-centralizing. -/
theorem Preaction.fitting_centralizer (a : Preaction.{u,v,w} 𝒦 F) :
    centralizer (generalizedFitting a.Actor : Set a.Actor) = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro g hg
  have hgL : g ∈ generalizedFitting a.Actor :=
    QuasisimpleSections.centralizer_generalizedFitting_le hg
  have hz : (⟨g, hgL⟩ : generalizedFitting a.Actor) ∈ center (generalizedFitting a.Actor) := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (hg l l.property)
  rw [a.fitting_center, mem_bot] at hz
  exact mem_bot.mpr (congrArg Subtype.val hz)

/-- A stable Irr⁺ section produces the exact B.4 actor. The actor is the
actual subgroup F*(E)A, the module is I/C_I(F*(E)), and its kernel is proved
trivial. In particular irreducibility is under the whole new F*, not just
under an unrelated subgroup. The stabilization premise belongs to B.1.5(3). -/
theorem Preaction.action_of_stable_section (a : Preaction.{u,v,w} 𝒦 F)
    (A : Subgroup a.Actor) (hs : IsStrongOffender a.representation A)
    (I : Submodule (ZMod 2) a.Space)
    (hI : IsIrrPlus a.representation (generalizedFitting a.Actor) I)
    (hAI : A ≤ subspaceStabilizer a.representation I) :
    Nonempty (StrongPSLTwoAction.{u,v,w} 𝒦 F) := by
  let L := generalizedFitting a.Actor
  let H := L ⊔ A
  let L₀ := L.subgroupOf H
  let A₀ := A.subgroupOf H
  let τ := a.representation.comp H.subtype
  let : L.Normal := generalizedFitting_normal
  let : IsQuasisimple L := a.quasisimple
  let : L₀.Normal := inferInstance
  let e₀ : L₀ ≃* L := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple L₀ := IsQuasisimple.of_mulEquiv e₀.symm
  have hgen : L₀ ⊔ A₀ = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup]
    change (L.subgroupOf H).map H.subtype ⊔ (A.subgroupOf H).map H.subtype =
      (⊤ : Subgroup H).map H.subtype
    rw [map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right)]
    exact H.range_subtype.symm.trans H.subtype.range_eq_map
  have hcent : centralizer (L₀ : Set H) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro g hg
    have hc : (g : a.Actor) ∈ centralizer (L : Set a.Actor) := by
      intro l hl
      exact congrArg Subtype.val (hg ⟨l, (show L ≤ H from le_sup_left) hl⟩ hl)
    rw [a.fitting_centralizer, mem_bot] at hc
    exact mem_bot.mpr (Subtype.ext hc)
  have hcore : pCore 2 H = ⊥ := by
    apply bot_unique
    rw [← hcent]
    exact irreducibleReduction_core_centralizes L₀
  have hpA : IsPGroup 2 A₀ := by
    let : IsElementaryAbelian 2 A := hs.1.2
    exact (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  have hfit : generalizedFitting H = L₀ :=
    generalizedFitting_eq_of_quasisimple_two_quotient L₀
      (quotient_isPGroup_of_sup_eq_top A₀ L₀ hpA (sup_comm L₀ A₀ ▸ hgen)) hcore
  have hi : IsIrrPlus τ L₀ I :=
    (IsIrrPlus.subgroupOf_iff a.representation L H le_sup_left I).mpr hI
  have hHI : H ≤ subspaceStabilizer a.representation I := sup_le hI.choose hAI
  let W : Subrepresentation τ := ⟨I, fun g _ hv => (hHI g.property _).2 hv⟩
  let C : Subrepresentation τ :=
    ⟨fixedSpace τ L₀, fun g _ hv =>
      (fixedSpace_stable_of_normal τ L₀ (mem_top g) _).2 hv⟩
  let σ := sectionRepresentation τ C W
  have hirr : IsIrreducible (σ.comp L₀.subtype) := hi.choose_spec.2
  have hn : ¬ ∀ l ∈ L₀, ∀ s, σ l s = s := by
    intro hn
    apply hi.not_le_fixedSpace τ
    apply le_fixedSpace_of_commutator_le_fixedSpace τ L₀ I hi.choose
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, v, hv, rfl⟩
    exact (sectionRepresentation_trivial_iff τ C W l).mp (hn l hl) v hv
  have hk : (actionHom σ).ker = ⊥ := by
    apply bot_unique
    rw [← hcent]
    exact action_kernel_le_centralizer σ L₀ (central_kernel_of_quasisimple σ L₀ hn)
  have hfaith : Function.Injective σ := by
    intro x y hxy
    apply (MonoidHom.ker_eq_bot_iff (actionHom σ)).mp hk
    apply imageRepresentation_injective σ
    exact hxy
  have hsτ : IsStrongOffender τ A₀ := strongOffender_subgroupOf a.representation hs le_sup_right
  have hsσ : IsStrongFFModule σ :=
    ⟨A₀, hsτ.1, (fixedCodim_section_le τ C W A₀).trans_lt hsτ.2⟩
  let : Finite (W.toSubmodule ⧸ (sectionLower τ C W).toSubmodule) :=
    Finite.of_surjective _ (sectionLower τ C W).toSubmodule.mkQ_surjective
  refine ⟨{
    Actor := H
    Space := W.toSubmodule ⧸ (sectionLower τ C W).toSubmodule
    representation := σ
    hypotheses := {
      sqtk := a.sqtk.subgroup H
      faithful := hfaith
      quasisimple := ?_
      irreducible := ?_ }
    strong := hsσ
    componentEquiv := (MulEquiv.subgroupCongr hfit).trans (e₀.trans a.componentEquiv) }⟩
  · rw [hfit]
    infer_instance
  · change IsIrreducible (σ.comp (generalizedFitting H).subtype)
    rw [hfit]
    exact hirr

/-- The remaining B.1.5(3) input is isolated at its genuine mathematical
boundary. Existence of I, strong replacement, the faithful section, SQTK and
the whole generalized-Fitting identification are discharged here. -/
theorem Preaction.action_of_stabilization (a : Preaction.{u,v,w} 𝒦 F)
    (hst : ∀ A, IsMinimalBestOffender a.representation A →
      ∀ I, IsIrrPlus a.representation (generalizedFitting a.Actor) I →
        A ≤ subspaceStabilizer a.representation I) :
    Nonempty (StrongPSLTwoAction.{u,v,w} 𝒦 F) := by
  obtain ⟨A₀, hA₀⟩ := a.strong
  obtain ⟨A, _, hA, _, hs⟩ := hA₀.exists_quadratic_minimalBestOffender a.representation
  let : IsQuasisimple (generalizedFitting a.Actor) := a.quasisimple
  have hL : generalizedFitting a.Actor ≠ ⊥ := by
    let : IsSimpleGroup ((generalizedFitting a.Actor) ⧸ center (generalizedFitting a.Actor)) :=
      IsQuasisimple.simple
    let : Nontrivial (generalizedFitting a.Actor) :=
      Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center (generalizedFitting a.Actor)))
    exact (nontrivial_iff_ne_bot _).mp inferInstance
  obtain ⟨I, hi⟩ := exists_isIrrPlus_of_faithful a.representation a.faithful
    (generalizedFitting a.Actor) hL
  exact a.action_of_stable_section A hs I hi (hst A hA I hi)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction
universe u v w
open CFSG.Quasithin.ChapterB
variable {𝒦 : GroupClass.{u}} {F : Type w} [Field F] [CharP F 2]

/-- All the group hypotheses needed for B.1.5(3) hold for the actual
quasisimple generalized Fitting subgroup. The two-residual, rather than
the two-core, is the whole subgroup; two-chief factors use normal intervals. -/
theorem Preaction.stabilization_hypotheses (a : Preaction.{u,v,w} 𝒦 F)
    {A : Subgroup a.Actor} (hA : IsElementaryTwo A) :
    pResidual 2 (generalizedFitting a.Actor) = ⊤ ∧
      HasCentralPChiefFactors 2 (generalizedFitting a.Actor) ∧
      ⁅generalizedFitting a.Actor, A⁆ = generalizedFitting a.Actor := by
  let L := generalizedFitting a.Actor
  let : IsQuasisimple L := a.quasisimple
  have hr : pResidual 2 L = ⊤ := by
    apply (pResidual_eq_top_iff 2 L).mpr
    intro N hN hp
    let := hN
    have hsub : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent
    apply top_unique
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  have hchief : HasCentralPChiefFactors 2 L :=
    hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
      (⊥ : Subgroup L) (by simp)
      (IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm)
  have hc : pCore 2 a.Actor = ⊥ := by
    apply bot_unique
    rw [← a.fitting_centralizer]
    exact irreducibleReduction_core_centralizes L
  let : IsElementaryAbelian 2 A := hA.2
  exact ⟨hr, hchief, QuasisimpleSections.commutator_fitting_eq hc a.quasisimple
    hA.1 (IsElementaryAbelian.isPGroup 2 A)⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction
