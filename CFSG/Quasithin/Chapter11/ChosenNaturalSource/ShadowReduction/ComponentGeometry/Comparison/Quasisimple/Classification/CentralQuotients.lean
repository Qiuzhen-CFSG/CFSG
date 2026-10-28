module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.Realization

/-!
# Central-quotient exclusions for the original FF comparison

The full B.5.1 reduction supplies a faithful irreducible test action for
every row, on the same actor and component. The proved B.4 obstructions
exclude all sporadic, odd linear-three, triality and Ree central quotients,
and restrict the odd rank-one and unitary parameters.

The original component application passes through its literal action
projection and actual best-offender subgroup. Central quotient isomorphisms
retain every covering kernel. The chosen-flag theorem constructs its FF
witness by the Thompson reduction. Earlier geometry and maximality remain
with their existing producers; final 11.4.2 assembly remains with
qt-d-1222-shadow-component-comparison and qt-d-1222-shadow-components.
This does not yet identify the surviving field parameters or prove the
proper-overcomponent and Hall/Cartan comparisons.

Source: Aschbacher--Smith 11.4.2, pp.776--777, using B.4.2 and B.5.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
open ChapterB.QuasisimpleSource
universe u v

/-- All central-cover sporadic rows are excluded by the same literal B.4
source domain, including every reducible B.5.1 alternative. -/
theorem not_sporadic_of_source
    {Q : Type u} [Group Q] [Finite Q]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hK : IsQuasisimple K)
    (hff : IsFFModule ρ) :
    ¬ ChapterA.Section02.IsTheoremCSporadicModel (K ⧸ center K) := by
  intro hm
  rcases irreducible_realization_of_source c hff with h | h <;>
    rcases h with ⟨U,_,_,_,σ,hf,hi,hff⟩ <;>
    exact ChapterB.SourceClassification.sporadic_false
      (ChapterB.SourceClassification.source_hypotheses hsq c.fitting_eq.symm hK hf hi hff) hff hm


/-- The odd prime linear-three exclusion also applies to reducible FF actions. -/
theorem not_odd_psl3_of_source
    {Q : Type u} [Group Q] [Finite Q]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hK : IsQuasisimple K)
    (hff : IsFFModule ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 p := by
  intro hm
  rcases irreducible_realization_of_source c hff with h | h <;>
    rcases h with ⟨U,_,_,_,σ,hf,hi,hff⟩ <;>
    exact ChapterB.SourceClassification.not_ff_odd_psl3
      (ChapterB.SourceClassification.source_hypotheses hsq c.fitting_eq.symm hK hf hi hff)
      hp ho hm hff

/-- The odd rank-one parameters are unchanged by the full B.5.1 reduction. -/
theorem odd_psl2_parameters_of_source
    {Q : Type u} [Group Q] [Finite Q]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hK : IsQuasisimple K)
    (hff : IsFFModule ρ) {p d : ℕ} (hp : p.Prime) (ho : Odd p)
    (hd : d = 1 ∨ d = 2) (hlo : 4 ≤ p ^ d)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 (p ^ d)) :
    (p = 5 ∧ d = 1) ∨ (p = 7 ∧ d = 1) ∨ (p = 3 ∧ d = 2) := by
  rcases irreducible_realization_of_source c hff with h | h <;>
    rcases h with ⟨U,_,_,_,σ,hf,hi,hff⟩ <;>
    exact ChapterB.SourceClassification.odd_pslTwo_parameters
      (ChapterB.SourceClassification.source_hypotheses hsq c.fitting_eq.symm hK hf hi hff)
      hff hp ho hd hlo hm

/-- Triality cannot occur even when the original FF module is reducible. -/
theorem not_triality_of_source
    {Q : Type u} [Group Q] [Finite Q]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hK : IsQuasisimple K)
    (hff : IsFFModule ρ) (n : ℕ) (hn : 0 < n) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) (K ⧸ center K) := by
  intro hm
  rcases irreducible_realization_of_source c hff with h | h <;>
    rcases h with ⟨U,_,_,_,σ,hf,hi,hff⟩ <;>
    exact ChapterB.SourceClassification.triality_not_ff
      (ChapterB.SourceClassification.source_hypotheses hsq c.fitting_eq.symm hK hf hi hff)
      n hn hm hff

/-- The Ree exclusion retains the actual central quotient marking. -/
theorem not_ree_of_source
    {Q : Type u} [Group Q] [Finite Q]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hK : IsQuasisimple K)
    (hff : IsFFModule ρ) (m : ℕ) (hm : 0 < m) :
    ¬ Nonempty ((K ⧸ center K) ≃* _root_.ReeF4.Model m) := by
  rintro ⟨e⟩
  rcases irreducible_realization_of_source c hff with h | h <;>
    rcases h with ⟨U,_,_,_,σ,hf,hi,hff⟩ <;>
    exact ChapterB.SourceClassification.reeF4_excluded
      (ChapterB.SourceClassification.source_hypotheses hsq c.fitting_eq.symm hK hf hi hff)
      hff hm e

/-- The only possible odd prime unitary parameter remains three. -/
theorem odd_psu3_parameter_of_source
    {Q : Type u} [Group Q] [Finite Q]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hK : IsQuasisimple K)
    (hff : IsFFModule ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 p) : p = 3 := by
  rcases irreducible_realization_of_source c hff with h | h <;>
    rcases h with ⟨U,_,_,_,σ,hf,hi,hff⟩ <;>
    exact ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.source_unitaryRestriction
      σ K ⟨hsq,c.fitting_eq,hK,hf,hi⟩ hp ho hm
      ((cubicRatio_le_quadraticRatio σ).trans
        (((isFFModule_iff_quadraticRatio_le_one σ).mp hff).trans (by norm_num)))

/-- Restrictions on the simple central quotient forced by an actual FF
module. These are derived from B.4/B.5, not a replacement classification input. -/
structure CentralQuotientRestrictions (A : Type*) [Group A] : Prop where
  not_sporadic : ¬ ChapterA.Section02.IsTheoremCSporadicModel A
  not_odd_psl3 : ∀ p, p.Prime → Odd p → ¬ ClassicalGroup.IsPSL A 3 p
  odd_psl2 : ∀ p d, p.Prime → Odd p → (d = 1 ∨ d = 2) → 4 ≤ p ^ d →
    ClassicalGroup.IsPSL A 2 (p ^ d) →
    (p = 5 ∧ d = 1) ∨ (p = 7 ∧ d = 1) ∨ (p = 3 ∧ d = 2)
  odd_psu3 : ∀ p, p.Prime → Odd p → ClassicalGroup.IsPSU A 3 p → p = 3
  not_triality : ∀ n, 0 < n → ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) A
  not_ree : ∀ m, 0 < m → ¬ Nonempty (A ≃* _root_.ReeF4.Model m)

/-- Transport every exclusion along its actual group isomorphism. -/
theorem CentralQuotientRestrictions.of_mulEquiv {A B : Type*} [Group A] [Group B]
    (h : CentralQuotientRestrictions A) (e : B ≃* A) : CentralQuotientRestrictions B where
  not_sporadic hm := h.not_sporadic (hm.of_mulEquiv e.symm)
  not_odd_psl3 p hp ho hm := h.not_odd_psl3 p hp ho (hm.of_mulEquiv e.symm)
  odd_psl2 p d hp ho hd hlo hm := h.odd_psl2 p d hp ho hd hlo (hm.of_mulEquiv e.symm)
  odd_psu3 p hp ho hm := h.odd_psu3 p hp ho (hm.of_mulEquiv e.symm)
  not_triality n hn hm := h.not_triality n hn (hm.of_mulEquiv e.symm)
  not_ree m hm he := h.not_ree m hm (he.map (fun a => e.symm.trans a))

/-- The full B.5.1 action has all six central-quotient restrictions, including
its reducible cases and possible covering centers. -/
theorem centralQuotientRestrictions_of_source
    {Q : Type u} [Group Q] [Finite Q]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) Q W} {K : Subgroup Q}
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Q) (hK : IsQuasisimple K)
    (hff : IsFFModule ρ) : CentralQuotientRestrictions (K ⧸ center K) where
  not_sporadic := not_sporadic_of_source c hsq hK hff
  not_odd_psl3 _ hp ho := not_odd_psl3_of_source c hsq hK hff hp ho
  odd_psl2 _ _ hp ho hd hlo := odd_psl2_parameters_of_source c hsq hK hff hp ho hd hlo
  odd_psu3 _ hp ho := odd_psu3_parameter_of_source c hsq hK hff hp ho
  not_triality n hn := not_triality_of_source c hsq hK hff n hn
  not_ree m hm := not_ree_of_source c hsq hK hff m hm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The actual best-offender actor inherits strong quasithinness from the
original semisimple section, through its two-group extension. -/
theorem offenderGroup_sqtk (h : EarlierGeometry E)
    [IsQuasisimple (componentImage E)] : IsSQTK KnownSimple.IsKnownSimple (offenderGroup E) := by
  let := componentImage_normal E h
  have hs := IrreducibleBranch.sqtk_of_twoGroup_quotient
    ChapterB.ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups
    (componentImage E) (quotient_componentImage_isTwoGroup E h) (componentImage_sqtk E h)
  exact hs.subgroup (offenderGroup E)

/-- Restriction retains an original best offender contained in its generated subgroup. -/
theorem offenderAction_ff (hff : IsFFModule (action E)) : IsFFModule (offenderAction E) := by
  obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender (action E)).mp hff
  exact ⟨A.subgroupOf (offenderGroup E),
    (hA.subgroupOf (action E) (hA.le_offenderSubgroup (action E))).isOffender _⟩

/-- The quotient comparison from the embedded offender component all the
way to the original two-core quotient, with every central kernel retained. -/
def offenderCentralQuotientEquiv (h : EarlierGeometry E)
    (hK : componentImage E ≤ offenderGroup E)
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)] [IsQuasisimple (componentImage E)]
    [Nontrivial (componentImage E)] :
    (offenderComponent E ⧸ center (offenderComponent E)) ≃*
      ((E.Kz ⧸ pCore 2 E.Kz) ⧸ center (E.Kz ⧸ pCore 2 E.Kz)) :=
  letI : IsQuasisimple (offenderComponent E) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hK).symm
  (IsQuasisimple.centralQuotientEquiv (subgroupOfEquivOfLe hK).toMonoidHom
    (subgroupOfEquivOfLe hK).surjective).trans (componentCentralQuotientEquiv E h).symm

/-- All negative comparisons on the literal original two-core quotient.
The normal subgroup, offender restriction and central-quotient maps are the
ones supplied by the actual reduced-module construction. -/
theorem centralQuotientRestrictions
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hff : IsFFModule (action E)) :
    CentralQuotientRestrictions
      ((E.Kz ⧸ pCore 2 E.Kz) ⧸ center (E.Kz ⧸ pCore 2 E.Kz)) := by
  let : IsQuasisimple (componentImage E) := (action_structure E h hf hne hstar hcent).2.2
  let : IsSimpleGroup (componentImage E ⧸ center (componentImage E)) := IsQuasisimple.simple
  let : Nontrivial (componentImage E) :=
    (QuotientGroup.mk'_surjective (center (componentImage E))).nontrivial
  obtain ⟨hK,⟨c⟩⟩ := source_classification E h hf hne hstar hcent hff
  let : IsQuasisimple (offenderComponent E) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hK).symm
  exact (centralQuotientRestrictions_of_source c (offenderGroup_sqtk E h) inferInstance
    (offenderAction_ff E hff)).of_mulEquiv (offenderCentralQuotientEquiv E h hK).symm

/-- On the chosen flag the Thompson reduction constructs the FF witness.
Only the original authorized earlier geometry and maximality remain explicit. -/
theorem ofFlag_centralQuotientRestrictions
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
    (hXR : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G)) :
    let Q := (ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz
    CentralQuotientRestrictions (Q ⧸ center Q) := by
  obtain ⟨_,_,_,_,_,hff,_⟩ := ofFlag_ff_reduction S f X z H h hne hstar
    hlinear h1132 hcent hline hXR
  exact centralQuotientRestrictions _ h (fixed_and_transitive D S _ hlinear h1132).1
    hne hstar hcent hff

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification
