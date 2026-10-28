module
public import Theory.GroupTheory.Amalgam.SylowRigidity
public import Theory.GroupTheory.Amalgam.ParabolicRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceBasic
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity.G2
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity.MathieuTwelve
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity.Tits

/-!
# Compatible recognition of the exceptional parabolic amalgams

The six rigid exceptional alternatives use the literal models from
`ExceptionalModels`: G₂(2)′, G₂(2), M₁₂, Aut(M₁₂), the Tits group and the
full binary Ree group. The three branch modules prove the overlap-automorphism
factorizations. This assembly upgrades independent isomorphisms of the three
groups to an isomorphism commuting with both overlap embeddings.

`isModel_of_injective_parabolicModel` requires injective maps and intrinsic
faithfulness, with no finite-model calculation left as a premise. Sylow orders
follow from the three group isomorphisms. The literal source application
`source_isModel_of_parabolicModel` further derives faithfulness from F.1.1(e):
a common normal overlap subgroup is a normal two-subgroup of the generated
group. No equality of the ambient group with that generated group is needed.
The earlier explicit-factorization interfaces are preserved below.

J₂ and Aut(J₂) retain exactly their parabolic-only conclusions. The corrected
Tits and outer M₁₂ models are used throughout. The genuine marked automorphism
identifications also give both commuting squares for the full extensions.

Source: Aschbacher--Smith F.1.1 and F.1.11--12, printed pp.259 and 262--264;
Goldschmidt, *Automorphisms of trivalent graphs*, Ann. Math. 111 (1980),
377--406; Fan, *Amalgams of prime index*, J. Algebra 98 (1986), 375--421.
The proofs are independent finite-model calculations. The original DGS/Fan/
Goldschmidt weaker hypotheses still require comparison with `ParabolicModel`;
this is not an assertion of that comparison or of exhaustive recognition.
See `ExceptionalRigidity/Source.md` for the precise remaining source boundary.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.ExceptionalRigidity
open Theory.GroupTheory RankTwoAmalgam
open ExceptionalModels

/-- The literal catalogue overlap embeds as a Sylow subgroup on both sides. -/
theorem g2Derived_sylow : SylowEmbedded 2 ExceptionalModels.G2.simpleAmalgam :=
  sylowEmbedded_ofSubgroups ExceptionalModels.G2.derivedS _ _ _ _ _ rfl

/-- The literal catalogue overlap embeds as a Sylow subgroup on both sides. -/
theorem g2Full_sylow : SylowEmbedded 2 ExceptionalModels.G2.fullAmalgam :=
  sylowEmbedded_ofSubgroups ExceptionalModels.G2.fullS _ _ _ _ _ rfl

/-- The literal catalogue overlap embeds as a Sylow subgroup on both sides. -/
theorem tits_sylow : SylowEmbedded 2 Tits.ExceptionalParabolics.amalgam :=
  sylowEmbedded_ofSubgroups Tits.atlas1600SylowTwo _ _ _ _ _
    (Tits.ExceptionalParabolics.overlap_eq_sylow.trans Tits.atlas1600SylowTwo_coe.symm)

/-- The literal catalogue overlap embeds as a Sylow subgroup on both sides. -/
theorem reeFull_sylow : SylowEmbedded 2 Tits.ExceptionalParabolics.FullRee.amalgam :=
  sylowEmbedded_ofSubgroups Tits.ExceptionalParabolics.FullRee.sylow _ _ _ _ _
    (Tits.ExceptionalParabolics.FullRee.borel_eq_sylow.trans
      Tits.ExceptionalParabolics.FullRee.sylow_coe.symm)

/-- The literal catalogue overlap embeds as a Sylow subgroup on both sides. -/
theorem m12_sylow : SylowEmbedded 2 MathieuTwelve.amalgam :=
  sylowEmbedded_ofSubgroups MathieuTwelve.S _ _ _ _ _ MathieuTwelve.B_eq_S

/-- The literal catalogue overlap embeds as a Sylow subgroup on both sides. -/
theorem autM12_sylow : SylowEmbedded 2 AutMathieuTwelve.autAmalgam := by
  apply sylowEmbedded_ofSubgroups AutMathieuTwelve.autS
  exact congrArg (Subgroup.map AutMathieuTwelve.ambientEquiv.toMonoidHom)
    AutMathieuTwelve.B_eq_S

/-- The local source completion supplies intrinsic amalgam faithfulness.
This uses the actual relative normal images and generating endpoints; it does
not certify the separate comparison with the original DGS Hypothesis A. -/
theorem source_faithful {G : Type*} [Group G]
    (P : Fin 2 → Subgroup G) (D : Subgroup G)
    (h : Source.LocallyRankOneTriple P D) (h₁ : D ≤ P 0) (h₂ : D ≤ P 1) :
    Faithful (ofSubgroups (P 0) D (P 1) h₁ h₂) :=
  faithful_ofSubgroups_of_completion (P 0) D (P 1) h₁ h₂ h.generate h.faithful

variable {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R}

/-- Model-specific overlap factorization upgrades raw parabolic equivalence.
The explicit premise is retained for compatibility; the branch calculation
now discharges it in `isModel_of_parabolicModel`. -/
theorem g2Derived_of_twist_factorization
    (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (he : ExceptionalModels.ParabolicModel .g2Derived α)
    (hfactor : ∀ d : MulAut ExceptionalModels.G2.derivedB,
      Faithful (twistRight ExceptionalModels.G2.simpleAmalgam d) → FactorsThrough ExceptionalModels.G2.simpleAmalgam d) :
    ExceptionalModels.IsModel .g2Derived α := by
  obtain ⟨e⟩ := he
  exact iso_of_faithful_twist_factorization hα g2Derived_sylow hf e hfactor

/-- Model-specific overlap factorization upgrades raw parabolic equivalence.
The explicit premise is retained for compatibility; the branch calculation
now discharges it in `isModel_of_parabolicModel`. -/
theorem g2Full_of_twist_factorization
    (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (he : ExceptionalModels.ParabolicModel .g2Full α)
    (hfactor : ∀ d : MulAut ExceptionalModels.G2.fullB,
      Faithful (twistRight ExceptionalModels.G2.fullAmalgam d) → FactorsThrough ExceptionalModels.G2.fullAmalgam d) :
    ExceptionalModels.IsModel .g2Full α := by
  obtain ⟨e⟩ := he
  exact iso_of_faithful_twist_factorization hα g2Full_sylow hf e hfactor

/-- Model-specific overlap factorization upgrades raw parabolic equivalence.
The explicit premise is retained for compatibility; the branch calculation
now discharges it in `isModel_of_parabolicModel`. -/
theorem tits_of_twist_factorization
    (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (he : ExceptionalModels.ParabolicModel .tits α)
    (hfactor : ∀ d : MulAut Tits.ExceptionalParabolics.overlap,
      Faithful (twistRight Tits.ExceptionalParabolics.amalgam d) →
        FactorsThrough Tits.ExceptionalParabolics.amalgam d) :
    ExceptionalModels.IsModel .tits α := by
  obtain ⟨e⟩ := he
  exact iso_of_faithful_twist_factorization hα tits_sylow hf e hfactor

/-- Model-specific overlap factorization upgrades raw parabolic equivalence.
The explicit premise is retained for compatibility; the branch calculation
now discharges it in `isModel_of_parabolicModel`. -/
theorem reeFull_of_twist_factorization
    (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (he : ExceptionalModels.ParabolicModel .reeFull α)
    (hfactor : ∀ d : MulAut Tits.ExceptionalParabolics.FullRee.B,
      Faithful (twistRight Tits.ExceptionalParabolics.FullRee.amalgam d) →
        FactorsThrough Tits.ExceptionalParabolics.FullRee.amalgam d) :
    ExceptionalModels.IsModel .reeFull α := by
  obtain ⟨e⟩ := he
  exact iso_of_faithful_twist_factorization hα reeFull_sylow hf e hfactor

/-- Model-specific overlap factorization upgrades raw parabolic equivalence.
The explicit premise is retained for compatibility; the branch calculation
now discharges it in `isModel_of_parabolicModel`. -/
theorem m12_of_twist_factorization
    (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (he : ExceptionalModels.ParabolicModel .m12 α)
    (hfactor : ∀ d : MulAut MathieuTwelve.B,
      Faithful (twistRight MathieuTwelve.amalgam d) → FactorsThrough MathieuTwelve.amalgam d) :
    ExceptionalModels.IsModel .m12 α := by
  obtain ⟨e⟩ := he
  exact iso_of_faithful_twist_factorization hα m12_sylow hf e hfactor

/-- Model-specific overlap factorization upgrades raw parabolic equivalence.
The explicit premise is retained for compatibility; the branch calculation
now discharges it in `isModel_of_parabolicModel`. -/
theorem autM12_of_twist_factorization
    (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (he : ExceptionalModels.ParabolicModel .autM12 α)
    (hfactor : ∀ d : MulAut AutMathieuTwelve.autB,
      Faithful (twistRight AutMathieuTwelve.autAmalgam d) →
        FactorsThrough AutMathieuTwelve.autAmalgam d) :
    ExceptionalModels.IsModel .autM12 α := by
  obtain ⟨e⟩ := he
  exact iso_of_faithful_twist_factorization hα autM12_sylow hf e hfactor


/-- All six proved rigidity branches, with Hall--Janko left at parabolic equivalence.
Every model-specific factorization premise is discharged. -/
theorem isModel_of_parabolicModel (hα : SylowEmbedded 2 α) (hf : Faithful α)
    {c : Case} (he : ParabolicModel c α) : IsModel c α := by
  cases c with
  | g2Derived =>
    exact g2Derived_of_twist_factorization hα hf he G2.simple_faithful_twist_factorization
  | g2Full =>
    exact g2Full_of_twist_factorization hα hf he G2.full_faithful_twist_factorization
  | tits => exact tits_of_twist_factorization hα hf he tits_faithful_twist_factorization
  | reeFull => exact reeFull_of_twist_factorization hα hf he reeFull_faithful_twist_factorization
  | m12 => exact m12_of_twist_factorization hα hf he MathieuTwistRigidity.m12_factorsThrough
  | autM12 =>
    exact autM12_of_twist_factorization hα hf he
      (fun d _ => MathieuTwistRigidity.autM12_factorsThrough d)
  | j2 | autJ2 => exact he

/-- In the six rigid cases, the independent group isomorphisms determine the
Sylow orders. Injectivity suffices; initial embedding compatibility is unnecessary. -/
theorem sylow_of_parabolicModel (hl : Function.Injective α.left)
    (hr : Function.Injective α.right) {c : Case}
    (hj : c ≠ .j2) (ha : c ≠ .autJ2) (he : ParabolicModel c α) :
    SylowEmbedded 2 α := by
  cases c with
  | j2 => exact (hj rfl).elim
  | autJ2 => exact (ha rfl).elim
  | g2Derived => obtain ⟨e⟩ := he; exact g2Derived_sylow.of_parabolicEquiv e hl hr
  | g2Full => obtain ⟨e⟩ := he; exact g2Full_sylow.of_parabolicEquiv e hl hr
  | tits => obtain ⟨e⟩ := he; exact tits_sylow.of_parabolicEquiv e hl hr
  | reeFull => obtain ⟨e⟩ := he; exact reeFull_sylow.of_parabolicEquiv e hl hr
  | m12 => obtain ⟨e⟩ := he; exact m12_sylow.of_parabolicEquiv e hl hr
  | autM12 => obtain ⟨e⟩ := he; exact autM12_sylow.of_parabolicEquiv e hl hr

/-- Faithful embedded input amalgams satisfy the precise catalogue conclusion.
The input identifies three groups, and the six rigid outputs commute with both maps. -/
theorem isModel_of_injective_parabolicModel (hl : Function.Injective α.left)
    (hr : Function.Injective α.right) (hf : Faithful α)
    {c : Case} (he : ParabolicModel c α) : IsModel c α := by
  by_cases hj : c = .j2
  · subst c; exact he
  by_cases ha : c = .autJ2
  · subst c; exact he
  exact isModel_of_parabolicModel (sylow_of_parabolicModel hl hr hj ha he) hf he

/-- For a subgroup amalgam, trivial two-core of the generated group discharges
faithfulness in every rigid case. No ambient finiteness or generation is assumed. -/
theorem isModel_of_subgroup_parabolicModel {G : Type*} [Group G]
    (P₁ D P₂ : Subgroup G) (h₁ : D ≤ P₁) (h₂ : D ≤ P₂)
    (hcore : pCore 2 (P₁ ⊔ P₂ : Subgroup G) = ⊥)
    {c : Case} (he : ParabolicModel c (ofSubgroups P₁ D P₂ h₁ h₂)) :
    IsModel c (ofSubgroups P₁ D P₂ h₁ h₂) := by
  by_cases hj : c = .j2
  · subst c; exact he
  by_cases ha : c = .autJ2
  · subst c; exact he
  have hs := sylow_of_parabolicModel
    (ofSubgroups_left_injective P₁ D P₂ h₁ h₂)
    (ofSubgroups_right_injective P₁ D P₂ h₁ h₂) hj ha he
  exact isModel_of_parabolicModel hs
    (faithful_ofSubgroups_of_pCore_eq_bot P₁ D P₂ h₁ h₂ hs.isPGroup hcore) he

variable {G : Type*} [Group G]

/-- The literal source triple `(L₁B, B, L₂B)`, with its two inclusion maps. -/
def sourceAmalgam (L : Fin 2 → Subgroup G) (S : Subgroup G) :
    RankTwoAmalgam (L 0 ⊔ Source.commonBorel L S : Subgroup G)
      (Source.commonBorel L S) (L 1 ⊔ Source.commonBorel L S : Subgroup G) :=
  ofSubgroups _ _ _ le_sup_right le_sup_right

/-- F.1.1 and raw parabolic equivalence give the exceptional catalogue conclusion.
F.1.1(e) supplies faithfulness; there are no extra Sylow or rigidity premises.
The derivation of this raw equivalence from DGS's exact weaker alternatives is
separate and is not claimed by this theorem. -/
theorem source_isModel_of_parabolicModel {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : Source.HypothesisF11 L S) {c : Case}
    (he : ParabolicModel c (sourceAmalgam L S)) :
    IsModel c (sourceAmalgam L S) := by
  apply isModel_of_subgroup_parabolicModel _ _ _ _ _ _ he
  rw [← Source.parabolic_eq_sup_commonBorel L S 0,
    ← Source.parabolic_eq_sup_commonBorel L S 1, Source.parabolics_generate]
  exact h.twoCore_free

/-- The generating-completion formulation supplies the same recognition result.
The actual kernel condition supplies relative amalgam faithfulness. -/
theorem sourceTriple_isModel_of_parabolicModel
    (P : Fin 2 → Subgroup G) (D : Subgroup G)
    (h : Source.LocallyRankOneTriple P D) (h₁ : D ≤ P 0) (h₂ : D ≤ P 1)
    {c : Case} (he : ParabolicModel c (ofSubgroups (P 0) D (P 1) h₁ h₂)) :
    IsModel c (ofSubgroups (P 0) D (P 1) h₁ h₂) :=
  isModel_of_injective_parabolicModel (ofSubgroups_left_injective _ _ _ _ _)
    (ofSubgroups_right_injective _ _ _ _ _) (source_faithful P D h h₁ h₂) he
/-- The source triple is recognized inside literal Aut(G₂(2)′), with both squares. -/
theorem source_g2Automorphism_of_parabolicEquiv
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : Source.HypothesisF11 L S)
    (he : ParabolicEquiv (sourceAmalgam L S) ExceptionalModels.G2.automorphismAmalgam) :
    Nonempty (Iso (sourceAmalgam L S) ExceptionalModels.G2.automorphismAmalgam) := by
  obtain ⟨e⟩ := source_isModel_of_parabolicModel h (c := .g2Full)
    ⟨he.trans ExceptionalModels.G2.automorphismAmalgamIso.symm.toParabolicEquiv⟩
  exact ⟨e.trans ExceptionalModels.G2.automorphismAmalgamIso⟩

/-- The source triple is recognized inside literal Aut(Tits), with both squares. -/
theorem source_titsAutomorphism_of_parabolicEquiv
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : Source.HypothesisF11 L S)
    (he : ParabolicEquiv (sourceAmalgam L S)
      Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgam) :
    Nonempty (Iso (sourceAmalgam L S)
      Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgam) := by
  obtain ⟨e⟩ := source_isModel_of_parabolicModel h (c := .reeFull)
    ⟨he.trans Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgamIso.symm.toParabolicEquiv⟩
  exact ⟨e.trans Tits.ExceptionalParabolics.FullRee.AutomorphismModel.amalgamIso⟩

end CFSG.Quasithin.ChapterF.GreenBook.ExceptionalRigidity
