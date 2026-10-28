module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.FFInput
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.SourceComparison
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CentralComparison
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Orientation

/-!
# Field-four FF recognition on the literal reselected central quotient

Apply complete B.5.1 to the original full-normalizer offender supplement,
compare its actual component order with Sp₄(4) and G₂(4), and transport the
surviving natural action through the original two-core quotient map. No
marking or natural-module premise is used in recognition. The preceding
source step must still supply the FF condition and T-invariance of the seed.

Source: Aschbacher--Smith 3.2.8, 11.0.2 and 11.4.1, printed pp.582,
759--760 and 776. Earlier 7.0.1 and 3.2.5 remain with
`qt-d-1222-normalized-nonff` and `qt-baumann-fsu`.
-/

set_option Elab.async false

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
open Chapter12.Section02 ChapterB.QuasisimpleSource LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L I U : Subgroup G}

/-- The component projection in a literal comparison is faithful when the
original two-core quotient acts faithfully. -/
private theorem comparison_injective (D : ChosenModule T I U)
    {H : Type*} [Group H] {ρ : Representation (ZMod 2) H D.space}
    {K : Subgroup H} (d : D.LiteralComparison ρ K)
    (hs : IsSimpleGroup (I ⧸ pCore 2 I)) : Function.Injective d.projection := by
  intro x y he
  apply D.quotientAction_injective hs
  exact (d.action x).symm.trans ((congrArg (fun k : K => ρ k) he).trans (d.action y))

/-- Transport the field-four row along the original component projection
and canonical central quotient, retaining the unchanged chosen space. -/
private theorem fieldFourAction_of_comparison (D : ChosenModule T I U)
    {H : Type*} [Group H] {ρ : Representation (ZMod 2) H D.space}
    {K : Subgroup H} (d : D.LiteralComparison ρ K)
    (hs : IsSimpleGroup (I ⧸ pCore 2 I))
    (hc : FieldFourOrder (Nat.card (I ⧸ pCore 2 I)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K) :
    FieldFourAction D.centralQuotientAction := by
  have hp := comparison_injective D d hs
  have he := Nat.card_congr (MulEquiv.ofBijective d.projection ⟨hp, d.surjective⟩).toEquiv
  obtain ⟨F, hF, hrow⟩ := fieldFourAction_of_sourceCase ρ (he ▸ hc) c.clause_one
  refine ⟨F, hF, ?_⟩
  rcases hrow with ⟨hcard, ⟨m⟩⟩ | ⟨hcard, ⟨m⟩⟩
  · exact Or.inl ⟨he.trans hcard, ⟨(d.quotientMarking c.sectionData hp).trans m⟩⟩
  · exact Or.inr ⟨he.trans hcard, ⟨(d.quotientMarking c.sectionData hp).trans m⟩⟩

/-- The complete earlier source classification recognizes the unchanged
chosen central quotient. All incompatible rows and multiplicities are removed. -/
theorem fieldFourAction_of_ff (D : ChosenModule T I U)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T I)
    (hs : IsSimpleGroup (I ⧸ pCore 2 I))
    (hc : FieldFourOrder (Nat.card (I ⧸ pCore 2 I)))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction)) :
    FieldFourAction D.centralQuotientAction := by
  obtain ⟨A, _, hle, ⟨c⟩⟩ := source_conclusion D h hff
  exact fieldFourAction_of_comparison D (D.normalizerOffenderComparison A hle) hs hc c

/-- Recognition produces the actual field-degree-two natural input once
its preceding FF and seed-invariance obligations are discharged. -/
theorem nonbinary_of_ff (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction)) :
    ∃ S : D.NonbinaryNaturalInput, S.field.degree = 2 := by
  obtain ⟨F, hF, hrow⟩ := fieldFourAction_of_ff D h.toHypothesis1221
    (orientation_simple ho) (orientation_order ho) hff
  have hnat : D.NaturalRankTwoAction F := by
    rcases hrow with ⟨_, hm⟩ | ⟨_, hm⟩
    · exact .sp4 hm
    · exact .g2 hm
  exact ⟨⟨h, hmany, hTU, hff, F, by omega,
    D.centralQuotientAction_injective (orientation_simple ho), hnat⟩, hF⟩

/-- The symplectic source orientation yields precisely its natural action. -/
theorem symplectic_of_ff (D : ChosenModule T I U)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (hmodel : Source.IsSp (I ⧸ pCore 2 I) 2 4)
    (hff : IsFFModule (normalizerRepresentation D.chosenAction)) :
    ∃ F : BinaryField, F.degree = 2 ∧ Nonempty (ActionEquiv
      D.centralQuotientAction (restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2))) := by
  obtain ⟨F, hF, hrow⟩ := fieldFourAction_of_ff D h (orientation_simple ho)
    (orientation_order ho) hff
  rcases hrow with ⟨_, hm⟩ | ⟨hc, _⟩
  · exact ⟨F, hF, hm⟩
  · obtain ⟨E, hE, hfin, hcard, ⟨e⟩⟩ := hmodel
    let := hE
    let := hfin
    rw [Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp, hcard] at hc
    norm_num at hc

/-- The G₂ source orientation yields precisely its natural action. -/
theorem g2_of_ff (D : ChosenModule T I U)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (hmodel : ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)
    (hff : IsFFModule (normalizerRepresentation D.chosenAction)) :
    ∃ F : BinaryField, F.degree = 2 ∧ Nonempty (ActionEquiv
      D.centralQuotientAction (restrictScalars (k := ZMod 2) (g2Natural F.Carrier))) := by
  obtain ⟨F, hF, hrow⟩ := fieldFourAction_of_ff D h (orientation_simple ho)
    (orientation_order ho) hff
  rcases hrow with ⟨hc, _⟩ | ⟨_, hm⟩
  · obtain ⟨E, hE, hfin, hcard, ⟨e⟩⟩ := hmodel
    let := hE
    let := hfin
    rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hcard] at hc
    norm_num at hc
  · exact ⟨F, hF, hm⟩

/-- Apply recognition to the literal choice I = K₀ ∨ L₂ without selecting
an already classified replacement. The earlier orbit step must supply
invariance and FF for this same D_I. -/
theorem exists_triangle_recognition {V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (K X : Subgroup G)
    (htriangle : FieldFourTriangle T L (f.Li 0) (f.Li 1) K X)
    (hKnormal : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) :
    ∃ K₀ : Subgroup G, K₀ ∈ Chapter1.L G T ∧ K₀ ≤ K ∧ K₀ ≠ K ∧ K₀ ≠ f.Li 0 ∧
      TriangleOrientation L (K₀ ⊔ f.Li 1) ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T (K₀ ⊔ f.Li 1) ∧
      ∃ (U : Subgroup G) (D_I : ChosenModule T (K₀ ⊔ f.Li 1) U),
        ((T : Subgroup G) ≤ normalizer (U : Set G)) →
        IsFFModule (normalizerRepresentation D_I.chosenAction) →
        ∃ S_I : D_I.NonbinaryNaturalInput, S_I.field.degree = 2 := by
  obtain ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, ⟨D_I⟩⟩ :=
    exists_triangle_choice D S f K X htriangle hKnormal
  exact ⟨K₀, hK, hle, hne, hne₁, ho, hI, U, D_I,
    fun hTU hff => nonbinary_of_ff D_I hI ho S.many hTU hff⟩

/-- The input and its symplectic marking use the very same degree-two field. -/
theorem symplectic_input_of_ff (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (hmodel : Source.IsSp (I ⧸ pCore 2 I) 2 4)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction)) :
    ∃ S : D.NonbinaryNaturalInput, S.field.degree = 2 ∧ Nonempty
      (ActionEquiv D.centralQuotientAction (binarySymplectic S.field)) := by
  obtain ⟨F, hF, hm⟩ := symplectic_of_ff D h.toHypothesis1221 ho hmodel hff
  exact ⟨⟨h, hmany, hTU, hff, F, by omega,
    D.centralQuotientAction_injective (orientation_simple ho), .sp4 hm⟩, hF, hm⟩

/-- The input and its G₂ marking use the very same degree-two field. -/
theorem g2_input_of_ff (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (hmodel : ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction)) :
    ∃ S : D.NonbinaryNaturalInput, S.field.degree = 2 ∧ Nonempty
      (ActionEquiv D.centralQuotientAction (binaryG2 S.field)) := by
  obtain ⟨F, hF, hm⟩ := g2_of_ff D h.toHypothesis1221 ho hmodel hff
  exact ⟨⟨h, hmany, hTU, hff, F, by omega,
    D.centralQuotientAction_injective (orientation_simple ho), .g2 hm⟩, hF, hm⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
