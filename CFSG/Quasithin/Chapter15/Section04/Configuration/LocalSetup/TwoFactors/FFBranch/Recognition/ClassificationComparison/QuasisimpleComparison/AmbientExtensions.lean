module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Targets
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.Rows
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.RankOneModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions.DegreeThreeModels

/-!
# Ambient two-group extensions of the small FF actors

`AmbientExtensions.fitting_eq_componentImage` and
`AmbientExtensions.residual_eq_componentImage` identify the ambient component
and residual with the literal image of F*(N), using B.5.1(1), D/N a two-group,
and O₂(D) = 1. The compatible component and offender equivalences retain
the original subgroup inclusions and representation.

`AmbientExtensions.comparison_reduction` eliminates rows (2)–(5), (12),(13)
of F.6.18, proves the A₇/S₇ conclusions in rows (7),(9), and retains the
genuine triple-six covers in rows (6),(8). The remaining classical rank-one
rows (6),(8) and degree-three rows (10),(11) are recognized here. Their model
comparisons construct the actual field and graph extension equivalences.
`AmbientExtensions.comparison` assembles these results in both generator
orientations and proves the small ambient catalogue, conditional on the
supplied small offender model. The parent comparison must discharge that
actor premise; no equality between the actor and its overgroup is assumed.

`AmbientExtensions.comparison_marked` retains each constructed equivalence
together with the original offender, quotient, derived-subgroup, centralizer
and representation markings. Both cubic covers remain on the original D,
with their covering maps intact. `modelComponentEquiv` also carries F*(N)
to the component of any such model, commuting with the literal inclusions.

Source: Aschbacher–Smith, B.5.1/B.5.6, pp.99–110; F.6.18, pp.309–310;
K.1.3, p.453; 15.4.18, p.1163 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace QuasisimpleComparison.AmbientExtensions
open GoldschmidtAlternatives
universe u v w
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D} {K : GroupClass.{u}}

/-- Exhaustive ambient comparison, conditional only on the stated bounded
branch and small model of the actual offender subgroup. -/
theorem comparison (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) : SmallAmbientModel D := by
  rcases comparison_reduction h s with hs | hr | hr
  · exact hs
  · exact rankOne_model_either_orientation h b s hr
  · rcases hr with hr | hr
    · exact degreeThree_model h b s hr
    · let h' : ProjectiveLine.ClassifiedAction K ρ G₂ G₁ :=
        ⟨h.faithful, h.twoCore, h.threePrimeCore, h.triple.symm, h.goldschmidt.symm,
          h.ffHypothesis, h.ffWitness, h.ffAlternatives, h.quotient_twoGroup,
          h.sylow_fixedSpace⟩
      exact degreeThree_model h' b s hr

/-- Component transport under any of the constructed ambient equivalences. -/
noncomputable def modelComponentEquiv
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    {M : Type w} [Group M] (e : D ≃* M) :
    generalizedFitting (offenderSubgroup ρ) ≃* generalizedFitting M :=
  (componentEquiv h b).trans ((e.subgroupMap (generalizedFitting D)).trans
    (MulEquiv.subgroupCongr (map_generalizedFitting_equiv e)))

/-- The component map agrees pointwise with N ≤ D followed by the model map. -/
theorem modelComponentEquiv_coe
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    {M : Type w} [Group M] (e : D ≃* M)
    (x : generalizedFitting (offenderSubgroup ρ)) :
    (modelComponentEquiv h b e x : M) = e ((x : offenderSubgroup ρ) : D) := by rfl

/-- The subgroup and action markings together with a compatible component map. -/
structure ModelMarking {M : Type w} [Group M] (ρ : Representation (ZMod 2) D V)
    (e : D ≃* M) : Prop extends RankOneMarking ρ e where
  component : ∃ c : generalizedFitting (offenderSubgroup ρ) ≃* generalizedFitting M,
    ∀ x, (c x : M) = e ((x : offenderSubgroup ρ) : D)

/-- Construct all markings on the same ambient equivalence. -/
theorem modelMarking (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    {M : Type w} [Group M] (e : D ≃* M) : ModelMarking ρ e :=
  ⟨rankOneMarking h b e, modelComponentEquiv h b e, modelComponentEquiv_coe h b e⟩

/-- The full ambient catalogue with the actual subgroup and action markings.
`RankOneMarking` applies to any ambient equivalence: its fields identify F*(N)
and O², and retain the offender restriction, quotient, derived subgroup and
centralizer. The covering alternatives already live on the original D. -/
inductive MarkedSmallAmbientModel (ρ : Representation (ZMod 2) D V) : Prop
  | linearThree (e : D ≃* SL(3,ZMod 2)) (marking : ModelMarking ρ e)
  | alternatingSix (e : D ≃* alternatingGroup (Fin 6)) (marking : ModelMarking ρ e)
  | symmetricSix (e : D ≃* Equiv.Perm (Fin 6)) (marking : ModelMarking ρ e)
  | alternatingSeven (e : D ≃* alternatingGroup (Fin 7)) (marking : ModelMarking ρ e)
  | symmetricSeven (e : D ≃* Equiv.Perm (Fin 7)) (marking : ModelMarking ρ e)
  | tripleSix (cover : TripleAlternating D 6) (marking : ModelMarking ρ (MulEquiv.refl D))
  | g2Derived (e : D ≃* commutator (Atlas.G2.Model (ZMod 2)))
      (marking : ModelMarking ρ e)
  | g2 (e : D ≃* Atlas.G2.Model (ZMod 2)) (marking : ModelMarking ρ e)
  | tripleSymmetricSix (cover : TripleSymmetric D 6)
      (marking : ModelMarking ρ (MulEquiv.refl D))

omit [Finite D] in
/-- Forget only the subgroup markings; keep every actual model and covering map. -/
theorem MarkedSmallAmbientModel.smallAmbientModel (m : MarkedSmallAmbientModel ρ) :
    SmallAmbientModel D := by
  cases m with
  | linearThree e _ => exact Or.inl (.linearThree e)
  | alternatingSix e _ => exact Or.inl (.alternatingSix e)
  | symmetricSix e _ => exact Or.inl (.symmetricSix e)
  | alternatingSeven e _ => exact Or.inl (.alternatingSeven e)
  | symmetricSeven e _ => exact Or.inl (.symmetricSeven e)
  | tripleSix c _ => exact Or.inl (.tripleSix c)
  | g2Derived e _ => exact Or.inl (.g2Derived e)
  | g2 e _ => exact Or.inl (.g2 e)
  | tripleSymmetricSix c _ => exact Or.inr c

/-- Apply the structural maps to the models constructed by the exhaustive
comparison. In each ordinary model the transported action restricts to
precisely rho on the original offender subgroup; the covers retain D itself. -/
theorem comparison_marked (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (s : SmallActorModel (offenderSubgroup ρ)) : MarkedSmallAmbientModel ρ := by
  rcases comparison h b s with m | c
  · cases m with
    | linearThree e => exact .linearThree e (modelMarking h b e)
    | alternatingSix e => exact .alternatingSix e (modelMarking h b e)
    | symmetricSix e => exact .symmetricSix e (modelMarking h b e)
    | alternatingSeven e => exact .alternatingSeven e (modelMarking h b e)
    | symmetricSeven e => exact .symmetricSeven e (modelMarking h b e)
    | tripleSix c => exact .tripleSix c (modelMarking h b (MulEquiv.refl D))
    | g2Derived e => exact .g2Derived e (modelMarking h b e)
    | g2 e => exact .g2 e (modelMarking h b e)
  · exact .tripleSymmetricSix c (modelMarking h b (MulEquiv.refl D))

end QuasisimpleComparison.AmbientExtensions
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
