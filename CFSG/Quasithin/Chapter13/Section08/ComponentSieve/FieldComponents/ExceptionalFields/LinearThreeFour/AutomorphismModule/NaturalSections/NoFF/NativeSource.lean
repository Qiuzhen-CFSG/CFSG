module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeActor
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved.Cubic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF.Recognition
public import Theory.SpecificGroups.PSL3Even.GraphRemarking

/-!
# Native no-FF and saturation for an SL₃(4) graph extension

The proved B.5.1 source classifier gives one or two identically marked natural
copies on the component-moved central section of any faithful FF module.
The graph automorphism exchanges natural and dual types, contradicting those
coordinates. This excludes FF modules for the whole graph extension, with the
scalar center retained.

A fixed-free central cubic remains fixed-free on invariant subspaces and
quotients. Quasisimplicity and the cubic centralizer then make both noncentral
sections faithful. If a nonzero fully moved submodule were proper in the
component moved space, the two no-FF inequalities would contradict the original
ratio-two bound. The original-source application is SpecialLinearFourModule:
its covered seed supplies the fixed-free scalar and its actual quadratic actor
supplies the bound. No natural constituent or whole-space saturation is assumed.

Source: Aschbacher–Smith, B.5.1, F.9.18(7), and13.8.20, printed
pp.99–103,326,955. The B.5.1 adapter preserves all carriers and action maps.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.SL3FourNaturalDual
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF.Native
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

private def field (E : ChapterB.QuasisimpleSource.BinaryField) : FFAlternatives.BinaryField where
  Carrier := E.Carrier
  degree := E.degree
  degree_pos := E.degree_pos
  card_eq := E.card_eq

private def four : ChapterB.QuasisimpleSource.BinaryField where
  Carrier := F
  degree := 2
  degree_pos := by decide
  card_eq := by rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]; decide

variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) D U) {K : Subgroup D}

private def sectionData (s : ChapterB.QuasisimpleSource.MovedSection ρ K) : FFAlternatives.MovedSection ρ K where
  space := s.space
  space_eq := s.space_eq
  central := s.central
  central_eq := s.central_eq

private def single (E : ChapterB.QuasisimpleSource.BinaryField)
    (e : ChapterB.QuasisimpleSource.ActionEquiv ρ (ChapterB.QuasisimpleSource.linearNatural E 3)) :
    FFAlternatives.ActionEquiv ρ (FFAlternatives.linearNatural (field E) 3) where
  groupEquiv := e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines := e.intertwines

private def repeated (E : ChapterB.QuasisimpleSource.BinaryField) (r : ℕ)
    (e : ChapterB.QuasisimpleSource.ActionEquiv ρ (ChapterB.QuasisimpleSource.repeated (ChapterB.QuasisimpleSource.linearNatural E 3) r)) :
    FFAlternatives.ActionEquiv ρ (FFAlternatives.repeated (FFAlternatives.linearNatural (field E) 3) r) where
  groupEquiv := e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines := e.intertwines

/-- Native B.5.1 on the literal moved central section gives one or two natural copies. -/
theorem repeatedSection (eK : K ≃* SL) (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K) :
    ∃ s : RepeatedNaturalSection ρ K, s.copies = 1 ∨ s.copies = 2 := by
  cases h.clause_one with
  | irreducible _ _ _ hc _ =>
    obtain ⟨E,⟨e⟩⟩ := ChapterB.QuasisimpleSource.SourceCompletion.linearThree_natural_of_irreducible_source
      h.sectionData.action hc four (by decide) eK
    let a := single _ E e
    have hE := Recognition.linearThree_card (field E) (eK.symm.trans a.groupEquiv)
    exact ⟨Recognition.quotientRepeatedSection (sectionData ρ h.sectionData) 1 (by decide)
      (Recognition.concreteSingleEquiv (field E) hE a),Or.inl rfl⟩
  | doubleThree E _ e _ _ =>
    let a := repeated _ E 2 e
    have hE := Recognition.linearThree_card (field E) (eK.symm.trans a.groupEquiv)
    exact ⟨Recognition.spaceRepeatedSection (sectionData ρ h.sectionData) 2 (by decide)
      (Recognition.concreteRepeatedEquiv (field E) hE 2 a),Or.inr rfl⟩
  | naturalDual d hd _ he =>
    obtain ⟨e⟩ := he
    exact (Recognition.not_binaryLinear d hd (eK.symm.trans e.groupEquiv)).elim
  | repeatedNatural d r hd _ _ _ he =>
    obtain ⟨e⟩ := he
    exact (Recognition.not_binaryLinear d hd (eK.symm.trans e.groupEquiv)).elim

variable [Module.Finite (ZMod 2) U] [K.Normal] [Theory.GroupTheory.IsQuasisimple K]
/-- A faithful action containing the specified graph automorphism is not FF. -/
theorem not_ff (hsq : IsSQTK KnownSimple.IsKnownSimple K)
    (eK : K ≃* SL) (hquot : IsPGroup 2 (D ⧸ K)) (hcore : pCore 2 D = ⊥)
    (hf : Function.Injective ρ) (t : D) (c : Matrix.GeneralLinearGroup (Fin 3) F)
    (ht : ∀ g, (eK.symm g : D) * t = t * (eK.symm
      (Matrix.PSL3.OuterSolvable.linearConjSL F c
        (Matrix.SpecialLinearGroup.inverseTranspose g)) : D)) : ¬ IsFFModule ρ := by
  intro hff
  obtain ⟨hKJ,⟨h⟩⟩ := ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    ρ K hquot hcore hsq hf hff
  obtain ⟨s,_⟩ := repeatedSection (ρ.comp (offenderSubgroup ρ).subtype)
    ((subgroupOfEquivOfLe hKJ).trans eK) h
  let a := Recognition.ambientRepeatedNaturalSection ρ hKJ s
  exact a.false_of_remarking Matrix.PSL3Even.GraphRemarking.linear_graph_remarking eK t c ht


omit [Finite D] in
private theorem quotient_fixedFree (S : Subrepresentation ρ) (x : D)
    (hx : ∀ v, ρ x v = v → v = 0) :
    ∀ v, S.quotientRepresentation x v = v → v = 0 := by
  have hi : Function.Injective (fun v : U => ρ x v - v) :=
    (injective_iff_map_eq_zero (ρ x - LinearMap.id)).mpr
      (fun v hv => hx v (sub_eq_zero.mp hv))
  let f : S.toSubmodule →ₗ[ZMod 2] S.toSubmodule := S.toRepresentation x - LinearMap.id
  have hfi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact hi (congrArg Subtype.val hab)
  have hfs := (LinearMap.injective_iff_surjective).mp hfi
  intro v hv
  obtain ⟨u,rfl⟩ := S.toSubmodule.mkQ_surjective v
  have hu : ρ x u - u ∈ S.toSubmodule := (Submodule.Quotient.eq S.toSubmodule).mp hv
  obtain ⟨w,hw⟩ := hfs ⟨ρ x u-u,hu⟩
  have hwu : (w : U) = u := hi (congrArg Subtype.val hw)
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hwu ▸ w.property)

open Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved

/-- The ratio-two bound saturates any nonzero invariant component-moved submodule. -/
theorem moved_space (hsq : IsSQTK KnownSimple.IsKnownSimple K)
    (eK : K ≃* SL) (hquot : IsPGroup 2 (D ⧸ K)) (hcore : pCore 2 D = ⊥)
    (t : D) (c : Matrix.GeneralLinearGroup (Fin 3) F)
    (ht : ∀ g, (eK.symm g : D) * t = t * (eK.symm
      (Matrix.PSL3.OuterSolvable.linearConjSL F c
        (Matrix.SpecialLinearGroup.inverseTranspose g)) : D))
    (x : D) (hx : x ∈ (center K).map K.subtype)
    (hfree : ∀ v, ρ x v = v → v = 0)
    (S : Subrepresentation ρ) (hS : S.toSubmodule ≠ ⊥)
    (hfull : subspaceCommutator ρ S.toSubmodule K = S.toSubmodule)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    S.toSubmodule = subspaceCommutator ρ ⊤ K := by
  let Z := (center K).map K.subtype
  have hfit : generalizedFitting D = K :=
    generalizedFitting_eq_of_quasisimple_two_quotient K hquot hcore
  have hCZ : centralizer (K : Set D) ≤ Z := by
    have hCK : centralizer (K : Set D) ≤ K :=
      hfit ▸ ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
    intro z hz
    refine ⟨⟨z,hCK hz⟩,?_,rfl⟩
    exact mem_center_iff.mpr (fun k => Subtype.ext (hz k k.property))
  have hZ : Nat.card Z = 3 := by
    rw [Nat.card_congr (equivMapOfInjective (center K) K.subtype K.subtype_injective).symm.toEquiv,
      Nat.card_congr (centerCongr eK).toEquiv,Atlas.ExceptionalSupport.card_sl_center,
      Fintype.card_fin, Nat.card_eq_fintype_card,SL2FourNatural.card_field]
    decide
  have hfS : ∀ v, S.toRepresentation x v = v → v = 0 := by
    intro v hv
    exact Subtype.ext (hfree v (congrArg Subtype.val hv))
  have hfaithS := faithful_of_cubic K Z hZ (inf_le_left.trans hCZ) S.toRepresentation
    (subrepresentation_action_nontrivial ρ S K hS hfull) x hx hfS
  have hnoS := not_ff S.toRepresentation hsq eK hquot hcore hfaithS t c ht
  by_contra hne
  have hfaithQ := faithful_of_cubic K Z hZ (inf_le_left.trans hCZ) S.quotientRepresentation
    (quotient_action_nontrivial ρ S K hfull hne) x hx (quotient_fixedFree ρ S x hfree)
  have hnoQ := not_ff S.quotientRepresentation hsq eK hquot hcore hfaithQ t c ht
  have hlowS : rank A < fixedCodim S.toRepresentation A :=
    Nat.lt_of_not_ge (fun h => hnoS ⟨A,hA,h⟩)
  have hlowQ : rank A < fixedCodim S.quotientRepresentation A :=
    Nat.lt_of_not_ge (fun h => hnoQ ⟨A,hA,h⟩)
  have hadd := fixedCodim_quotient_add_subrepresentation_le ρ S A
  omega
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NoFF.Native
